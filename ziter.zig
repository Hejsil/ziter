const std = @import("std");

const debug = std.debug;
const math = std.math;
const mem = std.mem;
const testing = std.testing;

pub usingnamespace @import("src/span.zig");

comptime {
    testing.refAllDecls(@This());
}

/// Tests that an iterator returns all the items in the `expected`
/// slice, and no more.
pub fn test_it(_it: anytype, hint: LengthHint, expected: anytype) void {
    testing.expectEqual(hint, _it.len_hint());

    var it = _it;
    for (expected) |item|
        testing.expectEqual(item, it.next().?);
    testing.expect(it.next() == null);
}

fn ReturnType(comptime F: type) type {
    return @typeInfo(F).Fn.return_type.?;
}

fn ReturnTypeOpt(comptime F: type) type {
    return @typeInfo(ReturnType(F)).Optional.child;
}

/// Get the type of the items an iterator iterates over.
pub fn Result(comptime It: type) type {
    return ReturnTypeOpt(@TypeOf(It.next));
}

pub const LengthHint = struct {
    min: usize,
    max: ?usize,

    pub fn len(hint: LengthHint) ?usize {
        const max = hint.max orelse return null;
        return if (hint.min == max) max else null;
    }

    pub fn add(a: LengthHint, b: LengthHint) LengthHint {
        return .{
            .min = a.min + b.min,
            .max = blk: {
                const a_max = a.max orelse break :blk null;
                const b_max = b.max orelse break :blk null;
                break :blk a_max + b_max;
            },
        };
    }
};

/// You see, we don't have ufc and an iterator interface using free functions
/// is kinda painful and hard to read:
/// ```
/// const it = filter(deref(span("aaa")), fn(a:u8){ return a == 0: });
/// ```
/// This is an attempt at emulating ufc by having all iterators have one function called
/// `call`. With that function, you could build iterators like this:
/// ```
/// const it = span("aaa")
///     .call(deref, .{})
///     .call(filter, .{ fn(a: u8){ return a == 0; } });
/// ```
pub fn call_method(
    it: anytype,
    func: anytype,
    args: anytype,
) @TypeOf(@call(.{}, func, .{@TypeOf(it.*){}} ++ @as(@TypeOf(args), undefined))) {
    return @call(.{}, func, .{it.*} ++ args);
}

//////////////////////////////////////////////////////////
// The functions creates iterators from other iterators //
//////////////////////////////////////////////////////////

pub fn ChainIt(comptime First: type, comptime Second: type) type {
    return struct {
        first: First = First{},
        second: Second = Second{},

        pub fn next(it: *@This()) ?Result(First) {
            return it.first.next() orelse it.second.next();
        }

        pub fn len_hint(it: @This()) LengthHint {
            return LengthHint.add(
                it.first.len_hint(),
                it.second.len_hint(),
            );
        }

        pub const call = call_method;
    };
}

/// Creates an iterator that first iterates over all items in `first` after
/// which it iterates over all elements in `second`.
pub fn chain(first: anytype, second: anytype) ChainIt(@TypeOf(first), @TypeOf(second)) {
    return .{ .first = first, .second = second };
}

test "chain" {
    const abc = deref(span("abc"));
    const def = deref(span("def"));
    const non = deref(span(""));
    test_it(chain(abc, def), .{ .min = 6, .max = 6 }, "abcdef");
    test_it(chain(non, def), .{ .min = 3, .max = 3 }, "def");
    test_it(chain(abc, non), .{ .min = 3, .max = 3 }, "abc");
    test_it(chain(non, non), .{ .min = 0, .max = 0 }, "");
}

pub fn DerefIt(comptime Child: type) type {
    return MapIt(void, Child, @typeInfo(Result(Child)).Pointer.child);
}

/// Creates an iterator which derefs all of the items it iterates over.
pub fn deref(it: anytype) DerefIt(@TypeOf(it)) {
    const It = @TypeOf(it);
    return map(it, struct {
        fn transform(ptr: Result(It)) Result(DerefIt(It)) {
            return ptr.*;
        }
    }.transform);
}

test "deref" {
    test_it(span("abcd").call(deref, .{}), .{ .min = 4, .max = 4 }, "abcd");
}

pub fn EnumerateIt(comptime I: type, comptime Child: type) type {
    return struct {
        index: I = 0,
        child: Child = Child{},

        pub const Pair = struct {
            index: I,
            item: Result(Child),
        };

        pub fn next(it: *@This()) ?Pair {
            const item = it.child.next() orelse return null;
            const index = it.index;
            it.index += 1;
            return Pair{ .index = index, .item = item };
        }

        pub fn len_hint(it: @This()) LengthHint {
            return it.child.len_hint();
        }

        pub const call = call_method;
    };
}

/// Same as `enumerate_ex` but with `usize` passed as the second parameter.
pub fn enumerate(it: anytype) EnumerateIt(usize, @TypeOf(it)) {
    return enumerate_ex(it, usize);
}

/// Creates an iterator that gives the item index as well as the item.
pub fn enumerate_ex(it: anytype, comptime I: type) EnumerateIt(I, @TypeOf(it)) {
    return .{ .child = it };
}

test "enumerate" {
    var it = span("ab") //
        .call(deref, .{}) //
        .call(enumerate, .{});

    testing.expectEqual(LengthHint{ .min = 2, .max = 2 }, it.len_hint());

    var i: usize = 0;
    while (it.next()) |item| : (i += 1) {
        testing.expectEqual(@as(usize, i), item.index);
        testing.expectEqual(@as(u8, "ab"[i]), item.item);
    }
}

pub fn FilterMapIt(comptime Context: type, comptime Child: type, comptime T: type) type {
    return struct {
        child: Child = Child{},
        ctx: Context = undefined,
        transform: fn (Context, Result(Child)) ?T = undefined,

        pub fn next(it: *@This()) ?T {
            while (it.child.next()) |item| {
                if (it.transform(it.ctx, item)) |res|
                    return res;
            }
            return null;
        }

        pub fn len_hint(it: @This()) LengthHint {
            return .{ .min = 0, .max = it.child.len_hint().max };
        }

        pub const call = call_method;
    };
}

/// Same as `filter_map_ex` but requires no context.
pub fn filter_map(
    it: anytype,
    transform: anytype,
) FilterMapIt(void, @TypeOf(it), ReturnTypeOpt(@TypeOf(transform))) {
    const Expect = fn (Result(@TypeOf(it))) ReturnType(@TypeOf(transform));
    const Transform = fn (void, Result(@TypeOf(it))) ReturnType(@TypeOf(transform));
    return filter_map_ex(it, {}, @ptrCast(Transform, @as(Expect, transform)));
}

/// Creates an iterator that transforms and filters out items the `transform` function.
pub fn filter_map_ex(
    it: anytype,
    ctx: anytype,
    transform: anytype,
) FilterMapIt(@TypeOf(ctx), @TypeOf(it), ReturnTypeOpt(@TypeOf(transform))) {
    return .{ .child = it, .ctx = ctx, .transform = transform };
}

test "filter_map" {
    const F = struct {
        fn even_double(i: u8) ?u16 {
            if (i % 2 != 0)
                return null;
            return i * 2;
        }
    };
    const i = range(u8, 0, 10) //
        .call(filter_map, .{F.even_double});
    test_it(i, .{ .min = 0, .max = 10 }, &[_]u16{ 0, 4, 8, 12, 16 });
}

pub fn FilterIt(comptime Context: type, comptime Child: type) type {
    return struct {
        child: Child = Child{},
        ctx: Context = undefined,
        pred: fn (Context, Result(Child)) bool = undefined,

        pub fn next(it: *@This()) ?Result(Child) {
            while (it.child.next()) |item| {
                if (it.pred(it.ctx, item))
                    return item;
            }
            return null;
        }

        pub fn len_hint(it: @This()) LengthHint {
            return .{ .min = 0, .max = it.child.len_hint().max };
        }

        pub const call = call_method;
    };
}

/// Same as `filter_ex` but requires no context.
pub fn filter(
    it: anytype,
    pred: fn (Result(@TypeOf(it))) bool,
) FilterIt(void, @TypeOf(it)) {
    return filter_ex(it, {}, @ptrCast(fn (void, Result(@TypeOf(it))) bool, pred));
}

/// Creates an iterator that filters out items that does not match
/// the predicate `pred`.
pub fn filter_ex(
    it: anytype,
    ctx: anytype,
    pred: fn (@TypeOf(ctx), Result(@TypeOf(it))) bool,
) FilterIt(@TypeOf(ctx), @TypeOf(it)) {
    return .{ .child = it, .ctx = ctx, .pred = pred };
}

test "filter" {
    const s1 = span("a1b2").call(deref, .{});
    const s2 = span("aaabb").call(deref, .{});
    test_it(s1.call(filter, .{std.ascii.isDigit}), .{ .min = 0, .max = 4 }, "12");
    test_it(s1.call(filter, .{std.ascii.isAlpha}), .{ .min = 0, .max = 4 }, "ab");
    test_it(s2.call(filter, .{std.ascii.isDigit}), .{ .min = 0, .max = 5 }, "");
}

pub fn InterLeaveIt(comptime First: type, comptime Second: type) type {
    return struct {
        first: First = First{},
        second: Second = Second{},
        flag: enum { first, second } = .first,

        pub fn next(it: *@This()) ?Result(First) {
            defer it.flag = if (it.flag == .first) .second else .first;
            return switch (it.flag) {
                .first => it.first.next() orelse it.second.next(),
                .second => it.second.next() orelse it.first.next(),
            };
        }

        pub fn len_hint(it: @This()) LengthHint {
            return LengthHint.add(
                it.first.len_hint(),
                it.second.len_hint(),
            );
        }

        pub const call = call_method;
    };
}

/// Creates an iterator switches between calling `first.next` and `second.next`.
pub fn interleave(
    first: anytype,
    second: anytype,
) InterLeaveIt(@TypeOf(first), @TypeOf(second)) {
    return .{ .first = first, .second = second };
}

test "interleave" {
    const abc = deref(span("abc"));
    const def = deref(span("def"));
    const non = deref(span(""));
    test_it(interleave(abc, def), .{ .min = 6, .max = 6 }, "adbecf");
    test_it(interleave(non, def), .{ .min = 3, .max = 3 }, "def");
    test_it(interleave(abc, non), .{ .min = 3, .max = 3 }, "abc");
    test_it(interleave(non, non), .{ .min = 0, .max = 0 }, "");
}

pub fn MapIt(comptime Context: type, comptime Child: type, comptime T: type) type {
    return struct {
        child: Child = Child{},
        ctx: Context = undefined,
        transform: fn (Context, Result(Child)) T = undefined,

        pub fn next(it: *@This()) ?T {
            return it.transform(it.ctx, it.child.next() orelse return null);
        }

        pub fn len_hint(it: @This()) LengthHint {
            return it.child.len_hint();
        }

        pub const call = call_method;
    };
}

/// Same as `map_ex` but requires no context.
pub fn map(
    it: anytype,
    transform: anytype,
) MapIt(void, @TypeOf(it), ReturnType(@TypeOf(transform))) {
    const Expect = fn (Result(@TypeOf(it))) ReturnType(@TypeOf(transform));
    const Transform = fn (void, Result(@TypeOf(it))) ReturnType(@TypeOf(transform));
    return map_ex(it, {}, @ptrCast(Transform, @as(Expect, transform)));
}

/// Creates an iterator that transforms all items using the `transform` function.
pub fn map_ex(
    it: anytype,
    ctx: anytype,
    transform: anytype,
) MapIt(@TypeOf(ctx), @TypeOf(it), ReturnType(@TypeOf(transform))) {
    return .{ .child = it, .ctx = ctx, .transform = transform };
}

test "map" {
    const m1 = span("abcd") //
        .call(deref, .{}) //
        .call(map, .{std.ascii.toUpper});
    test_it(m1, .{ .min = 4, .max = 4 }, "ABCD");

    const m2 = span("") //
        .call(deref, .{}) //
        .call(map, .{std.ascii.toUpper});
    test_it(m2, .{ .min = 0, .max = 0 }, "");
}

pub fn PairIt(comptime Child: type) type {
    return struct {
        prev: ?Result(Child) = null,
        child: Child = Child{},

        pub fn next(it: *@This()) ?[2]Result(Child) {
            const p = it.prev orelse it.child.next() orelse return null;
            const n = it.child.next() orelse return null;
            defer it.prev = n;
            return [2]Result(Child){ p, n };
        }

        pub fn len_hint(it: @This()) LengthHint {
            const child = it.child.len_hint();
            return .{
                .min = math.sub(usize, child.min, 1) catch 0,
                .max = blk: {
                    const max = child.max orelse break :blk null;
                    break :blk math.sub(usize, max, 1) catch 0;
                },
            };
        }

        pub const call = call_method;
    };
}

/// Creates an iterator that iterates over the provided iterator and
/// returns prev+next pairs. If the provided iterator iterates N times
/// then the iterator created iterates N-1 times.
pub fn pair(it: anytype) PairIt(@TypeOf(it)) {
    return .{ .child = it };
}

test "pair" {
    var p = span("abcd") //
        .call(deref, .{}) //
        .call(pair, .{});
    testing.expectEqualSlices(u8, "ab", &p.next().?);
    testing.expectEqualSlices(u8, "bc", &p.next().?);
    testing.expectEqualSlices(u8, "cd", &p.next().?);
    testing.expect(p.next() == null);
}

pub fn Range(comptime T: type) type {
    return struct {
        start: T = 0,
        end: T = 0,
        step: T = 1,

        pub fn next(it: *@This()) ?T {
            if (it.end <= it.start)
                return null;

            defer it.start += it.step;
            return it.start;
        }

        pub fn len_hint(it: @This()) LengthHint {
            const diff = math.sub(T, it.end, it.start) catch 0;
            const len = diff / it.step + @boolToInt(diff % it.step != 0);
            return .{ .min = len, .max = len };
        }

        pub const call = call_method;
    };
}

/// Same as `range_ex` with 1 passed to the `step` paramter.
pub fn range(comptime T: type, start: T, end: T) Range(T) {
    return range_ex(T, start, end, 1);
}

/// Creates an iterator that iterates from `start` to `end` exclusively
/// with a step size of `step`.
pub fn range_ex(comptime T: type, start: T, end: T, step: T) Range(T) {
    debug.assert(start <= end and step != 0);
    return .{ .start = start, .end = end, .step = step };
}

test "range" {
    test_it(range(u8, 'a', 'd'), .{ .min = 3, .max = 3 }, "abc");
    test_it(range_ex(u8, 'a', 'd', 2), .{ .min = 2, .max = 2 }, "ac");
    test_it(range_ex(u8, 'a', 'd', 3), .{ .min = 1, .max = 1 }, "a");
}

pub fn RepeatIt(comptime Child: type) type {
    return struct {
        reset: Child = Child{},
        curr: Child = Child{},

        pub fn next(it: *@This()) ?Result(Child) {
            if (it.curr.next()) |res|
                return res;

            it.curr = it.reset;
            return it.curr.next();
        }

        pub fn len_hint(it: @This()) LengthHint {
            const child = it.reset.len_hint();
            const min = child.min;
            const max = child.max orelse std.math.maxInt(usize);
            return .{
                .min = min,
                .max = if (min == 0 and max == 0) 0 else null,
            };
        }

        pub const call = call_method;
    };
}

/// Creates an iterator that keeps repeating the items returned from the
/// child iterator, never returning `null` unless the child iterator returns
/// no items, in which case `repeat` always returns `null`.
pub fn repeat(_it: anytype) RepeatIt(@TypeOf(_it)) {
    return .{ .reset = _it, .curr = _it };
}

test "repeat" {
    var it = span("ab") //
        .call(deref, .{}) //
        .call(repeat, .{});

    testing.expectEqual(LengthHint{ .min = 2, .max = null }, it.len_hint());
    testing.expect(it.next().? == 'a');
    testing.expect(it.next().? == 'b');
    testing.expect(it.next().? == 'a');
    testing.expect(it.next().? == 'b');
    testing.expect(it.next().? == 'a');
    testing.expect(it.next().? == 'b');
}

/// Skips `n` iterations of `it` and return it.
pub fn skip(_it: anytype, _n: usize) @TypeOf(_it) {
    var n = _n;
    var it = _it;
    while (n != 0) : (n -= 1)
        _ = it.next();
    return it;
}

test "skip" {
    const i = span("abcd") //
        .call(deref, .{}) //
        .call(skip, .{2});
    test_it(i, .{ .min = 2, .max = 2 }, "cd");
}

pub fn TakeWhileIt(comptime Context: type, comptime Child: type) type {
    return struct {
        child: Child = Child{},
        ctx: Context = undefined,
        pred: fn (Context, Result(Child)) bool = undefined,

        pub fn next(it: *@This()) ?Result(Child) {
            const item = it.child.next() orelse return null;
            return if (it.pred(it.ctx, item)) item else null;
        }

        pub fn len_hint(it: @This()) LengthHint {
            return .{ .min = 0, .max = it.child.len_hint().max };
        }
    };
}

/// Same as `take_while` but requires no context.
pub fn take_while(
    it: anytype,
    pred: fn (Result(@TypeOf(it))) bool,
) TakeWhileIt(void, @TypeOf(it)) {
    const F = fn (void, Result(@TypeOf(it))) bool;
    return take_while_ex(it, {}, @ptrCast(F, pred));
}

/// Creates an iterator that takes values from the child iterator so long
/// as they matches the predicate `pred`. When the predicate is no longer
/// satisfied, the iterator will return null.
pub fn take_while_ex(
    it: anytype,
    ctx: anytype,
    pred: fn (@TypeOf(ctx), Result(@TypeOf(it))) bool,
) TakeWhileIt(@TypeOf(ctx), @TypeOf(it)) {
    return .{ .child = it, .ctx = ctx, .pred = pred };
}

test "take_while" {
    const tw = span("abCD") //
        .call(deref, .{}) //
        .call(take_while, .{std.ascii.isLower});
    test_it(tw, .{ .min = 0, .max = 4 }, "ab");
}

pub fn TakeIt(comptime Child: type) type {
    return struct {
        child: Child = Child{},
        n: usize,

        pub fn next(it: *@This()) ?Result(Child) {
            if (it.n == 0)
                return null;

            defer it.n -= 1;
            return it.child.next();
        }

        pub fn len_hint(it: @This()) LengthHint {
            return .{ .min = math.min(it.n, it.child.len_hint().min), .max = it.n };
        }
    };
}

/// Creates an iterator that takes at most `n` items from the child iterator.
pub fn take(it: anytype, n: usize) TakeIt(@TypeOf(it)) {
    return .{ .child = it, .n = n };
}

test "take" {
    const abCD = span("abCD").call(deref, .{});
    test_it(abCD.call(take, .{1}), .{ .min = 1, .max = 1 }, "a");
    test_it(abCD.call(take, .{2}), .{ .min = 2, .max = 2 }, "ab");
    test_it(abCD.call(take, .{3}), .{ .min = 3, .max = 3 }, "abC");
}

/////////////////////////////////////////////////////////////////
// The functions below iterates over iterators to get a result //
/////////////////////////////////////////////////////////////////

/// Same as `all_ex` but requires no context.
pub fn all(it: anytype, pred: fn (Result(@TypeOf(it))) bool) bool {
    const F = fn (void, Result(@TypeOf(it))) bool;
    return all_ex(it, {}, @ptrCast(F, pred));
}

/// Check that all items in an iterator matches a predicate.
pub fn all_ex(
    _it: anytype,
    ctx: anytype,
    pred: fn (@TypeOf(ctx), Result(@TypeOf(_it))) bool,
) bool {
    var it = _it;
    while (it.next()) |item| {
        if (!pred(ctx, item))
            return false;
    }

    return true;
}

test "all" {
    testing.expect(span("aaa").call(deref, .{}).call(all, .{std.ascii.isLower}));
    testing.expect(!span("Aaa").call(deref, .{}).call(all, .{std.ascii.isLower}));
}

/// Same as `any_ex` but requires no context.
pub fn any(it: anytype, pred: fn (Result(@TypeOf(it))) bool) bool {
    const F = fn (void, Result(@TypeOf(it))) bool;
    return any_ex(it, {}, @ptrCast(F, pred));
}

/// Check that any items in an iterator matches a predicate.
pub fn any_ex(
    it: anytype,
    ctx: anytype,
    pred: fn (@TypeOf(ctx), Result(@TypeOf(it))) bool,
) bool {
    return find_ex(it, ctx, pred) != null;
}

test "any" {
    testing.expect(span("aAA").call(deref, .{}).call(any, .{std.ascii.isLower}));
    testing.expect(!span("AAA").call(deref, .{}).call(any, .{std.ascii.isLower}));
}

pub fn collect(
    _it: anytype,
    allocator: *mem.Allocator,
) mem.Allocator.Error![]Result(@TypeOf(_it)) {
    var res = std.ArrayList(Result(@TypeOf(_it))).init(allocator);
    errdefer res.deinit();

    if (@hasDecl(@TypeOf(_it), "len_hint"))
        try res.ensureCapacity(_it.len_hint().min);

    var it = _it;
    while (it.next()) |item|
        try res.append(item);

    return res.items;
}

test "collect" {
    const collected = try span("abcd") //
        .call(deref, .{}) //
        .call(collect, .{testing.allocator});
    defer testing.allocator.free(collected);

    testing.expectEqualSlices(u8, "abcd", collected);

    const collected_range = try range(usize, 0, 5) //
        .call(collect, .{testing.allocator});
    defer testing.allocator.free(collected_range);

    testing.expectEqualSlices(usize, &[_]usize{ 0, 1, 2, 3, 4 }, collected_range);
}

/// Counts the number of iterations before an iterator returns `null`.
pub fn count(_it: anytype) usize {
    if (@hasDecl(@TypeOf(_it), "len_hint")) {
        if (_it.len_hint().len()) |len|
            return len;
    }

    var res: usize = 0;
    var it = _it;
    while (it.next()) |_|
        res += 1;

    return res;
}

test "count" {
    testing.expectEqual(@as(usize, 0), span("").call(count, .{}));
    testing.expectEqual(@as(usize, 1), span("a").call(count, .{}));
    testing.expectEqual(@as(usize, 2), span("aa").call(count, .{}));
}

/// Same as `find_ex` but requires no context.
pub fn find(it: anytype, pred: fn (Result(@TypeOf(it))) bool) ?Result(@TypeOf(it)) {
    const F = fn (void, Result(@TypeOf(it))) bool;
    return find_ex(it, {}, @ptrCast(F, pred));
}

/// Gets the first item in an iterator that satiesfies the predicate.
pub fn find_ex(
    _it: anytype,
    ctx: anytype,
    pred: fn (@TypeOf(ctx), Result(@TypeOf(_it))) bool,
) ?Result(@TypeOf(_it)) {
    var it = _it;
    while (it.next()) |item| {
        if (pred(ctx, item))
            return item;
    }

    return null;
}

test "find" {
    const aAA = span("aAA").call(deref, .{});
    const AAA = span("AAA").call(deref, .{});
    testing.expect(aAA.call(find, .{std.ascii.isLower}).? == 'a');
    testing.expect(AAA.call(find, .{std.ascii.isLower}) == null);
}

/// Same as `fold_ex` but requires no context.
pub fn fold(
    it: anytype,
    init: anytype,
    f: fn (@TypeOf(init), Result(@TypeOf(it))) @TypeOf(init),
) @TypeOf(init) {
    const F = fn (void, @TypeOf(init), Result(@TypeOf(it))) @TypeOf(init);
    return fold_ex(it, init, {}, @ptrCast(F, f));
}

/// Iterates over an iterator to get a single resulting value. This result is aquired
/// by starting with the value of `init` and calling the function `f` on all result +
/// item pairs, reassing the result to the return value of `f` on each iteration. Once
/// all items have been iterated over the result is returned.
pub fn fold_ex(
    _it: anytype,
    init: anytype,
    ctx: anytype,
    f: fn (@TypeOf(ctx), @TypeOf(init), Result(@TypeOf(_it))) @TypeOf(init),
) @TypeOf(init) {
    var res = init;
    var it = _it;
    while (it.next()) |item|
        res = f(ctx, res, item);

    return res;
}

test "fold" {
    const add = struct {
        fn add(a: u8, b: u8) u8 {
            return a + b;
        }
    }.add;

    const r1 = range_ex(u8, 2, 8, 2);
    const r2 = range(u8, 0, 0);
    testing.expectEqual(@as(u8, 12), r1.call(fold, .{ @as(u8, 0), add }));
    testing.expectEqual(@as(u8, 0), r2.call(fold, .{ @as(u8, 0), add }));
}
