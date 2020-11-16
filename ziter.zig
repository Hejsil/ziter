const std = @import("std");

const debug = std.debug;
const math = std.math;
const mem = std.mem;
const testing = std.testing;

/// Tests that an iterator returns all the items in the `expected`
/// slice, and no more.
pub fn test_it(_it: anytype, hint: LengthHint, expected: anytype) void {
    if (@hasDecl(@TypeOf(_it), "len_hint"))
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
    min: usize = 0,
    max: ?usize = null,

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
/// const it = filter(span("aaa"), fn(a:u8){ return a == 0: });
/// ```
/// This is an attempt at emulating ufc by having all iterators have one function called
/// `call`. With that function, you could build iterators like this:
/// ```
/// const it = span("aaa")
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

pub fn Chain(comptime First: type, comptime Second: type) type {
    return struct {
        first: First = First{},
        second: Second = Second{},

        pub fn next(it: *@This()) ?Result(First) {
            return it.first.next() orelse it.second.next();
        }

        pub fn len_hint(it: @This()) LengthHint {
            if (!@hasDecl(First, "len_hint") or !@hasDecl(Second, "len_hint"))
                return .{};

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
pub fn chain(first: anytype, second: anytype) Chain(@TypeOf(first), @TypeOf(second)) {
    return .{ .first = first, .second = second };
}

test "chain" {
    const abc = span("abc");
    const def = span("def");
    const non = span("");
    test_it(chain(abc, def), .{ .min = 6, .max = 6 }, "abcdef");
    test_it(chain(non, def), .{ .min = 3, .max = 3 }, "def");
    test_it(chain(abc, non), .{ .min = 3, .max = 3 }, "abc");
    test_it(chain(non, non), .{ .min = 0, .max = 0 }, "");
}

pub fn Deref(comptime Child: type) type {
    return Map(void, Child, @typeInfo(Result(Child)).Pointer.child);
}

/// Creates an iterator which derefs all of the items it iterates over.
pub fn deref(it: anytype) Deref(@TypeOf(it)) {
    const It = @TypeOf(it);
    return map(it, struct {
        fn transform(ptr: Result(It)) Result(Deref(It)) {
            return ptr.*;
        }
    }.transform);
}

test "deref" {
    test_it(span_by_ref("abcd").call(deref, .{}), .{ .min = 4, .max = 4 }, "abcd");
}

pub fn Enumerate(comptime I: type, comptime Child: type) type {
    return struct {
        index: I = 0,
        child: Child = Child{},

        pub const Res = struct {
            index: I,
            item: Result(Child),
        };

        pub fn next(it: *@This()) ?Res {
            const item = it.child.next() orelse return null;
            const index = it.index;
            it.index += 1;
            return Res{ .index = index, .item = item };
        }

        pub fn len_hint(it: @This()) LengthHint {
            if (!@hasDecl(Child, "len_hint"))
                return .{};

            return it.child.len_hint();
        }

        pub const call = call_method;
    };
}

/// Same as `enumerate_ex` but with `usize` passed as the second parameter.
pub fn enumerate(it: anytype) Enumerate(usize, @TypeOf(it)) {
    return enumerate_ex(it, usize);
}

/// Creates an iterator that gives the item index as well as the item.
pub fn enumerate_ex(it: anytype, comptime I: type) Enumerate(I, @TypeOf(it)) {
    return .{ .child = it };
}

test "enumerate" {
    var it = span("ab") //
        .call(enumerate, .{});

    testing.expectEqual(LengthHint{ .min = 2, .max = 2 }, it.len_hint());

    var i: usize = 0;
    while (it.next()) |item| : (i += 1) {
        testing.expectEqual(@as(usize, i), item.index);
        testing.expectEqual(@as(u8, "ab"[i]), item.item);
    }
}

pub fn ErrInner(comptime Child: type) type {
    const err_union = @typeInfo(ReturnType(@TypeOf(Child.next))).ErrorUnion;
    const Error = err_union.error_set;
    const Res = @typeInfo(err_union.payload).Optional.child;

    return struct {
        child: Child = Child{},

        pub fn next(it: *@This()) ?(Error!Res) {
            const res = it.child.next() catch |err| return err;
            return res orelse return null;
        }

        pub fn len_hint(it: @This()) LengthHint {
            if (!@hasDecl(Child, "len_hint"))
                return .{};

            return it.child.len_hint();
        }

        pub const call = call_method;
    };
}

/// Takes an iterator that returns `Error!?T` and makes it into an iterator
/// take returns `?(Error!T)`.
pub fn err_inner(it: anytype) ErrInner(@TypeOf(it)) {
    return .{ .child = it };
}

test "err_inner" {
    const Dummy = struct {
        const Error = error{A};

        num: usize = 0,
        fn next(it: *@This()) Error!?u8 {
            defer it.num += 1;
            switch (it.num) {
                0 => return 0,
                1 => return error.A,
                else => return null,
            }
        }
    };

    const i = err_inner(Dummy{});
    test_it(i, .{}, &[_](Dummy.Error!u8){ 0, error.A });
}

pub fn FilterMap(comptime Context: type, comptime Child: type, comptime T: type) type {
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
            if (!@hasDecl(Child, "len_hint"))
                return .{};

            return .{ .min = 0, .max = it.child.len_hint().max };
        }

        pub const call = call_method;
    };
}

/// Same as `filter_map_ex` but requires no context.
pub fn filter_map(
    it: anytype,
    transform: anytype,
) FilterMap(void, @TypeOf(it), ReturnTypeOpt(@TypeOf(transform))) {
    const Expect = fn (Result(@TypeOf(it))) ReturnType(@TypeOf(transform));
    const Transform = fn (void, Result(@TypeOf(it))) ReturnType(@TypeOf(transform));
    return filter_map_ex(it, {}, @ptrCast(Transform, @as(Expect, transform)));
}

/// Creates an iterator that transforms and filters out items the `transform` function.
pub fn filter_map_ex(
    it: anytype,
    ctx: anytype,
    transform: anytype,
) FilterMap(@TypeOf(ctx), @TypeOf(it), ReturnTypeOpt(@TypeOf(transform))) {
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

pub fn Filter(comptime Context: type, comptime Child: type) type {
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
            if (!@hasDecl(Child, "len_hint"))
                return .{};

            return .{ .min = 0, .max = it.child.len_hint().max };
        }

        pub const call = call_method;
    };
}

/// Same as `filter_ex` but requires no context.
pub fn filter(
    it: anytype,
    pred: fn (Result(@TypeOf(it))) bool,
) Filter(void, @TypeOf(it)) {
    return filter_ex(it, {}, @ptrCast(fn (void, Result(@TypeOf(it))) bool, pred));
}

/// Creates an iterator that filters out items that does not match
/// the predicate `pred`.
pub fn filter_ex(
    it: anytype,
    ctx: anytype,
    pred: fn (@TypeOf(ctx), Result(@TypeOf(it))) bool,
) Filter(@TypeOf(ctx), @TypeOf(it)) {
    return .{ .child = it, .ctx = ctx, .pred = pred };
}

test "filter" {
    const s1 = span("a1b2");
    const s2 = span("aaabb");
    test_it(s1.call(filter, .{std.ascii.isDigit}), .{ .min = 0, .max = 4 }, "12");
    test_it(s1.call(filter, .{std.ascii.isAlpha}), .{ .min = 0, .max = 4 }, "ab");
    test_it(s2.call(filter, .{std.ascii.isDigit}), .{ .min = 0, .max = 5 }, "");
}

pub fn InterLeave(comptime First: type, comptime Second: type) type {
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
            if (!@hasDecl(First, "len_hint") or !@hasDecl(Second, "len_hint"))
                return .{};

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
) InterLeave(@TypeOf(first), @TypeOf(second)) {
    return .{ .first = first, .second = second };
}

test "interleave" {
    const abc = span("abc");
    const def = span("def");
    const non = span("");
    test_it(interleave(abc, def), .{ .min = 6, .max = 6 }, "adbecf");
    test_it(interleave(non, def), .{ .min = 3, .max = 3 }, "def");
    test_it(interleave(abc, non), .{ .min = 3, .max = 3 }, "abc");
    test_it(interleave(non, non), .{ .min = 0, .max = 0 }, "");
}

pub fn Map(comptime Context: type, comptime Child: type, comptime T: type) type {
    return struct {
        child: Child = Child{},
        ctx: Context = undefined,
        transform: fn (Context, Result(Child)) T = undefined,

        pub fn next(it: *@This()) ?T {
            return it.transform(it.ctx, it.child.next() orelse return null);
        }

        pub fn len_hint(it: @This()) LengthHint {
            if (!@hasDecl(Child, "len_hint"))
                return .{};

            return it.child.len_hint();
        }

        pub const call = call_method;
    };
}

/// Same as `map_ex` but requires no context.
pub fn map(
    it: anytype,
    transform: anytype,
) Map(void, @TypeOf(it), ReturnType(@TypeOf(transform))) {
    const Expect = fn (Result(@TypeOf(it))) ReturnType(@TypeOf(transform));
    const Transform = fn (void, Result(@TypeOf(it))) ReturnType(@TypeOf(transform));
    return map_ex(it, {}, @ptrCast(Transform, @as(Expect, transform)));
}

/// Creates an iterator that transforms all items using the `transform` function.
pub fn map_ex(
    it: anytype,
    ctx: anytype,
    transform: anytype,
) Map(@TypeOf(ctx), @TypeOf(it), ReturnType(@TypeOf(transform))) {
    return .{ .child = it, .ctx = ctx, .transform = transform };
}

test "map" {
    const m1 = span("abcd") //
        .call(map, .{std.ascii.toUpper});
    test_it(m1, .{ .min = 4, .max = 4 }, "ABCD");

    const m2 = span("") //
        .call(map, .{std.ascii.toUpper});
    test_it(m2, .{ .min = 0, .max = 0 }, "");
}

pub fn SlidingWindow(comptime Child: type, comptime window: usize) type {
    return struct {
        prev: ?[window]T = null,
        child: Child = Child{},

        const T = Result(Child);

        pub fn next(it: *@This()) ?[window]T {
            if (it.prev) |*prev| {
                mem.copy(T, prev, prev[1..]);
                prev[window - 1] = it.child.next() orelse return null;
                return it.prev;
            } else {
                it.prev = [_]Result(Child){undefined} ** window;
                for (it.prev.?) |*item|
                    item.* = it.child.next() orelse return null;

                return it.prev;
            }
        }

        pub fn len_hint(it: @This()) LengthHint {
            if (!@hasDecl(Child, "len_hint"))
                return .{};

            const child = it.child.len_hint();
            return .{
                .min = math.sub(usize, child.min, window - 1) catch 0,
                .max = blk: {
                    const max = child.max orelse break :blk null;
                    break :blk math.sub(usize, max, window - 1) catch 0;
                },
            };
        }

        pub const call = call_method;
    };
}

/// Creates an iterator that iterates over the provided iterator and
/// returns a window into the elements of the iterator, and slides
/// that window along:
/// ```
/// span("abcde")
///     .call(sliding_window, {3}) = "abc"
///                                  "bcd"
///                                  "cde"
/// ```
pub fn sliding_window(it: anytype, comptime window: usize) SlidingWindow(@TypeOf(it), window) {
    return .{ .child = it };
}

test "sliding_window" {
    const s1 = span("abcd") //
        .call(sliding_window, .{2});
    test_it(s1, .{ .min = 3, .max = 3 }, [_][2]u8{ "ab".*, "bc".*, "cd".* });

    const s2 = span("abcd") //
        .call(sliding_window, .{3});
    test_it(s2, .{ .min = 2, .max = 2 }, [_][3]u8{ "abc".*, "bcd".* });
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

pub fn Repeat(comptime Child: type) type {
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
            if (!@hasDecl(Child, "len_hint"))
                return .{};

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
pub fn repeat(_it: anytype) Repeat(@TypeOf(_it)) {
    return .{ .reset = _it, .curr = _it };
}

test "repeat" {
    var it = span("ab") //
        .call(repeat, .{});

    testing.expectEqual(LengthHint{ .min = 2, .max = null }, it.len_hint());
    testing.expect(it.next().? == 'a');
    testing.expect(it.next().? == 'b');
    testing.expect(it.next().? == 'a');
    testing.expect(it.next().? == 'b');
    testing.expect(it.next().? == 'a');
    testing.expect(it.next().? == 'b');
}

pub fn Span(comptime S: type) type {
    const Array = @Type(.{
        .Array = .{
            .child = @typeInfo(S).Pointer.child,
            .sentinel = @typeInfo(S).Pointer.sentinel,
            .len = 0,
        },
    });

    return struct {
        span: S = &Array{},

        // HACK: Cannot use &it.span[0] here
        // --------------------------------vvvvvvvvvvvvvvvvvvvvvvvvv
        pub fn next(it: *@This()) ?@TypeOf(&@intToPtr(*S, 0x10).*[0]) {
            if (it.span.len == 0)
                return null;

            defer it.span = it.span[1..];
            return &it.span[0];
        }

        pub fn len_hint(it: @This()) LengthHint {
            return .{ .min = it.span.len, .max = it.span.len };
        }

        pub const call = call_method;
    };
}

/// Creates an iterator that iterates over all the items of an array or slice.
pub fn span(s: anytype) Deref(Span(mem.Span(@TypeOf(s)))) {
    return deref(span_by_ref(s));
}

test "span" {
    const items = "abcd";
    test_it(span(items[0..]), .{ .min = 4, .max = 4 }, items[0..]);
    test_it(span(items[1..]), .{ .min = 3, .max = 3 }, items[1..]);
    test_it(span(items[2..]), .{ .min = 2, .max = 2 }, items[2..]);
    test_it(span(items[3..]), .{ .min = 1, .max = 1 }, items[3..]);
    test_it(span(items[4..]), .{ .min = 0, .max = 0 }, items[4..]);
}

/// Creates an iterator that iterates over all the items of an array or slice
/// by reference.
pub fn span_by_ref(s: anytype) Span(mem.Span(@TypeOf(s))) {
    return .{ .span = mem.span(s) };
}

comptime {
    const c = "a".*;
    var v = "a".*;
    var sc = span_by_ref(&c);
    var sv = span_by_ref(&v);

    debug.assert(@TypeOf(sc.next()) == ?*const u8);
    debug.assert(@TypeOf(sv.next()) == ?*u8);
}

test "span_by_ref" {
    const items = "abcd";
    const refs = &[_]*const u8{ &items[0], &items[1], &items[2], &items[3] };
    test_it(span_by_ref(items[0..]), .{ .min = 4, .max = 4 }, refs[0..]);
    test_it(span_by_ref(items[1..]), .{ .min = 3, .max = 3 }, refs[1..]);
    test_it(span_by_ref(items[2..]), .{ .min = 2, .max = 2 }, refs[2..]);
    test_it(span_by_ref(items[3..]), .{ .min = 1, .max = 1 }, refs[3..]);
    test_it(span_by_ref(items[4..]), .{ .min = 0, .max = 0 }, refs[4..]);
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
        .call(skip, .{2});
    test_it(i, .{ .min = 2, .max = 2 }, "cd");
}

pub fn TakeWhile(comptime Context: type, comptime Child: type) type {
    return struct {
        child: Child = Child{},
        ctx: Context = undefined,
        pred: fn (Context, Result(Child)) bool = undefined,

        pub fn next(it: *@This()) ?Result(Child) {
            const item = it.child.next() orelse return null;
            return if (it.pred(it.ctx, item)) item else null;
        }

        pub fn len_hint(it: @This()) LengthHint {
            if (!@hasDecl(Child, "len_hint"))
                return .{};

            return .{ .min = 0, .max = it.child.len_hint().max };
        }
    };
}

/// Same as `take_while` but requires no context.
pub fn take_while(
    it: anytype,
    pred: fn (Result(@TypeOf(it))) bool,
) TakeWhile(void, @TypeOf(it)) {
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
) TakeWhile(@TypeOf(ctx), @TypeOf(it)) {
    return .{ .child = it, .ctx = ctx, .pred = pred };
}

test "take_while" {
    const tw = span("abCD") //
        .call(take_while, .{std.ascii.isLower});
    test_it(tw, .{ .min = 0, .max = 4 }, "ab");
}

pub fn Take(comptime Child: type) type {
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
            if (!@hasDecl(Child, "len_hint"))
                return .{ .max = it.n };

            return .{ .min = math.min(it.n, it.child.len_hint().min), .max = it.n };
        }
    };
}

/// Creates an iterator that takes at most `n` items from the child iterator.
pub fn take(it: anytype, n: usize) Take(@TypeOf(it)) {
    return .{ .child = it, .n = n };
}

test "take" {
    const abCD = span("abCD");
    test_it(abCD.call(take, .{1}), .{ .min = 1, .max = 1 }, "a");
    test_it(abCD.call(take, .{2}), .{ .min = 2, .max = 2 }, "ab");
    test_it(abCD.call(take, .{3}), .{ .min = 3, .max = 3 }, "abC");
}

pub fn Unwrap(comptime Child: type) type {
    const err_union = @typeInfo(Result(Child)).ErrorUnion;
    const Error = err_union.error_set;
    const Res = err_union.payload;

    return struct {
        child: Child = Child{},
        last_err: Error!void = {},

        pub fn next(it: *@This()) ?Res {
            const errun = it.child.next() orelse return null;
            return errun catch |err| {
                it.last_err = err;
                return null;
            };
        }

        pub fn len_hint(it: @This()) LengthHint {
            if (!@hasDecl(Child, "len_hint"))
                return .{};

            return it.child.len_hint();
        }

        pub const call = call_method;
    };
}

/// Creates an iterator that returns `null` on the first error returned
/// from the child iterator. The child iterator is expected to return
/// `?(Error!T)`. The error returned will be stored in a field called
/// `last_err`.
pub fn unwrap(it: anytype) Unwrap(@TypeOf(it)) {
    return .{ .child = it };
}

test "unwrap" {
    const Dummy = struct {
        const Error = error{A};

        num: usize = 0,
        fn next(it: *@This()) ?(Error!u8) {
            defer it.num += 1;
            switch (it.num) {
                // Without all these `@as` we get:
                // broken LLVM module found: Operand is null
                //  call fastcc void @__zig_return_error(<null operand!>), !dbg !6394
                0 => return @as(?(Error!u8), @as(Error!u8, 0)),
                1 => return @as(?(Error!u8), @as(Error!u8, error.A)),
                else => return null,
            }
        }
    };

    var i = unwrap(Dummy{});
    testing.expectEqual(@as(?u8, 0), i.next());
    testing.expectEqual(@as(?u8, null), i.next());
    testing.expectEqual(@as(Dummy.Error!void, error.A), i.last_err);
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
    testing.expect(span("aaa").call(all, .{std.ascii.isLower}));
    testing.expect(!span("Aaa").call(all, .{std.ascii.isLower}));
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
    testing.expect(span("aAA").call(any, .{std.ascii.isLower}));
    testing.expect(!span("AAA").call(any, .{std.ascii.isLower}));
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
    const aAA = span("aAA");
    const AAA = span("AAA");
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
