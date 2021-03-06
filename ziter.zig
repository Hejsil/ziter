const std = @import("std");

const debug = std.debug;
const math = std.math;
const mem = std.mem;
const testing = std.testing;

/// Tests that an iterator returns all the items in the `expected`
/// slice, and no more.
pub fn testIt(_it: anytype, hint: LengthHint, expected: anytype) !void {
    var it = iterator(_it);

    if (@hasDecl(@TypeOf(it), "len_hint"))
        try testing.expectEqual(hint, _it.len_hint());

    for (expected) |item|
        try testing.expectEqual(item, it.next().?);
    try testing.expect(it.next() == null);
}

fn Return(comptime F: type) type {
    return @typeInfo(F).Fn.return_type.?;
}

fn ReturnOpt(comptime F: type) type {
    return @typeInfo(Return(F)).Optional.child;
}

fn Predicate(comptime It: type) type {
    return fn (Result(It)) bool;
}

fn Predicate2(comptime Ctx: type, comptime It: type) type {
    return fn (Ctx, Result(It)) bool;
}

fn Compare(comptime It: type) type {
    return fn (Result(It), Result(It)) bool;
}

fn Compare2(comptime Ctx: type, comptime It: type) type {
    return fn (Ctx, Result(It), Result(It)) bool;
}

/// Get the type of the items an iterator iterates over.
pub fn Result(comptime It: type) type {
    return ReturnOpt(@TypeOf(Iterator(It).next));
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
///     .pipe(filter, .{ fn(a: u8){ return a == 0; } });
/// ```
pub fn pipeMethod(
    it: anytype,
    func: anytype,
    args: anytype,
) @TypeOf(@call(.{}, func, .{@TypeOf(it.*){}} ++ @as(@TypeOf(args), undefined))) {
    return @call(.{}, func, .{it.*} ++ args);
}

///////////////////////////////////////////////////////////
// The functions creates iterators from other data types //
///////////////////////////////////////////////////////////

pub fn Iterator(comptime T: type) type {
    switch (@typeInfo(T)) {
        .Pointer => |info| switch (info.size) {
            .One, .Slice => return Deref(Span(mem.Span(T))),
            else => {},
        },
        .Enum, .Union, .Struct => {
            if (@hasDecl(T, "next"))
                return T;
            if (@hasDecl(T, "iterator") and @hasDecl(T, "Iterator"))
                return T.Iterator;
        },
        else => {},
    }

    @compileError("Could not get an iterator from type '" ++ @typeName(T) ++ "'");
}

/// Given a value, this function will attempt to construct an iterator from the value.
/// * Slices and array pointers will give you a `Span` iterator
/// * Any value with a `iterator` method will give you the iterator that method returns.
/// * Any value with a `next` method will be considered an iterator and just returned.
pub fn iterator(value: anytype) Iterator(@TypeOf(value)) {
    const T = @TypeOf(value);
    switch (@typeInfo(T)) {
        .Pointer => |info| switch (info.size) {
            .One, .Slice => return span(value),
            else => {},
        },
        .Enum, .Union, .Struct => {
            if (@hasDecl(T, "iterator") and @hasDecl(T, "Iterator"))
                return value.iterator();
            if (@hasDecl(T, "next"))
                return value;
        },
        else => {},
    }
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

        pub const pipe = pipeMethod;
    };
}

/// Same as `rangeEx` with 1 passed to the `step` paramter.
pub fn range(comptime T: type, start: T, end: T) Range(T) {
    return rangeEx(T, start, end, 1);
}

/// Creates an iterator that iterates from `start` to `end` exclusively
/// with a step size of `step`.
pub fn rangeEx(comptime T: type, start: T, end: T, step: T) Range(T) {
    debug.assert(start <= end and step != 0);
    return .{ .start = start, .end = end, .step = step };
}

test "range" {
    try testIt(range(u8, 'a', 'd'), .{ .min = 3, .max = 3 }, "abc");
    try testIt(rangeEx(u8, 'a', 'd', 2), .{ .min = 2, .max = 2 }, "ac");
    try testIt(rangeEx(u8, 'a', 'd', 3), .{ .min = 1, .max = 1 }, "a");
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

        pub const pipe = pipeMethod;
    };
}

/// Creates an iterator that iterates over all the items of an array or slice.
pub fn span(s: anytype) Deref(Span(mem.Span(@TypeOf(s)))) {
    return deref(spanByRef(s));
}

test "span" {
    const items = "abcd";
    try testIt(span(items[0..]), .{ .min = 4, .max = 4 }, items[0..]);
    try testIt(span(items[1..]), .{ .min = 3, .max = 3 }, items[1..]);
    try testIt(span(items[2..]), .{ .min = 2, .max = 2 }, items[2..]);
    try testIt(span(items[3..]), .{ .min = 1, .max = 1 }, items[3..]);
    try testIt(span(items[4..]), .{ .min = 0, .max = 0 }, items[4..]);
}

/// Creates an iterator that iterates over all the items of an array or slice
/// by reference.
pub fn spanByRef(s: anytype) Span(mem.Span(@TypeOf(s))) {
    return .{ .span = mem.span(s) };
}

comptime {
    const c = "a".*;
    var v = "a".*;
    var sc = spanByRef(&c);
    var sv = spanByRef(&v);

    debug.assert(@TypeOf(sc.next()) == ?*const u8);
    debug.assert(@TypeOf(sv.next()) == ?*u8);
}

test "spanByRef" {
    const items = "abcd";
    const refs = &[_]*const u8{ &items[0], &items[1], &items[2], &items[3] };
    try testIt(spanByRef(items[0..]), .{ .min = 4, .max = 4 }, refs[0..]);
    try testIt(spanByRef(items[1..]), .{ .min = 3, .max = 3 }, refs[1..]);
    try testIt(spanByRef(items[2..]), .{ .min = 2, .max = 2 }, refs[2..]);
    try testIt(spanByRef(items[3..]), .{ .min = 1, .max = 1 }, refs[3..]);
    try testIt(spanByRef(items[4..]), .{ .min = 0, .max = 0 }, refs[4..]);
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

        pub const pipe = pipeMethod;
    };
}

/// Creates an iterator that first iterates over all items in `first` after
/// which it iterates over all elements in `second`.
pub fn chain(first: anytype, second: anytype) Chain(
    Iterator(@TypeOf(first)),
    Iterator(@TypeOf(second)),
) {
    return .{ .first = iterator(first), .second = iterator(second) };
}

test "chain" {
    try testIt(chain("abc", "def"), .{ .min = 6, .max = 6 }, "abcdef");
    try testIt(chain("", "def"), .{ .min = 3, .max = 3 }, "def");
    try testIt(chain("abc", ""), .{ .min = 3, .max = 3 }, "abc");
    try testIt(chain("", ""), .{ .min = 0, .max = 0 }, "");
}

pub fn Deref(comptime Child: type) type {
    return Map(void, Child, @typeInfo(Result(Child)).Pointer.child);
}

/// Creates an iterator which derefs all of the items it iterates over.
pub fn deref(it: anytype) Deref(Iterator(@TypeOf(it))) {
    const It = @TypeOf(it);
    return mapEx(it, {}, struct {
        fn transform(_: void, ptr: Result(It)) Result(Deref(It)) {
            return ptr.*;
        }
    }.transform);
}

test "deref" {
    try testIt(spanByRef("abcd").pipe(deref, .{}), .{ .min = 4, .max = 4 }, "abcd");
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

        pub const pipe = pipeMethod;
    };
}

/// Same as `enumerateEx` but with `usize` passed as the second parameter.
pub fn enumerate(it: anytype) Enumerate(usize, Iterator(@TypeOf(it))) {
    return enumerateEx(it, usize);
}

/// Creates an iterator that gives the item index as well as the item.
pub fn enumerateEx(it: anytype, comptime I: type) Enumerate(I, Iterator(@TypeOf(it))) {
    return .{ .child = iterator(it) };
}

test "enumerate" {
    var it = enumerate("ab");
    try testing.expectEqual(LengthHint{ .min = 2, .max = 2 }, it.len_hint());

    var i: usize = 0;
    while (it.next()) |item| : (i += 1) {
        try testing.expectEqual(@as(usize, i), item.index);
        try testing.expectEqual(@as(u8, "ab"[i]), item.item);
    }
}

pub fn ErrInner(comptime Child: type) type {
    const err_union = @typeInfo(Return(@TypeOf(Child.next))).ErrorUnion;
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

        pub const pipe = pipeMethod;
    };
}

/// Takes an iterator that returns `Error!?T` and makes it into an iterator
/// take returns `?(Error!T)`.
pub fn errInner(it: anytype) ErrInner(Iterator(@TypeOf(it))) {
    return .{ .child = iterator(it) };
}

test "errInner" {
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

    const i = errInner(Dummy{});
    try testIt(i, .{}, &[_](Dummy.Error!u8){ 0, error.A });
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

        pub const pipe = pipeMethod;
    };
}

/// Same as `filterMapEx` but requires no context.
pub fn filterMap(
    it: anytype,
    transform: anytype,
) FilterMap(@TypeOf(transform), Iterator(@TypeOf(it)), ReturnOpt(@TypeOf(transform))) {
    const Iter = Iterator(@TypeOf(it));
    const Res = Result(Iter);
    const Trans = @TypeOf(transform);
    return filterMapEx(it, transform, struct {
        fn wrapper(trans: Trans, item: Res) Return(Trans) {
            return trans(item);
        }
    }.wrapper);
}

/// Creates an iterator that transforms and filters out items the `transform` function.
pub fn filterMapEx(
    it: anytype,
    ctx: anytype,
    transform: anytype,
) FilterMap(@TypeOf(ctx), Iterator(@TypeOf(it)), ReturnOpt(@TypeOf(transform))) {
    return .{ .child = iterator(it), .ctx = ctx, .transform = transform };
}

test "filterMap" {
    const F = struct {
        fn even_double(i: u8) ?u16 {
            if (i % 2 != 0)
                return null;
            return i * 2;
        }
    };
    const i = range(u8, 0, 10) //
        .pipe(filterMap, .{F.even_double});
    try testIt(i, .{ .min = 0, .max = 10 }, &[_]u16{ 0, 4, 8, 12, 16 });
}

pub fn Filter(comptime Context: type, comptime Child: type) type {
    return struct {
        child: Child = Child{},
        ctx: Context = undefined,
        pred: Predicate2(Context, Child) = undefined,

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

        pub const pipe = pipeMethod;
    };
}

/// Same as `filterEx` but requires no context.
pub fn filter(
    it: anytype,
    pred: Predicate(@TypeOf(it)),
) Filter(Predicate(@TypeOf(it)), Iterator(@TypeOf(it))) {
    const Iter = Iterator(@TypeOf(it));
    const Res = Result(Iter);
    const Pred = fn (Res) bool;
    return filterEx(it, pred, struct {
        fn wrapper(p: Pred, item: Res) bool {
            return p(item);
        }
    }.wrapper);
}

/// Creates an iterator that filters out items that does not match
/// the predicate `pred`.
pub fn filterEx(
    it: anytype,
    ctx: anytype,
    pred: Predicate2(@TypeOf(ctx), @TypeOf(it)),
) Filter(@TypeOf(ctx), Iterator(@TypeOf(it))) {
    return .{ .child = iterator(it), .ctx = ctx, .pred = pred };
}

test "filter" {
    try testIt(filter("a1b2", std.ascii.isDigit), .{ .min = 0, .max = 4 }, "12");
    try testIt(filter("a1b2", std.ascii.isAlpha), .{ .min = 0, .max = 4 }, "ab");
    try testIt(filter("aaabb", std.ascii.isDigit), .{ .min = 0, .max = 5 }, "");
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

        pub const pipe = pipeMethod;
    };
}

/// Creates an iterator switches between calling `first.next` and `second.next`.
pub fn interleave(
    first: anytype,
    second: anytype,
) InterLeave(Iterator(@TypeOf(first)), Iterator(@TypeOf(second))) {
    return .{ .first = iterator(first), .second = iterator(second) };
}

test "interleave" {
    try testIt(interleave("abc", "def"), .{ .min = 6, .max = 6 }, "adbecf");
    try testIt(interleave("", "def"), .{ .min = 3, .max = 3 }, "def");
    try testIt(interleave("abc", ""), .{ .min = 3, .max = 3 }, "abc");
    try testIt(interleave("", ""), .{ .min = 0, .max = 0 }, "");
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

        pub const pipe = pipeMethod;
    };
}

/// Same as `mapEx` but requires no context.
pub fn map(
    it: anytype,
    transform: anytype,
) Map(@TypeOf(transform), Iterator(@TypeOf(it)), Return(@TypeOf(transform))) {
    const Iter = Iterator(@TypeOf(it));
    const Res = Result(Iter);
    const Trans = @TypeOf(transform);
    return mapEx(it, transform, struct {
        fn wrapper(trans: Trans, item: Res) Return(Trans) {
            return trans(item);
        }
    }.wrapper);
}

/// Creates an iterator that transforms all items using the `transform` function.
pub fn mapEx(
    it: anytype,
    ctx: anytype,
    transform: anytype,
) Map(@TypeOf(ctx), Iterator(@TypeOf(it)), Return(@TypeOf(transform))) {
    return .{ .child = iterator(it), .ctx = ctx, .transform = transform };
}

test "map" {
    const m1 = map("abcd", std.ascii.toUpper);
    try testIt(m1, .{ .min = 4, .max = 4 }, "ABCD");

    const m2 = map("", std.ascii.toUpper);
    try testIt(m2, .{ .min = 0, .max = 0 }, "");
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

        pub const pipe = pipeMethod;
    };
}

/// Creates an iterator that iterates over the provided iterator and
/// returns a window into the elements of the iterator, and slides
/// that window along:
/// ```
/// span("abcde")
///     .pipe(slidingWindow, {3}) = "abc"
///                                  "bcd"
///                                  "cde"
/// ```
pub fn slidingWindow(
    it: anytype,
    comptime window: usize,
) SlidingWindow(Iterator(@TypeOf(it)), window) {
    return .{ .child = iterator(it) };
}

test "slidingWindow" {
    const s1 = slidingWindow("abcd", 2);
    try testIt(s1, .{ .min = 3, .max = 3 }, [_][2]u8{ "ab".*, "bc".*, "cd".* });

    const s2 = slidingWindow("abcd", 3);
    try testIt(s2, .{ .min = 2, .max = 2 }, [_][3]u8{ "abc".*, "bcd".* });
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

        pub const pipe = pipeMethod;
    };
}

/// Creates an iterator that keeps repeating the items returned from the
/// child iterator, never returning `null` unless the child iterator returns
/// no items, in which case `repeat` always returns `null`.
pub fn repeat(it: anytype) Repeat(Iterator(@TypeOf(it))) {
    return .{ .reset = iterator(it), .curr = iterator(it) };
}

test "repeat" {
    var it = repeat("ab");
    try testing.expectEqual(LengthHint{ .min = 2, .max = null }, it.len_hint());
    try testing.expect(it.next().? == 'a');
    try testing.expect(it.next().? == 'b');
    try testing.expect(it.next().? == 'a');
    try testing.expect(it.next().? == 'b');
    try testing.expect(it.next().? == 'a');
    try testing.expect(it.next().? == 'b');
}

/// Skips `n` iterations of `it` and return it.
pub fn skip(_it: anytype, _n: usize) Iterator(@TypeOf(_it)) {
    var n = _n;
    var it = iterator(_it);
    while (n != 0) : (n -= 1)
        _ = it.next();
    return it;
}

test "skip" {
    const i = skip("abcd", 2);
    try testIt(i, .{ .min = 2, .max = 2 }, "cd");
}

pub fn TakeWhile(comptime Context: type, comptime Child: type) type {
    return struct {
        child: Child = Child{},
        ctx: Context = undefined,
        pred: Predicate2(Context, Child) = undefined,

        pub fn next(it: *@This()) ?Result(Child) {
            const item = it.child.next() orelse return null;
            return if (it.pred(it.ctx, item)) item else null;
        }

        pub fn len_hint(it: @This()) LengthHint {
            if (!@hasDecl(Child, "len_hint"))
                return .{};

            return .{ .min = 0, .max = it.child.len_hint().max };
        }

        pub const pipe = pipeMethod;
    };
}

/// Same as `takeWhile` but requires no context.
pub fn takeWhile(
    it: anytype,
    pred: Predicate(@TypeOf(it)),
) TakeWhile(Predicate(@TypeOf(it)), Iterator(@TypeOf(it))) {
    const Res = Result(@TypeOf(it));
    const Pred = Predicate(@TypeOf(it));
    return takeWhileEx(it, pred, struct {
        fn wrapper(p: Pred, item: Res) bool {
            return p(item);
        }
    }.wrapper);
}

/// Creates an iterator that takes values from the child iterator so long
/// as they matches the predicate `pred`. When the predicate is no longer
/// satisfied, the iterator will return null.
pub fn takeWhileEx(
    it: anytype,
    ctx: anytype,
    pred: Predicate2(@TypeOf(ctx), @TypeOf(it)),
) TakeWhile(@TypeOf(ctx), Iterator(@TypeOf(it))) {
    return .{ .child = iterator(it), .ctx = ctx, .pred = pred };
}

test "takeWhile" {
    const tw = takeWhile("abCD", std.ascii.isLower);
    try testIt(tw, .{ .min = 0, .max = 4 }, "ab");
}

pub fn Take(comptime Child: type) type {
    return struct {
        child: Child = Child{},
        n: usize = 0,

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

        pub const pipe = pipeMethod;
    };
}

/// Creates an iterator that takes at most `n` items from the child iterator.
pub fn take(it: anytype, n: usize) Take(Iterator(@TypeOf(it))) {
    return .{ .child = iterator(it), .n = n };
}

test "take" {
    try testIt(take("abCD", 1), .{ .min = 1, .max = 1 }, "a");
    try testIt(take("abCD", 2), .{ .min = 2, .max = 2 }, "ab");
    try testIt(take("abCD", 3), .{ .min = 3, .max = 3 }, "abC");
}

pub fn Dedup(comptime Context: type, comptime Child: type) type {
    const Res = Result(Child);

    return struct {
        child: Child = Child{},
        ctx: Context = undefined,
        eql: fn (Context, Res, Res) bool = undefined,
        prev: ?Res = null,

        pub fn next(it: *@This()) ?Res {
            var prev = it.prev orelse {
                it.prev = it.child.next();
                return it.prev;
            };

            var curr = it.child.next() orelse return null;
            while (it.eql(it.ctx, prev, curr)) {
                prev = curr;
                curr = it.child.next() orelse return null;
            }

            it.prev = curr;
            return curr;
        }

        pub fn len_hint(it: @This()) LengthHint {
            if (!@hasDecl(Child, "len_hint"))
                return .{};

            return .{ .min = 0, .max = it.child.len_hint().max };
        }

        pub const pipe = pipeMethod;
    };
}

/// Removes dublicates from consectutive identical results using
/// `eql` to determin if two results are identical.
pub fn dedup(it: anytype) Dedup(Compare(@TypeOf(it)), Iterator(@TypeOf(it))) {
    const Iter = Iterator(@TypeOf(it));
    const Res = Result(Iter);
    return dedupEx(it, struct {
        fn eql(a: Res, b: Res) bool {
            return a == b;
        }
    }.eql);
}

/// Removes dublicates from consectutive identical results using
/// `eql` to determin if two results are identical.
pub fn dedupEx(
    it: anytype,
    eql: Compare(@TypeOf(it)),
) Dedup(Compare(@TypeOf(it)), Iterator(@TypeOf(it))) {
    const Res = Result(@TypeOf(it));
    const Eql = Compare(@TypeOf(it));
    return dedupEx2(it, eql, struct {
        fn eql(func: Eql, a: Res, b: Res) bool {
            return func(a, b);
        }
    }.eql);
}

/// Removes dublicates from consectutive identical results using
/// `eql` to determin if two results are identical.
pub fn dedupEx2(
    it: anytype,
    ctx: anytype,
    eql: Compare2(@TypeOf(ctx), @TypeOf(it)),
) Dedup(@TypeOf(ctx), Iterator(@TypeOf(it))) {
    return .{ .child = iterator(it), .ctx = ctx, .eql = eql };
}

test "dedup" {
    const dd = dedup("aaabbcccdd");
    try testIt(dd, .{ .min = 0, .max = 10 }, "abcd");

    const dd2 = dedupEx(&[_][]const u8{ "aa", "AA", "ba", "BA" }, std.ascii.eqlIgnoreCase);
    try testIt(dd2, .{ .min = 0, .max = 4 }, &[_][]const u8{ "aa", "ba" });
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

        pub const pipe = pipeMethod;
    };
}

/// Creates an iterator that returns `null` on the first error returned
/// from the child iterator. The child iterator is expected to return
/// `?(Error!T)`. The error returned will be stored in a field called
/// `last_err`.
pub fn unwrap(it: anytype) Unwrap(Iterator(@TypeOf(it))) {
    return .{ .child = iterator(it) };
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
    try testing.expectEqual(@as(?u8, 0), i.next());
    try testing.expectEqual(@as(?u8, null), i.next());
    try testing.expectEqual(@as(Dummy.Error!void, error.A), i.last_err);
}

/////////////////////////////////////////////////////////////////
// The functions below iterates over iterators to get a result //
/////////////////////////////////////////////////////////////////

/// Same as `allEx` but requires no context.
pub fn all(it: anytype, pred: Predicate(@TypeOf(it))) bool {
    const Iter = Iterator(@TypeOf(it));
    const Res = Result(Iter);
    const Pred = fn (Res) bool;
    return allEx(it, pred, struct {
        fn wrapper(p: Pred, res: Res) bool {
            return p(res);
        }
    }.wrapper);
}

/// Check that all items in an iterator matches a predicate.
pub fn allEx(
    _it: anytype,
    ctx: anytype,
    pred: Predicate2(@TypeOf(ctx), @TypeOf(_it)),
) bool {
    var it = iterator(_it);
    while (it.next()) |item| {
        if (!pred(ctx, item))
            return false;
    }

    return true;
}

test "all" {
    try testing.expect(all("aaa", std.ascii.isLower));
    try testing.expect(!all("Aaa", std.ascii.isLower));
}

/// Same as `anyEx` but requires no context.
pub fn any(it: anytype, pred: Predicate(@TypeOf(it))) bool {
    const Res = Result(@TypeOf(it));
    const Pred = Predicate(@TypeOf(it));
    return anyEx(it, pred, struct {
        fn wrapper(p: Pred, res: Res) bool {
            return p(res);
        }
    }.wrapper);
}

/// Check that any items in an iterator matches a predicate.
pub fn anyEx(
    it: anytype,
    ctx: anytype,
    pred: Predicate2(@TypeOf(ctx), @TypeOf(it)),
) bool {
    return findEx(it, ctx, pred) != null;
}

test "any" {
    try testing.expect(any("aAA", std.ascii.isLower));
    try testing.expect(!any("AAA", std.ascii.isLower));
}

pub fn collect(
    _it: anytype,
    allocator: *mem.Allocator,
) mem.Allocator.Error![]Result(@TypeOf(_it)) {
    var it = iterator(_it);

    var res = std.ArrayList(Result(@TypeOf(it))).init(allocator);
    errdefer res.deinit();

    if (@hasDecl(@TypeOf(it), "len_hint"))
        try res.ensureCapacity(it.len_hint().min);

    while (it.next()) |item|
        try res.append(item);

    return res.items;
}

test "collect" {
    const collected = try collect("abcd", testing.allocator);
    defer testing.allocator.free(collected);

    try testing.expectEqualSlices(u8, "abcd", collected);

    const collected_range = try range(usize, 0, 5) //
        .pipe(collect, .{testing.allocator});
    defer testing.allocator.free(collected_range);

    try testing.expectEqualSlices(usize, &[_]usize{ 0, 1, 2, 3, 4 }, collected_range);
}

/// Counts the number of iterations before an iterator returns `null`.
pub fn count(_it: anytype) usize {
    var it = iterator(_it);

    if (@hasDecl(@TypeOf(it), "len_hint")) {
        if (it.len_hint().len()) |len|
            return len;
    }

    var res: usize = 0;
    while (it.next()) |_|
        res += 1;

    return res;
}

test "count" {
    try testing.expectEqual(@as(usize, 0), count(""));
    try testing.expectEqual(@as(usize, 1), count("a"));
    try testing.expectEqual(@as(usize, 2), count("aa"));
}

/// Same as `findEx` but requires no context.
pub fn find(it: anytype, pred: Predicate(@TypeOf(it))) ?Result(@TypeOf(it)) {
    const Res = Result(@TypeOf(it));
    const Pred = Predicate(@TypeOf(it));
    return findEx(it, pred, struct {
        fn wrapper(p: Pred, res: Res) bool {
            return p(res);
        }
    }.wrapper);
}

/// Gets the first item in an iterator that satiesfies the predicate.
pub fn findEx(
    _it: anytype,
    ctx: anytype,
    pred: Predicate2(@TypeOf(ctx), @TypeOf(_it)),
) ?Result(@TypeOf(_it)) {
    var it = iterator(_it);
    while (it.next()) |item| {
        if (pred(ctx, item))
            return item;
    }

    return null;
}

test "find" {
    try testing.expect(find("aAA", std.ascii.isLower).? == 'a');
    try testing.expect(find("AAA", std.ascii.isLower) == null);
}

/// Same as `foldEx` but requires no context.
pub fn fold(
    it: anytype,
    init: anytype,
    f: fn (@TypeOf(init), Result(@TypeOf(it))) @TypeOf(init),
) @TypeOf(init) {
    const Res = Result(@TypeOf(it));
    const Init = @TypeOf(init);
    const Func = fn (Init, Res) Init;
    return foldEx(it, init, f, struct {
        fn wrapper(func: Func, acc: Init, item: Res) Init {
            return func(acc, item);
        }
    }.wrapper);
}

/// Iterates over an iterator to get a single resulting value. This result is aquired
/// by starting with the value of `init` and calling the function `f` on all result +
/// item pairs, reassing the result to the return value of `f` on each iteration. Once
/// all items have been iterated over the result is returned.
pub fn foldEx(
    _it: anytype,
    init: anytype,
    ctx: anytype,
    f: fn (@TypeOf(ctx), @TypeOf(init), Result(@TypeOf(_it))) @TypeOf(init),
) @TypeOf(init) {
    var res = init;
    var it = iterator(_it);
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

    const r1 = rangeEx(u8, 2, 8, 2);
    const r2 = range(u8, 0, 0);
    try testing.expectEqual(@as(u8, 12), r1.pipe(fold, .{ @as(u8, 0), add }));
    try testing.expectEqual(@as(u8, 0), r2.pipe(fold, .{ @as(u8, 0), add }));
}

/////////////////////////////////////////////////////
// Tests that std iterators also works with ziter. //
/////////////////////////////////////////////////////

// test "mem.split" {
//     const eql = struct {
//         fn eql(comptime c: []const u8) fn ([]const u8) bool {
//             return struct {
//                 fn e(str: []const u8) bool {
//                     return mem.eql(u8, str, c);
//                 }
//             }.e;
//         }
//     }.eql;

//     const it = take(mem.split("a\nab\nabc\ncc", "\n"), 3);
//     try testing.expect(any(it, eql("abc")));
//     try testing.expect(any(it, eql("a")));
//     try testing.expect(any(it, eql("ab")));
//     try testing.expect(any(it, eql("abc")));
//     try testing.expect(!any(it, eql("cc")));
// }
