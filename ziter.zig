const std = @import("std");

const math = std.math;
const testing = std.testing;

const ziter = @This();

/// Given *[N]T or []T, returns an iterator that can iterate over all items in these types both
/// forward and backwards. Items are iterated by pointer. If you want by value, see `deref`.
pub fn slice(s: anytype) Slice(ToSlice(@TypeOf(s))) {
    return .{ .slice = s, .start = 0, .end = s.len };
}

pub fn Slice(comptime _T: type) type {
    return struct {
        slice: T,
        start: usize,
        end: usize,

        pub const T = _T;
        pub const Item = ToOnePtr(T);

        pub fn next(it: *@This()) ?Item {
            if (it.start >= it.end)
                return null;

            defer it.start += 1;
            return &it.slice[it.start];
        }

        pub fn next_back(it: *@This()) ?Item {
            if (it.start >= it.end)
                return null;

            it.end -= 1;
            return &it.slice[it.end];
        }

        pub usingnamespace ziter;
    };
}

fn ToOnePtr(comptime T: type) type {
    var info = @typeInfo(T);
    info.Pointer.child = std.meta.Elem(T);
    info.Pointer.size = .One;
    return @Type(info);
}

fn ToSlice(comptime T: type) type {
    var info = @typeInfo(T);
    info.Pointer.child = std.meta.Elem(T);
    info.Pointer.size = .Slice;
    return @Type(info);
}

test "slice" {
    const items = "abcd";
    var it1 = slice(items);
    for (items) |*expected|
        try testing.expectEqual(@as(?*const u8, expected), it1.next());

    try testing.expectEqual(@as(?*const u8, null), it1.next());

    var it2 = slice(items);
    var i: usize = items.len;
    while (i != 0) : (i -= 1)
        try testing.expectEqual(@as(?*const u8, &items[i - 1]), it2.next_back());

    try testing.expectEqual(@as(?*const u8, null), it2.next());

    var it3 = slice(items);
    try testing.expectEqual(@as(?*const u8, &items[0]), it3.next());
    try testing.expectEqual(@as(?*const u8, &items[3]), it3.next_back());
    try testing.expectEqual(@as(?*const u8, &items[2]), it3.next_back());
    try testing.expectEqual(@as(?*const u8, &items[1]), it3.next());
    try testing.expectEqual(@as(?*const u8, null), it3.next());
}

/// Creates an iterator that contains one item.
pub fn one(v: anytype) One(@TypeOf(v)) {
    return .{ .item = v };
}

pub fn One(comptime _Item: type) type {
    return struct {
        item: ?Item,

        pub const Item = _Item;

        pub fn next(it: *@This()) ?Item {
            defer it.item = null;
            return it.item;
        }

        pub const next_back = next;

        pub usingnamespace ziter;
    };
}

test "one" {
    try expectEqual(deref("a"), one(@as(u8, 'a')));
    try expectEqualReverse(deref("a"), one(@as(u8, 'a')));
}

/// Given ?T, returns an iterator that first returns the payload (if any) and then null.
pub fn optional(o: anytype) Iterator(@TypeOf(o)) {
    return .{ .item = o };
}

test "optional" {
    try expectEqual(deref("a"), optional(@as(?u8, 'a')));
    try expectEqual(deref(""), optional(@as(?u8, null)));
    try expectEqualReverse(deref("a"), optional(@as(?u8, 'a')));
    try expectEqualReverse(deref(""), optional(@as(?u8, null)));
}

/// Given anyerror!T, returns an iterator that first returns the payload (if any) and then null.
pub fn error_union(u: anytype) Iterator(@TypeOf(u)) {
    return optional(u catch null);
}

test "error_union" {
    try expectEqual(deref("a"), error_union(@as(anyerror!u8, 'a')));
    try expectEqual(deref(""), error_union(@as(anyerror!u8, error.Oof)));
    try expectEqualReverse(deref("a"), error_union(@as(anyerror!u8, 'a')));
    try expectEqualReverse(deref(""), error_union(@as(anyerror!u8, error.Oof)));
}

/// Returns an iterator that gives all ints from `from` to `to`. Can be iterated backwards as well.
pub fn range(comptime Item: type, from: Item, to: Item) Range(Item) {
    return .{ .from = from, .to = to };
}

pub fn Range(comptime _Item: type) type {
    return struct {
        from: Inner,
        to: Inner,

        // To avoid overflows when `from` is minInt or `to` is maxInt we have `from` and `to`
        // be this new int that makes room for going above or below those values.
        const Inner = math.IntFittingRange(math.minInt(Item) - 1, math.maxInt(Item) + 1);

        pub const Item = _Item;

        pub fn next(it: *@This()) ?Item {
            if (it.from > it.to)
                return null;

            defer it.from += 1;
            return @intCast(Item, it.from);
        }

        pub fn next_back(it: *@This()) ?Item {
            if (it.from > it.to)
                return null;

            defer it.to -= 1;
            return @intCast(Item, it.to);
        }

        pub usingnamespace ziter;
    };
}

test "range" {
    try expectEqual(deref("abcd"), range(u8, 'a', 'd'));
    try expectEqualReverse(deref("abcd"), range(u8, 'a', 'd'));
    try expectEqual(deref(&[_]u8{0}), range(u8, 0, 0));
    try expectEqualReverse(deref(&[_]u8{0}), range(u8, 0, 0));
    try expectEqual(deref(&[_]u8{255}), range(u8, 255, 255));
    try expectEqualReverse(deref(&[_]u8{255}), range(u8, 255, 255));

    const all_u8 = blk: {
        var items: [256]u8 = undefined;
        for (&items, 0..) |*item, i|
            item.* = @intCast(u8, i);

        std.debug.assert(items[0] == 0);
        std.debug.assert(items[255] == 255);
        break :blk items;
    };
    try expectEqual(deref(&all_u8), range(u8, 0, 255));
    try expectEqualReverse(deref(&all_u8), range(u8, 0, 255));

    var i: u64 = 0;
    while (i < 100) : (i += 1) {
        var random = std.rand.DefaultPrng.init(i);
        try expectEqualRandomOrder(random.random(), deref(&all_u8), range(u8, 0, 255));
    }
}

/// Creates an empty iterator.
pub fn empty(comptime Item: type) Empty(Item) {
    return .{};
}

pub fn Empty(comptime _Item: type) type {
    return struct {
        pub const Item = _Item;

        pub fn next(_: @This()) ?Item {
            return null;
        }
    };
}

test "empty" {
    try expectEqual(slice(""), empty(*const u8));
    try expectEqual(deref(""), empty(u8));
}

/// Counts the number of items `next` returns before `null`
pub fn count(_it: anytype) usize {
    var result: usize = 0;

    var it = iterator(_it);
    while (it.next()) |_|
        result += 1;

    return result;
}

test "count" {
    try testing.expectEqual(@as(usize, 4), slice("abcd").count());
    try testing.expectEqual(@as(usize, 4), count(slice("abcd")));
    try testing.expectEqual(@as(usize, 0), slice("").count());
    try testing.expectEqual(@as(usize, 0), count(slice("")));
}

/// Given an iterator, this function will return the last item of the iterator. If the iterator
/// can be iterated backwards, then this function is O(1). If not, then it is O(n).
pub fn last(_it: anytype) ?IteratorItem(@TypeOf(_it)) {
    const It = Iterator(@TypeOf(_it));
    var it = iterator(_it);
    if (@hasDecl(It, "next_back"))
        return it.next_back();

    var result: ?IteratorItem(@TypeOf(_it)) = null;
    while (it.next()) |item|
        result = item;

    return result;
}

test "last" {
    const items = "abcd";
    try testing.expectEqual(@as(?*const u8, &items[items.len - 1]), slice(items).last());
    try testing.expectEqual(@as(?*const u8, &items[items.len - 1]), last(slice(items)));
    try testing.expectEqual(@as(?*const u8, null), slice("").last());
    try testing.expectEqual(@as(?*const u8, null), last(slice("")));
}

/// Given an iterator, this function will return the first item of the iterator.
pub fn first(_it: anytype) ?IteratorItem(@TypeOf(_it)) {
    return nth(_it, 0);
}

test "first" {
    const items = "abcd";
    try testing.expectEqual(@as(?*const u8, &items[0]), slice(items).first());
    try testing.expectEqual(@as(?*const u8, &items[0]), first(slice(items)));
    try testing.expectEqual(@as(?*const u8, null), slice("").first());
    try testing.expectEqual(@as(?*const u8, null), first(slice("")));
}

/// Given an iterator, this function will return the nth item of the iterator. This function is
/// O(n) in worst case.
pub fn nth(_it: anytype, n: usize) ?IteratorItem(@TypeOf(_it)) {
    var curr: usize = 0;

    var it = iterator(_it);
    var result = it.next() orelse return null;
    while (curr < n) : (curr += 1)
        result = it.next() orelse return null;

    return result;
}

test "nth" {
    const items = "abcd";
    for (0..items.len) |i| {
        try testing.expectEqual(@as(?*const u8, &items[i]), slice(items).nth(i));
        try testing.expectEqual(@as(?*const u8, &items[i]), nth(slice(items), i));
    }
    try testing.expectEqual(@as(?*const u8, null), slice(items).nth(items.len));
    try testing.expectEqual(@as(?*const u8, null), nth(slice(items), items.len));
}

/// Creates an iterator that starts at the old iterators first item and returns every nths item
/// from there. This is semantically the same as `it.nth(n*0); it.nth(n*1); it.nth(n*2); ...` in
/// iterator form.
pub fn step_by(_it: anytype, step: usize) StepBy(Iterator(@TypeOf(_it))) {
    return .{ .it = iterator(_it), .step = step };
}

pub fn StepBy(comptime _It: type) type {
    return struct {
        it: It,
        step: usize,

        pub const It = _It;
        pub const Item = IteratorItem(It);

        pub fn next(it: *@This()) ?Item {
            const result = it.it.next() orelse return null;

            var times_stepped: usize = 1;
            while (times_stepped < it.step) : (times_stepped += 1)
                _ = it.it.next() orelse break;

            return result;
        }

        pub usingnamespace ziter;
    };
}

test "step_by" {
    const items = deref("abcdefgh");
    const results = deref("aceg");

    try expectEqual(results, items.step_by(2));
    try expectEqual(results, step_by(items, 2));
}

/// Creates an iterator that starts at `first` and continues on to `second` when `first` is
/// empty. Can be iterated backwards as well, starting at `second` until empty. Then continuing
/// to `first`. This requires that both iterators can be iterated backwards.
pub fn chain(first_it: anytype, second_it: anytype) Chain(
    Iterator(@TypeOf(first_it)),
    Iterator(@TypeOf(second_it)),
) {
    return .{ .first = iterator(first_it), .second = iterator(second_it) };
}

pub fn Chain(comptime _First: type, comptime _Second: type) type {
    return struct {
        first: First,
        second: Second,

        pub const First = _First;
        pub const Second = _Second;
        pub const Item = IteratorItem(First);

        pub fn next(it: *@This()) ?Item {
            return it.first.next() orelse it.second.next();
        }

        pub fn next_back(it: *@This()) ?Item {
            return it.second.next_back() orelse it.first.next_back();
        }

        pub usingnamespace ziter;
    };
}

test "chain" {
    const first_it = deref("ab");
    const second_it = deref("cd");
    const results = deref("abcd");

    try expectEqual(results, chain(first_it, second_it));
    try expectEqual(results, first_it.chain(second_it));
    try expectEqualReverse(results, chain(first_it, second_it));
    try expectEqualReverse(results, first_it.chain(second_it));
}

/// Creates an iterator that yields the items of both `a` and `b` when `next` is called. This
/// iterator ends when one of the iterator ends.
pub fn zip(a: anytype, b: anytype) Zip(
    Iterator(@TypeOf(a)),
    Iterator(@TypeOf(b)),
) {
    return .{ .a = iterator(a), .b = iterator(b) };
}

pub fn Zip(comptime _A: type, comptime _B: type) type {
    return struct {
        a: A,
        b: B,

        pub const A = _A;
        pub const B = _B;
        pub const Item = std.meta.Tuple(&.{ IteratorItem(A), IteratorItem(B) });

        pub fn next(it: *@This()) ?Item {
            return Item{
                it.a.next() orelse return null,
                it.b.next() orelse return null,
            };
        }

        pub usingnamespace ziter;
    };
}

test "zip" {
    const Item = std.meta.Tuple(&.{ u8, u8 });

    const a = deref("ab");
    const b = deref("cde");
    const results = deref(&[_]Item{
        .{ 'a', 'c' },
        .{ 'b', 'd' },
    });

    try expectEqual(results, zip(a, b));
    try expectEqual(results, a.zip(b));
}

/// Creates an iterator that puts seperators inbetween items. So for any iterator, this iterator
/// returns `item, sep, item, ..., sep, item, null`.
pub fn intersperse(
    _it: anytype,
    separator: IteratorItem(@TypeOf(_it)),
) Intersperse(Iterator(@TypeOf(_it))) {
    return .{ .it = iterator(_it).peekable(), .separator = separator };
}

pub fn Intersperse(comptime _It: type) type {
    return struct {
        it: Peekable(It),
        separator: Item,
        which: enum { item, separator } = .item,

        pub const It = _It;
        pub const Item = IteratorItem(It);

        pub fn next(it: *@This()) ?Item {
            switch (it.which) {
                .item => {
                    it.which = .separator;
                    return it.it.next();
                },
                .separator => {
                    _ = it.it.peek() orelse return null;
                    it.which = .item;
                    return it.separator;
                },
            }
        }

        pub usingnamespace ziter;
    };
}

test "intersperse" {
    const items = deref("abcd");
    const results = deref("a b c d");

    try expectEqual(results, intersperse(items, ' '));
    try expectEqual(results, items.intersperse(' '));
}

/// Creates an iterator that transforms the items from the child iterator using `func`. If the
/// child iterator can be iterated backwards, then so can this one.
pub fn map(_it: anytype, ctx: anytype, func: anytype) Map(
    Iterator(@TypeOf(_it)),
    @TypeOf(ctx),
    ReturnType(@TypeOf(func)),
) {
    return .{ .it = iterator(_it), .ctx = ctx, .func = func };
}

pub fn Map(comptime _It: type, comptime _Ctx: type, comptime _Item: type) type {
    return struct {
        it: It,
        ctx: Ctx,
        func: *const fn (Ctx, IteratorItem(It)) Item,

        pub const It = _It;
        pub const Ctx = _Ctx;
        pub const Item = _Item;

        pub fn next(it: *@This()) ?Item {
            const item = it.it.next() orelse return null;
            return it.func(it.ctx, item);
        }

        pub fn next_back(it: *@This()) ?Item {
            const item = it.it.next_back() orelse return null;
            return it.func(it.ctx, item);
        }

        pub usingnamespace ziter;
    };
}

test "map" {
    const add = struct {
        fn func(ctx: u8, item: u8) u8 {
            return ctx + item;
        }
    }.func;

    const items = deref("abcd");
    const results = deref("bcde");
    try expectEqual(results, map(items, @as(u8, 1), add));
    try expectEqual(results, items.map(@as(u8, 1), add));
    try expectEqualReverse(results, map(items, @as(u8, 1), add));
    try expectEqualReverse(results, items.map(@as(u8, 1), add));
}

/// Creates an iterator that only returns items where `predicate` returns `true`. If the child
/// iterator can be iterated backwards, then so can this one.
pub fn filter(_it: anytype, ctx: anytype, predicate: anytype) Filter(
    Iterator(@TypeOf(_it)),
    @TypeOf(ctx),
) {
    return .{ .it = iterator(_it), .ctx = ctx, .predicate = predicate };
}

pub fn Filter(comptime _It: type, comptime _Ctx: type) type {
    return struct {
        it: It,
        ctx: Ctx,
        predicate: *const fn (Ctx, Item) bool,

        pub const It = _It;
        pub const Ctx = _Ctx;
        pub const Item = IteratorItem(It);

        pub fn next(it: *@This()) ?Item {
            while (it.it.next()) |item| {
                if (it.predicate(it.ctx, item))
                    return item;
            }

            return null;
        }

        pub fn next_back(it: *@This()) ?Item {
            while (it.it.next_back()) |item| {
                if (it.predicate(it.ctx, item))
                    return item;
            }

            return null;
        }

        pub usingnamespace ziter;
    };
}

test "filter" {
    const filtering = struct {
        fn func(ctx: u8, item: u8) bool {
            return ctx != item;
        }
    }.func;

    const items = deref("abcd");
    const results = deref("acd");
    try expectEqual(results, filter(items, @as(u8, 'b'), filtering));
    try expectEqual(results, items.filter(@as(u8, 'b'), filtering));
    try expectEqualReverse(results, filter(items, @as(u8, 'b'), filtering));
    try expectEqualReverse(results, items.filter(@as(u8, 'b'), filtering));
}

/// Creates an iterator that only returns items where `func` does not return `null`. `func` is
/// allowed to transform the items into another type as well. If the child iterator can be iterated
/// backwards, then so can this one.
pub fn filter_map(_it: anytype, ctx: anytype, func: anytype) FilterMap(
    Iterator(@TypeOf(_it)),
    @TypeOf(ctx),
    @typeInfo(ReturnType(@TypeOf(func))).Optional.child,
) {
    return .{ .it = iterator(_it), .ctx = ctx, .func = func };
}

pub fn FilterMap(comptime _It: type, comptime _Ctx: type, comptime _Item: type) type {
    return struct {
        it: It,
        ctx: Ctx,
        func: *const fn (Ctx, IteratorItem(It)) ?Item,

        pub const It = _It;
        pub const Ctx = _Ctx;
        pub const Item = _Item;

        pub fn next(it: *@This()) ?Item {
            while (it.it.next()) |item| {
                if (it.func(it.ctx, item)) |result|
                    return result;
            }

            return null;
        }

        pub fn next_back(it: *@This()) ?Item {
            while (it.it.next_back()) |item| {
                if (it.func(it.ctx, item)) |result|
                    return result;
            }

            return null;
        }

        pub usingnamespace ziter;
    };
}

test "filter_map" {
    const Char = struct { c: u8 };
    const filtering = struct {
        fn func(ctx: u8, item: u8) ?Char {
            if (ctx != item)
                return Char{ .c = item + 1 };
            return null;
        }
    }.func;

    const items = deref("abcd");
    const results = deref(&[_]Char{
        .{ .c = 'b' },
        .{ .c = 'd' },
        .{ .c = 'e' },
    });
    try expectEqual(results, filter_map(items, @as(u8, 'b'), filtering));
    try expectEqual(results, items.filter_map(@as(u8, 'b'), filtering));
    try expectEqualReverse(results, filter_map(items, @as(u8, 'b'), filtering));
    try expectEqualReverse(results, items.filter_map(@as(u8, 'b'), filtering));
}

/// Creates an iterator that returns the items of the child as well as the index of that those
/// items.
pub fn enumerate(_it: anytype) Enumerate(Iterator(@TypeOf(_it))) {
    return .{ .it = iterator(_it) };
}

pub fn Enumerate(comptime _It: type) type {
    return struct {
        it: It,
        i: usize = 0,

        pub const It = _It;
        pub const Item = EnumerateItem(IteratorItem(It));

        pub fn next(it: *@This()) ?Item {
            const item = it.it.next() orelse return null;
            defer it.i += 1;
            return Item{ .i = it.i, .item = item };
        }

        pub usingnamespace ziter;
    };
}

pub fn EnumerateItem(comptime T: type) type {
    return struct {
        i: usize,
        item: T,
    };
}

test "enumerate" {
    const items = deref("abcd");

    const Item = EnumerateItem(u8);
    const results = deref(&[_]Item{
        .{ .i = 0, .item = 'a' },
        .{ .i = 1, .item = 'b' },
        .{ .i = 2, .item = 'c' },
        .{ .i = 3, .item = 'd' },
    });

    try expectEqual(results, enumerate(items));
    try expectEqual(results, items.enumerate());
}

/// Creates an iterator where the next item that been looked at without advancing the iterator.
/// This is also provided for backwards iteration of the child iterator can be iterated backwards.
pub fn peekable(_it: anytype) Peekable(Iterator(@TypeOf(_it))) {
    return .{ .it = iterator(_it) };
}

pub fn Peekable(comptime _It: type) type {
    return struct {
        it: It,
        peeked_front: ?Item = null,
        peeked_back: ?Item = null,

        pub const It = _It;
        pub const Item = IteratorItem(It);

        pub fn next(it: *@This()) ?Item {
            if (it.peeked_front) |peeked| {
                it.peeked_front = null;
                return peeked;
            }

            if (it.it.next()) |item|
                return item;

            if (it.peeked_back) |peeked| {
                it.peeked_back = null;
                return peeked;
            }

            return null;
        }

        pub fn next_back(it: *@This()) ?Item {
            if (it.peeked_back) |peeked| {
                it.peeked_back = null;
                return peeked;
            }

            if (it.it.next_back()) |item|
                return item;

            if (it.peeked_front) |peeked| {
                it.peeked_front = null;
                return peeked;
            }

            return null;
        }

        pub fn peek(it: *@This()) ?Item {
            if (it.peeked_front) |peeked|
                return peeked;

            if (it.it.next()) |item| {
                it.peeked_front = item;
                return it.peeked_front;
            }

            return it.peeked_back;
        }

        pub fn peek_back(it: *@This()) ?Item {
            if (it.peeked_back) |peeked|
                return peeked;

            if (it.it.next_back()) |item| {
                it.peeked_back = item;
                return it.peeked_back;
            }

            return it.peeked_front;
        }

        pub usingnamespace ziter;
    };
}

test "peekable" {
    const string = "abcd";
    const items = deref(string);

    var peekable1 = peekable(items);
    var peekable2 = items.peekable();

    for (string) |item| {
        try testing.expectEqual(@as(?u8, item), peekable1.peek());
        try testing.expectEqual(@as(?u8, item), peekable2.peek());
        try testing.expectEqual(@as(?u8, item), peekable1.peek());
        try testing.expectEqual(@as(?u8, item), peekable2.peek());
        try testing.expectEqual(@as(?u8, item), peekable1.next());
        try testing.expectEqual(@as(?u8, item), peekable2.next());
    }

    try testing.expectEqual(@as(?u8, null), peekable1.peek());
    try testing.expectEqual(@as(?u8, null), peekable2.peek());
    try testing.expectEqual(@as(?u8, null), peekable1.next());
    try testing.expectEqual(@as(?u8, null), peekable2.next());

    var peekable3 = peekable(items);
    var peekable4 = items.peekable();

    for (string) |item| {
        try testing.expectEqual(@as(?u8, item), peekable3.next());
        try testing.expectEqual(@as(?u8, item), peekable4.next());
    }

    try testing.expectEqual(@as(?u8, null), peekable3.next());
    try testing.expectEqual(@as(?u8, null), peekable4.next());

    var peekable5 = peekable(items);
    try testing.expectEqual(@as(?u8, string[0]), peekable5.peek());
    try testing.expectEqual(@as(?u8, string[3]), peekable5.peek_back());
    try testing.expectEqual(@as(?u8, string[0]), peekable5.next());
    try testing.expectEqual(@as(?u8, string[1]), peekable5.next());
    try testing.expectEqual(@as(?u8, string[2]), peekable5.peek());
    try testing.expectEqual(@as(?u8, string[3]), peekable5.peek_back());
    try testing.expectEqual(@as(?u8, string[3]), peekable5.next_back());
    try testing.expectEqual(@as(?u8, string[2]), peekable5.peek());
    try testing.expectEqual(@as(?u8, string[2]), peekable5.peek_back());
    try testing.expectEqual(@as(?u8, string[2]), peekable5.next_back());
    try testing.expectEqual(@as(?u8, null), peekable5.peek());
    try testing.expectEqual(@as(?u8, null), peekable5.peek_back());
}

/// Iterates the iterator, skipping items until `predicate` returns true. This iterator is then
/// returned. The iterator returned is `Peekable` as `skip_while` requires such an iterator to
/// function.
pub fn skip_while(_it: anytype, ctx: anytype, predicate: anytype) Peekable(Iterator(@TypeOf(_it))) {
    var it = peekable(_it);
    while (it.peek()) |item| {
        if (!predicate(ctx, item))
            break;
        _ = it.next();
    }

    return it;
}

test "skip_while" {
    const filtering = struct {
        fn func(ctx: u8, item: u8) bool {
            return ctx == item;
        }
    }.func;

    const items = deref("aaaabcd");
    const results = deref("bcd");
    try expectEqual(results, skip_while(items, @as(u8, 'a'), filtering));
    try expectEqual(results, items.skip_while(@as(u8, 'a'), filtering));
}

/// Creates an iterator that yields items while `predicate` on those items returns `true`. Once
/// `predicate` returns `false` on an item, the iterator ends.
pub fn take_while(_it: anytype, ctx: anytype, predicate: anytype) TakeWhile(
    Iterator(@TypeOf(_it)),
    @TypeOf(ctx),
) {
    return .{ .it = iterator(_it), .ctx = ctx, .predicate = predicate };
}

pub fn TakeWhile(comptime _It: type, comptime _Ctx: type) type {
    return struct {
        it: It,
        ctx: Ctx,
        predicate: *const fn (Ctx, Item) bool,
        done: bool = false,

        pub const It = _It;
        pub const Ctx = _Ctx;
        pub const Item = IteratorItem(It);

        pub fn next(it: *@This()) ?Item {
            // !it.done and it.it.next() and it.predicate(item)
            if (!it.done) if (it.it.next()) |item| if (it.predicate(it.ctx, item)) {
                return item;
            };

            it.done = true;
            return null;
        }

        pub usingnamespace ziter;
    };
}

test "take_while" {
    const filtering = struct {
        fn func(ctx: u8, item: u8) bool {
            return item == ctx;
        }
    }.func;

    const items = deref("aaaabcd");
    const results = deref("aaaa");
    try expectEqual(results, take_while(items, @as(u8, 'a'), filtering));
    try expectEqual(results, items.take_while(@as(u8, 'a'), filtering));
}

/// Creates an iterator that yields items while `func` does not return `null`. `func` is allowed
/// to transform the items to a new type. Once `func` returns `null` on an item, the iterator ends.
pub fn map_while(_it: anytype, ctx: anytype, func: anytype) MapWhile(
    Iterator(@TypeOf(_it)),
    @TypeOf(ctx),
    @typeInfo(ReturnType(@TypeOf(func))).Optional.child,
) {
    return .{ .it = iterator(_it), .ctx = ctx, .func = func };
}

pub fn MapWhile(comptime _It: type, comptime _Ctx: type, comptime _Item: type) type {
    return struct {
        it: It,
        ctx: Ctx,
        func: *const fn (Ctx, IteratorItem(It)) ?Item,
        done: bool = false,

        pub const It = _It;
        pub const Ctx = _Ctx;
        pub const Item = _Item;

        pub fn next(it: *@This()) ?Item {
            // !it.done and it.it.next() and it.func(item)
            if (!it.done) if (it.it.next()) |item| if (it.func(it.ctx, item)) |result| {
                return result;
            };

            it.done = true;
            return null;
        }

        pub usingnamespace ziter;
    };
}

test "map_while" {
    const Char = struct { c: u8 };
    const filtering = struct {
        fn func(ctx: u8, item: u8) ?Char {
            if (ctx == item)
                return Char{ .c = item + 1 };
            return null;
        }
    }.func;

    const items = deref("aaaabcd");
    const results = deref(&[_]Char{
        .{ .c = 'b' },
        .{ .c = 'b' },
        .{ .c = 'b' },
        .{ .c = 'b' },
    });
    try expectEqual(results, map_while(items, @as(u8, 'a'), filtering));
    try expectEqual(results, items.map_while(@as(u8, 'a'), filtering));
}

/// Skips over the first `n` items in the iterator and returns it.
pub fn skip(_it: anytype, n: usize) Iterator(@TypeOf(_it)) {
    var i: usize = 0;
    var it = iterator(_it);
    while (i < n) : (i += 1)
        _ = it.next() orelse break;

    return it;
}

test "skip" {
    const items = deref("aaaabcd");
    const results = deref("abcd");
    try expectEqual(results, skip(items, 3));
    try expectEqual(results, items.skip(3));
}

/// Creates an iterator that yields the first `n` items. Once those items have been yielded, the
/// iterator ends.
pub fn take(_it: anytype, n: usize) Take(Iterator(@TypeOf(_it))) {
    return .{ .it = iterator(_it), .n = n };
}

pub fn Take(comptime _It: type) type {
    return struct {
        it: It,
        n: usize,

        pub const It = _It;
        pub const Item = IteratorItem(It);

        pub fn next(it: *@This()) ?Item {
            if (it.n == 0)
                return null;

            it.n -= 1;
            return it.it.next();
        }

        pub usingnamespace ziter;
    };
}

test "take" {
    const items = deref("aaaabcd");
    const results = deref("aaaab");
    try expectEqual(results, take(items, 5));
    try expectEqual(results, items.take(5));
}

/// A wrapper function around `it.map(...).flatten()`.
pub fn flat_map(_it: anytype, ctx: anytype, func: anytype) Flatten(Map(
    Iterator(@TypeOf(_it)),
    @TypeOf(ctx),
    ReturnType(@TypeOf(func)),
)) {
    return map(_it, ctx, func).flatten();
}

test "flat_map" {
    const to_optional = struct {
        fn func(_: void, item: u8) ?u8 {
            return item;
        }
    }.func;
    try expectEqual(
        deref("abcd"),
        deref("abcd").flat_map({}, to_optional),
    );
    try expectEqual(
        deref("abcd"),
        flat_map(deref("abcd"), {}, to_optional),
    );
}

/// Given an iterator that returns items that can be iterated, this function will create an
/// iterator that iterates the items of those items. For example, if you have an iterator that
/// yields `"abc", "ab", "a"`, calling `flatten` on it will create a new iterator that yield
/// `'a', 'b', 'c', 'a', 'b', 'a'`. Note that this is not exactly how iterating over slices work.
/// see: `slice` and `deref`.
pub fn flatten(_it: anytype) Flatten(Iterator(@TypeOf(_it))) {
    const It = Iterator(@TypeOf(_it));
    var it = iterator(_it);
    const first_item: ?IteratorItem(It) = it.next();
    const last_item: ?IteratorItem(It) = if (@hasDecl(It, "next_back")) it.next_back() else null;
    return .{
        .it = it,
        .front_it = if (first_item) |item| iterator(item) else null,
        .back_it = if (last_item) |item| iterator(item) else null,
    };
}

pub fn Flatten(comptime _It: type) type {
    return struct {
        it: It,
        front_it: ?ItemIt,
        back_it: ?ItemIt,

        pub const It = _It;
        pub const ItemIt = Iterator(IteratorItem(It));
        pub const Item = IteratorItem(ItemIt);

        pub fn next(it: *@This()) ?Item {
            while (it.front_it) |*item_it| {
                if (item_it.next()) |result|
                    return result;

                it.front_it = if (it.it.next()) |item| iterator(item) else null;
            }
            while (it.back_it) |*item_it| {
                if (item_it.next()) |result|
                    return result;

                it.back_it = null;
            }

            return null;
        }

        pub fn next_back(it: *@This()) ?Item {
            while (it.back_it) |*item_it| {
                if (item_it.next_back()) |result|
                    return result;

                it.back_it = if (it.it.next_back()) |item| iterator(item) else null;
            }
            while (it.front_it) |*item_it| {
                if (item_it.next_back()) |result|
                    return result;

                it.front_it = null;
            }

            return null;
        }

        pub usingnamespace ziter;
    };
}

test "flatten" {
    var i: u64 = 0;
    while (i < 100) : (i += 1) {
        var random = std.rand.DefaultPrng.init(i);
        try expectEqualRandomOrder(
            random.random(),
            deref("abcd"),
            deref(&[_]?u8{ 'a', null, 'b', null, 'c', 'd', null })
                .flatten(),
        );
        try expectEqualRandomOrder(
            random.random(),
            deref("abcd"),
            flatten(deref(&[_]?u8{ 'a', null, 'b', null, 'c', 'd', null })),
        );
        try expectEqualRandomOrder(
            random.random(),
            deref("abcd"),
            flatten(&[_][2]u8{ "ab".*, "cd".* })
                .deref(),
        );
        try expectEqualRandomOrder(
            random.random(),
            deref("abcd"),
            flatten(&[_][2]u8{ "ab".*, "cd".* })
                .deref(),
        );
    }
}

/// Creates a new iterator that yields the same items as the child iterator, but also calls `func`
/// on each item it yields.
pub fn inspect(_it: anytype, ctx: anytype, func: anytype) Inspect(
    Iterator(@TypeOf(_it)),
    @TypeOf(ctx),
) {
    return .{ .it = iterator(_it), .ctx = ctx, .func = func };
}

pub fn Inspect(comptime _It: type, comptime _Ctx: type) type {
    return struct {
        it: It,
        ctx: Ctx,
        func: *const fn (Ctx, Item) void,

        pub const It = _It;
        pub const Ctx = _Ctx;
        pub const Item = IteratorItem(It);

        pub fn next(it: *@This()) ?Item {
            const item = it.it.next() orelse return null;
            it.func(it.ctx, item);
            return item;
        }

        pub fn next_back(it: *@This()) ?Item {
            const item = it.it.next_back() orelse return null;
            it.func(it.ctx, item);
            return item;
        }

        pub usingnamespace ziter;
    };
}

test "inspect" {
    const append = struct {
        fn append(list: *std.ArrayList(u8), item: u8) void {
            list.append(item) catch {};
        }
    }.append;

    var list = std.ArrayList(u8).init(testing.allocator);
    defer list.deinit();

    const items = deref("abcd");

    try expectEqual(items, items.inspect(&list, append));
    try expectEqual(items, inspect(items, &list, append));
    try expectEqualReverse(items, items.inspect(&list, append));
    try expectEqualReverse(items, inspect(items, &list, append));
    try testing.expectEqualStrings("abcdabcddcbadcba", list.items);
}

/// Takes all items in an iterator, appends them to a container and returns that container. The
/// caller owns the container once returned. The caller is responsible for passing in the initial
/// state of the container. For `std.ArrayList(u8)` you would pass
/// `std.ArrayList(u8).init(allocator)` to the `init` argument.
/// `collect` will `deinit` the container if an error occures.
pub fn collect(_it: anytype, init: anytype) !@TypeOf(init) {
    var container = init;
    errdefer container.deinit();

    try collect_into(_it, &container);
    return container;
}

test "collect" {
    const S = struct {
        a: u8,
        b: u8,
    };

    const results = [_]S{
        .{ .a = 1, .b = 2 },
        .{ .a = 3, .b = 4 },
        .{ .a = 5, .b = 6 },
        .{ .a = 7, .b = 8 },
    };
    const items = deref(&results);

    var list1 = try collect(items, std.ArrayList(S).init(testing.allocator));
    defer list1.deinit();
    try testing.expectEqualSlices(S, &results, list1.items);

    var list2 = try items.collect(std.ArrayList(S).init(testing.allocator));
    defer list2.deinit();
    try testing.expectEqualSlices(S, &results, list2.items);
}

/// Same as `collect` but for `Unmanaged` containers such as `ArrayListUnmanaged`.
pub fn collect_unmanaged(
    _it: anytype,
    allocator: std.mem.Allocator,
    init: anytype,
) !@TypeOf(init) {
    var container = init;
    errdefer container.deinit(allocator);

    try collect_into_unmanaged(_it, allocator, &container);
    return container;
}

test "collect_unmanaged" {
    const S = struct {
        a: u8,
        b: u8,
    };

    const results = [_]S{
        .{ .a = 1, .b = 2 },
        .{ .a = 3, .b = 4 },
        .{ .a = 5, .b = 6 },
        .{ .a = 7, .b = 8 },
    };
    const items = deref(&results);

    var list1 = try collect_unmanaged(items, testing.allocator, std.ArrayListUnmanaged(S){});
    defer list1.deinit(testing.allocator);
    try testing.expectEqualSlices(S, &results, list1.items);

    var list2 = try items.collect_unmanaged(testing.allocator, std.ArrayListUnmanaged(S){});
    defer list2.deinit(testing.allocator);
    try testing.expectEqualSlices(S, &results, list2.items);

    var list3 = try collect_unmanaged(items, testing.allocator, std.MultiArrayList(S){});
    defer list3.deinit(testing.allocator);
    try testing.expectEqualSlices(u8, &[_]u8{ 1, 3, 5, 7 }, list3.items(.a));
    try testing.expectEqualSlices(u8, &[_]u8{ 2, 4, 6, 8 }, list3.items(.b));

    var list4 = try items.collect_unmanaged(testing.allocator, std.MultiArrayList(S){});
    defer list4.deinit(testing.allocator);
    try testing.expectEqualSlices(u8, &[_]u8{ 1, 3, 5, 7 }, list4.items(.a));
    try testing.expectEqualSlices(u8, &[_]u8{ 2, 4, 6, 8 }, list4.items(.b));

    var list5 = try collect_unmanaged(items, testing.allocator, std.SegmentedList(S, 0){});
    defer list5.deinit(testing.allocator);
    try expectEqual(items, deref(list5.iterator(0)));

    var list6 = try items.collect_unmanaged(testing.allocator, std.SegmentedList(S, 0){});
    defer list6.deinit(testing.allocator);
    try expectEqual(items, deref(list6.iterator(0)));
}

/// Same as `collect` but for non allocating containers such as `std.BoundArray`. This function
/// does not try to `deinit` the container when an error occures.
pub fn collect_no_allocator(
    _it: anytype,
    init: anytype,
) !@TypeOf(init) {
    var container = init;
    try collect_into(_it, &container);
    return container;
}

test "collect_no_allocator" {
    const S = struct {
        a: u8,
        b: u8,
    };

    const results = [_]S{
        .{ .a = 1, .b = 2 },
        .{ .a = 3, .b = 4 },
        .{ .a = 5, .b = 6 },
        .{ .a = 7, .b = 8 },
    };
    const items = deref(&results);

    var list1 = try collect_no_allocator(items, std.BoundedArray(S, 16){});
    try testing.expectEqualSlices(S, &results, list1.slice());

    var list2 = try items.collect_no_allocator(std.BoundedArray(S, 16){});
    try testing.expectEqualSlices(S, &results, list2.slice());
}

/// Takes all items in an iterator and appends them to a container. The caller needs to pass a
/// pointer to a container they own.
pub fn collect_into(_it: anytype, container: anytype) !void {
    var it = iterator(_it);
    while (it.next()) |item|
        try container.append(item);
}

test "collect_into" {
    const S = struct {
        a: u8,
        b: u8,
    };

    const results = [_]S{
        .{ .a = 1, .b = 2 },
        .{ .a = 3, .b = 4 },
        .{ .a = 5, .b = 6 },
        .{ .a = 7, .b = 8 },
    };
    const items = deref(&results);

    var list1 = std.ArrayList(S).init(testing.allocator);
    defer list1.deinit();

    try collect_into(items, &list1);
    try testing.expectEqualSlices(S, &results, list1.items);

    try items.collect_into(&list1);
    try testing.expectEqualSlices(S, &(results ** 2), list1.items);

    var list2 = std.BoundedArray(S, 16){};

    try collect_into(items, &list2);
    try testing.expectEqualSlices(S, &results, list2.slice());

    try items.collect_into(&list2);
    try testing.expectEqualSlices(S, &(results ** 2), list2.slice());
}

/// Same as `collect_into` but for `Unmanaged` containers such as `ArrayListUnmanged`.
pub fn collect_into_unmanaged(
    _it: anytype,
    allocator: std.mem.Allocator,
    container: anytype,
) !void {
    var it = iterator(_it);
    while (it.next()) |item|
        try container.append(allocator, item);
}

test "collect_into_unmanaged" {
    const S = struct {
        a: u8,
        b: u8,
    };

    const results = [_]S{
        .{ .a = 1, .b = 2 },
        .{ .a = 3, .b = 4 },
        .{ .a = 5, .b = 6 },
        .{ .a = 7, .b = 8 },
    };
    const items = deref(&results);

    var list1 = std.ArrayListUnmanaged(S){};
    defer list1.deinit(testing.allocator);

    try collect_into_unmanaged(items, testing.allocator, &list1);
    try testing.expectEqualSlices(S, &results, list1.items);

    try items.collect_into_unmanaged(testing.allocator, &list1);
    try testing.expectEqualSlices(S, &(results ** 2), list1.items);

    var list2 = std.MultiArrayList(S){};
    defer list2.deinit(testing.allocator);

    try collect_into_unmanaged(items, testing.allocator, &list2);
    try testing.expectEqualSlices(u8, &[_]u8{ 1, 3, 5, 7 }, list2.items(.a));
    try testing.expectEqualSlices(u8, &[_]u8{ 2, 4, 6, 8 }, list2.items(.b));

    try items.collect_into_unmanaged(testing.allocator, &list2);
    try testing.expectEqualSlices(u8, &([_]u8{ 1, 3, 5, 7 } ** 2), list2.items(.a));
    try testing.expectEqualSlices(u8, &([_]u8{ 2, 4, 6, 8 } ** 2), list2.items(.b));
}

/// Same as `fold` but `func` is allowed to fail. If it fails, the `fold` will fail as well.
pub fn try_fold(_it: anytype, init: anytype, ctx: anytype, func: anytype) !@TypeOf(init) {
    var res = init;
    var it = iterator(_it);
    while (it.next()) |item|
        res = try func(ctx, res, item);

    return res;
}

test "try_fold" {
    const add = struct {
        fn add(extra: u16, acc: u16, item: u8) !u16 {
            return try math.add(u16, extra, try math.add(u16, acc, item));
        }
    }.add;
    try testing.expectEqual(
        @as(anyerror!u16, '0' + '1' + '2' + '3' + 4),
        try_fold(deref("0123"), @as(u16, 0), @as(u16, 1), add),
    );
    try testing.expectEqual(
        @as(anyerror!u16, '0' + '1' + '2' + '3' + 4),
        deref("0123").try_fold(@as(u16, 0), @as(u16, 1), add),
    );
    try testing.expectEqual(
        @as(anyerror!u16, error.Overflow),
        try_fold(deref("0123"), @as(u16, 0), @as(u16, 40000), add),
    );
    try testing.expectEqual(
        @as(anyerror!u16, error.Overflow),
        deref("0123").try_fold(@as(u16, 0), @as(u16, 40000), add),
    );
}

/// Iterates over all items in an iterator and calls `acc = func(ctx, acc, item)` on each of
/// them. `acc` starts out as the value of `init` and is then changed on each iteration. This
/// function is useful for implementing things like `sum`, which is
/// `sum = fold(it, 0, {}, fn(_, acc, item) T { return acc + item; })`
/// Note that `sum` is already implemented in this library. See `sum`
pub fn fold(_it: anytype, init: anytype, ctx: anytype, func: anytype) @TypeOf(init) {
    var acc = init;
    var it = iterator(_it);
    while (it.next()) |item|
        acc = func(ctx, acc, item);

    return acc;
}

test "fold" {
    const add = struct {
        fn add(extra: u16, acc: u16, item: u8) u16 {
            return acc + item + extra;
        }
    }.add;
    try testing.expectEqual(
        @as(u16, '0' + '1' + '2' + '3' + 4),
        fold(deref("0123"), @as(u16, 0), @as(u16, 1), add),
    );
    try testing.expectEqual(
        @as(u16, '0' + '1' + '2' + '3' + 4),
        deref("0123").fold(@as(u16, 0), @as(u16, 1), add),
    );
}

/// Same as `fold`, but the first item of the iterator is passed as the `init` argument. If the
/// iterator is empty, then `null` is returned.
pub fn reduce(_it: anytype, ctx: anytype, func: anytype) ?IteratorItem(@TypeOf(_it)) {
    var it = iterator(_it);
    const init = it.next() orelse return null;
    return fold(it, init, ctx, func);
}

test "reduce" {
    const S = struct {
        fn add(extra: u16, acc: u16, item: u16) u16 {
            return acc + item + extra;
        }
        fn to_u16(_: void, item: u8) u16 {
            return item;
        }
    };
    try testing.expectEqual(
        @as(?u16, '0' + '1' + '2' + '3' + 3),
        reduce(deref("0123").map({}, S.to_u16), @as(u16, 1), S.add),
    );
    try testing.expectEqual(
        @as(?u16, '0' + '1' + '2' + '3' + 3),
        deref("0123").map({}, S.to_u16).reduce(@as(u16, 1), S.add),
    );
    try testing.expectEqual(
        @as(?u16, null),
        reduce(deref("").map({}, S.to_u16), @as(u16, 1), S.add),
    );
    try testing.expectEqual(
        @as(?u16, null),
        deref("").map({}, S.to_u16).reduce(@as(u16, 1), S.add),
    );
}

/// Same as `reduce` but `func` is allowed to fail. If it fails, the `reduce` will fail as well.
pub fn try_reduce(_it: anytype, ctx: anytype, func: anytype) !?IteratorItem(@TypeOf(_it)) {
    var it = iterator(_it);
    const init = it.next() orelse return null;
    return try try_fold(it, init, ctx, func);
}

test "try_reduce" {
    const S = struct {
        fn add(extra: u16, acc: u16, item: u16) !u16 {
            return try math.add(u16, extra, try math.add(u16, acc, item));
        }
        fn to_u16(_: void, item: u8) u16 {
            return item;
        }
    };
    try testing.expectEqual(
        @as(anyerror!?u16, '0' + '1' + '2' + '3' + 3),
        try_reduce(deref("0123").map({}, S.to_u16), @as(u16, 1), S.add),
    );
    try testing.expectEqual(
        @as(anyerror!?u16, '0' + '1' + '2' + '3' + 3),
        deref("0123").map({}, S.to_u16).try_reduce(@as(u16, 1), S.add),
    );
    try testing.expectEqual(
        @as(anyerror!?u16, null),
        try_reduce(deref("").map({}, S.to_u16), @as(u16, 1), S.add),
    );
    try testing.expectEqual(
        @as(anyerror!?u16, null),
        deref("").map({}, S.to_u16).try_reduce(@as(u16, 1), S.add),
    );
    try testing.expectEqual(
        @as(anyerror!?u16, error.Overflow),
        try_reduce(deref("0123").map({}, S.to_u16), @as(u16, 40000), S.add),
    );
    try testing.expectEqual(
        @as(anyerror!?u16, error.Overflow),
        deref("0123").map({}, S.to_u16).try_reduce(@as(u16, 40000), S.add),
    );
}

/// Iterators the items of an iterator and checks if `predicate` returns `true` for all of them.
/// If so, `true` is returned. If a call to `predicate` returns `false`, `all` returns `false`
/// without iterating over the rest of the items.
pub fn all(_it: anytype, ctx: anytype, predicate: anytype) bool {
    var it = iterator(_it);
    while (it.next()) |item| {
        if (!predicate(ctx, item))
            return false;
    }

    return true;
}

test "all" {
    try testing.expect(all(deref("abcd"), {}, void_ctx(std.ascii.isAlphabetic)));
    try testing.expect(deref("abcd").all({}, void_ctx(std.ascii.isAlphabetic)));
    try testing.expect(!all(deref("1bcd"), {}, void_ctx(std.ascii.isAlphabetic)));
    try testing.expect(!deref("1bcd").all({}, void_ctx(std.ascii.isAlphabetic)));
}

/// Iterators the items of an iterator and checks if `predicate` returns `false` for all of them.
/// If so, `true` is returned. If a call to `predicate` returns `true`, `none` returns `false`
/// without iterating over the rest of the items.
pub fn none(_it: anytype, ctx: anytype, predicate: anytype) bool {
    var it = iterator(_it);
    while (it.next()) |item| {
        if (predicate(ctx, item))
            return false;
    }

    return true;
}

test "none" {
    try testing.expect(!none(deref("abcd"), {}, void_ctx(std.ascii.isAlphabetic)));
    try testing.expect(!deref("abcd").none({}, void_ctx(std.ascii.isAlphabetic)));
    try testing.expect(!none(deref("1bcd"), {}, void_ctx(std.ascii.isAlphabetic)));
    try testing.expect(!deref("1bcd").none({}, void_ctx(std.ascii.isAlphabetic)));
    try testing.expect(none(deref("1234"), {}, void_ctx(std.ascii.isAlphabetic)));
    try testing.expect(deref("1234").none({}, void_ctx(std.ascii.isAlphabetic)));
}

/// Iterators the items of an iterator and checks if `predicate` returns `true` for any of them.
/// If not, `false` is returned. If a call to `predicate` returns `true`, `any` returns `true`
/// without iterating over the rest of the items.
pub fn any(_it: anytype, ctx: anytype, predicate: anytype) bool {
    return find(_it, ctx, predicate) != null;
}

test "any" {
    try testing.expect(!any(deref("abcd"), {}, void_ctx(std.ascii.isDigit)));
    try testing.expect(!deref("abcd").any({}, void_ctx(std.ascii.isDigit)));
    try testing.expect(any(deref("1bcd"), {}, void_ctx(std.ascii.isDigit)));
    try testing.expect(deref("1bcd").any({}, void_ctx(std.ascii.isDigit)));
}

/// Iterators the items of an iterator and returns the first item where `predicate` returns `true`.
/// `find` will only iterate up until it finds this item. If no item is found, `null` is returned.
pub fn find(_it: anytype, ctx: anytype, predicate: anytype) ?IteratorItem(@TypeOf(_it)) {
    var it = iterator(_it);
    while (it.next()) |item| {
        if (predicate(ctx, item))
            return item;
    }

    return null;
}

test "find" {
    try testing.expectEqual(@as(?u8, null), find(deref("abcd"), {}, void_ctx(std.ascii.isDigit)));
    try testing.expectEqual(@as(?u8, null), deref("abcd").find({}, void_ctx(std.ascii.isDigit)));
    try testing.expectEqual(@as(?u8, '1'), find(deref("1bcd"), {}, void_ctx(std.ascii.isDigit)));
    try testing.expectEqual(@as(?u8, '1'), deref("1bcd").find({}, void_ctx(std.ascii.isDigit)));
}

/// Same as `find`, but instead of returning the item found, `position` will return the index of
/// that item.
pub fn position(_it: anytype, ctx: anytype, predicate: anytype) ?usize {
    var i: usize = 0;
    var it = iterator(_it);
    while (it.next()) |item| : (i += 1) {
        if (predicate(ctx, item))
            return i;
    }

    return null;
}

test "position" {
    try testing.expectEqual(@as(?usize, null), position(deref("abcd"), {}, void_ctx(std.ascii.isDigit)));
    try testing.expectEqual(@as(?usize, null), deref("abcd").position({}, void_ctx(std.ascii.isDigit)));
    try testing.expectEqual(@as(?usize, 0), position(deref("1bcd"), {}, void_ctx(std.ascii.isDigit)));
    try testing.expectEqual(@as(?usize, 0), deref("1bcd").position({}, void_ctx(std.ascii.isDigit)));
}

/// Iterates an iterator to find the largest item in it. `null` is returned if the iterator is
/// empty.
pub fn max(_it: anytype) ?IteratorItem(@TypeOf(_it)) {
    var it = iterator(_it);
    var best = it.next() orelse return null;
    while (it.next()) |item|
        best = math.max(best, item);

    return best;
}

test "max" {
    try testing.expectEqual(@as(?u8, 'g'), max(deref("abcdefg")));
    try testing.expectEqual(@as(?u8, 'g'), deref("abcdefg").max());
    try testing.expectEqual(@as(?u8, 'g'), max(deref("gabcdef")));
    try testing.expectEqual(@as(?u8, 'g'), deref("gabcdef").max());
    try testing.expectEqual(@as(?u8, 'g'), max(deref("g")));
    try testing.expectEqual(@as(?u8, 'g'), deref("g").max());
    try testing.expectEqual(@as(?u8, null), max(deref("")));
    try testing.expectEqual(@as(?u8, null), deref("").max());
}

/// Iterates an iterator to find the smallest item in it. `null` is returned if the iterator is
/// empty.
pub fn min(_it: anytype) ?IteratorItem(@TypeOf(_it)) {
    var it = iterator(_it);
    var best = it.next() orelse return null;
    while (it.next()) |item|
        best = math.min(best, item);

    return best;
}

test "min" {
    try testing.expectEqual(@as(?u8, 'a'), min(deref("abcdefg")));
    try testing.expectEqual(@as(?u8, 'a'), deref("abcdefg").min());
    try testing.expectEqual(@as(?u8, 'a'), min(deref("gabcdef")));
    try testing.expectEqual(@as(?u8, 'a'), deref("gabcdef").min());
    try testing.expectEqual(@as(?u8, 'g'), min(deref("g")));
    try testing.expectEqual(@as(?u8, 'g'), deref("g").min());
    try testing.expectEqual(@as(?u8, null), min(deref("")));
    try testing.expectEqual(@as(?u8, null), deref("").min());
}

/// Creates an iterator that iterates in reverse order from the iterator passed in. This only works
/// if the iterator can actually be iterated backwards.
pub fn reverse(_it: anytype) Reverse(Iterator(@TypeOf(_it))) {
    return .{ .it = iterator(_it) };
}

pub fn Reverse(comptime _It: type) type {
    return struct {
        it: It,

        pub const It = _It;
        pub const Item = IteratorItem(It);

        pub fn next(it: *@This()) ?Item {
            return it.it.next_back();
        }

        pub fn next_back(it: *@This()) ?Item {
            return it.it.next();
        }

        pub usingnamespace ziter;
    };
}

test "reverse" {
    try expectEqual(deref("abcd"), deref("dcba").reverse());
    try expectEqual(deref("abcd"), reverse(deref("dcba")));
    try expectEqualReverse(deref("abcd"), deref("dcba").reverse());
    try expectEqualReverse(deref("abcd"), reverse(deref("dcba")));
}

/// Creates an iterator that dereferences all items of the child iterator. If the child iterator
/// can be iterated backwards, then so can this one.
pub fn deref(_it: anytype) Map(
    Iterator(@TypeOf(_it)),
    void,
    std.meta.Child(IteratorItem(@TypeOf(_it))),
) {
    const Item = IteratorItem(@TypeOf(_it));
    return map(_it, {}, struct {
        fn func(_: void, ptr: Item) std.meta.Child(Item) {
            return ptr.*;
        }
    }.func);
}

test "deref" {
    const items = "abcd";
    var deref1 = deref(items);
    var deref2 = slice(items).deref();

    for (items) |item| {
        try testing.expectEqual(@as(?u8, item), deref1.next());
        try testing.expectEqual(@as(?u8, item), deref2.next());
    }

    try testing.expectEqual(@as(?u8, null), deref1.next());
    try testing.expectEqual(@as(?u8, null), deref2.next());
}

/// Creates an iterator that never ends. Once the child iterator is empty, it is reset and
/// iterated again. If the child iterator can be iterated backwards, then so can this one.
pub fn cycle(_it: anytype) Cycle(Iterator(@TypeOf(_it))) {
    const it = iterator(_it);
    return .{ .reset = it, .front_it = it, .back_it = it };
}

pub fn Cycle(comptime _It: type) type {
    return struct {
        reset: It,
        front_it: It,
        back_it: It,

        pub const Item = IteratorItem(It);
        pub const It = _It;

        pub fn next(it: *@This()) ?Item {
            if (it.front_it.next()) |item|
                return item;

            it.front_it = it.reset;
            return it.front_it.next();
        }

        pub fn next_back(it: *@This()) ?Item {
            if (it.back_it.next_back()) |item|
                return item;

            it.back_it = it.reset;
            return it.back_it.next_back();
        }

        pub usingnamespace ziter;
    };
}

test "cycle" {
    try expectEqual(deref("abababa"), deref("ab").cycle().take(7));
    try expectEqual(deref("abababa"), take(cycle(deref("ab")), 7));
    try expectEqual(deref("cdcdcdc"), deref("dc").cycle().reverse().take(7));
    try expectEqual(deref("cdcdcdc"), take(reverse(cycle(deref("dc"))), 7));
}

/// Creates an iterator that deduplicates repeated items. An iterator that yields
/// `0, 1, 1, 2, 2, 0` would, when wrapped by dedup, yield `0, 1, 2, 0`.
pub fn dedup(_it: anytype, ctx: anytype, eq: *const fn (
    @TypeOf(ctx),
    IteratorItem(@TypeOf(_it)),
    IteratorItem(@TypeOf(_it)),
) bool) Dedup(Iterator(@TypeOf(_it)), @TypeOf(ctx)) {
    return .{ .it = iterator(_it), .ctx = ctx, .eql = eq };
}

pub fn Dedup(comptime _It: type, comptime _Ctx: type) type {
    return struct {
        it: It,
        ctx: Ctx,
        eql: *const fn (Ctx, Item, Item) bool,
        prev: ?Item = null,

        pub const It = _It;
        pub const Ctx = _Ctx;
        pub const Item = IteratorItem(It);

        pub fn next(it: *@This()) ?Item {
            const prev = it.prev orelse {
                it.prev = it.it.next();
                return it.prev;
            };

            while (it.it.next()) |item| {
                if (!it.eql(it.ctx, prev, item)) {
                    it.prev = item;
                    return item;
                }
            }

            return null;
        }
    };
}

test "dedup" {
    const eq = struct {
        fn eq(_: void, a: u8, b: u8) bool {
            return a == b;
        }
    }.eq;

    try expectEqual(deref("abcd"), dedup(deref("aabccdd"), {}, eq));
    try expectEqual(deref("abcd"), deref("aabccdd").dedup({}, eq));
    try expectEqual(deref("a"), dedup(deref("aaaaa"), {}, eq));
    try expectEqual(deref("a"), deref("aaaaa").dedup({}, eq));
    try expectEqual(deref("a"), dedup(deref("a"), {}, eq));
    try expectEqual(deref("a"), deref("a").dedup({}, eq));
    try expectEqual(deref("aba"), dedup(deref("aabbaa"), {}, eq));
    try expectEqual(deref("aba"), deref("aabbaa").dedup({}, eq));
}

pub fn is_empty(_it: anytype) bool {
    var it = iterator(_it);
    return it.next() == null;
}

test "is_empty" {
    try testing.expect(is_empty(""));
    try testing.expect(!is_empty("a"));
}

/// Calculates the sum of all the items in the iterator. If the iterator is empty, `0` is returned.
pub fn sum(_it: anytype, comptime T: type) T {
    var it = iterator(_it);
    var res: T = 0;
    while (it.next()) |item|
        res += item;

    return res;
}

test "sum" {
    try testing.expectEqual(@as(u16, 'a' + 'b' + 'c'), deref("abc").sum(u16));
    try testing.expectEqual(@as(u16, 'a' + 'b' + 'c'), sum(deref("abc"), u16));
    try testing.expectEqual(@as(u16, 0), deref("").sum(u16));
    try testing.expectEqual(@as(u16, 0), sum(deref(""), u16));
}

/// Calculates the product of all the items in the iterator. If the iterator is empty, `1` is
/// returned.
pub fn product(_it: anytype, comptime T: type) T {
    var it = iterator(_it);
    var res: T = 1;
    while (it.next()) |item|
        res *= item;

    return res;
}

test "product" {
    try testing.expectEqual(@as(u32, 'a' * 'b' * 'c'), deref("abc").product(u32));
    try testing.expectEqual(@as(u32, 'a' * 'b' * 'c'), product(deref("abc"), u32));
    try testing.expectEqual(@as(u32, 1), deref("").product(u32));
    try testing.expectEqual(@as(u32, 1), product(deref(""), u32));
}

/// Compares two iterators lexicographically, returning the `std.math.Order` of the comparison.
pub fn order(_lhs: anytype, _rhs: anytype) math.Order {
    var lhs = iterator(_lhs);
    var rhs = iterator(_rhs);

    while (true) {
        const lhs_item = lhs.next();
        const rhs_item = rhs.next();
        if (lhs_item == null and rhs_item == null)
            return .eq;
        if (lhs_item == null)
            return .lt;
        if (rhs_item == null)
            return .gt;

        switch (math.order(lhs_item.?, rhs_item.?)) {
            .eq => {},
            .lt => return .lt,
            .gt => return .gt,
        }
    }
}

test "order" {
    try testing.expect(order(deref("abcd"), deref("bee")) == .lt);
    try testing.expect(order(deref("bee"), deref("abcd")) == .gt);
    try testing.expect(order(deref("abc"), deref("abc")) == .eq);
    try testing.expect(order(deref("abc"), deref("abc0")) == .lt);
    try testing.expect(order(deref("abc0"), deref("abc")) == .gt);
    try testing.expect(order(deref(""), deref("")) == .eq);
    try testing.expect(order(deref(""), deref("a")) == .lt);
    try testing.expect(order(deref("a"), deref("")) == .gt);
}

/// Returns whether two iterators contains the same items.
pub fn eql(lhs: anytype, rhs: anytype) bool {
    return order(lhs, rhs) == .eq;
}

test "eql" {
    try testing.expect(!eql(deref("abcd"), deref("bee")));
    try testing.expect(!eql(deref("bee"), deref("abcd")));
    try testing.expect(eql(deref("abc"), deref("abc")));
    try testing.expect(!eql(deref("abc"), deref("abc0")));
    try testing.expect(!eql(deref("abc0"), deref("abc")));
    try testing.expect(eql(deref(""), deref("")));
    try testing.expect(!eql(deref(""), deref("a")));
    try testing.expect(!eql(deref("a"), deref("")));
}

/// Returns whether two iterators contains different items.
pub fn not_eql(lhs: anytype, rhs: anytype) bool {
    return order(lhs, rhs) != .eq;
}

test "not_eql" {
    try testing.expect(not_eql(deref("abcd"), deref("bee")));
    try testing.expect(not_eql(deref("bee"), deref("abcd")));
    try testing.expect(!not_eql(deref("abc"), deref("abc")));
    try testing.expect(not_eql(deref("abc"), deref("abc0")));
    try testing.expect(not_eql(deref("abc0"), deref("abc")));
    try testing.expect(!not_eql(deref(""), deref("")));
    try testing.expect(not_eql(deref(""), deref("a")));
    try testing.expect(not_eql(deref("a"), deref("")));
}

/// Compares two iterators lexicographically, returning `true` if `lhs` is less than `rhs`
pub fn less_than(lhs: anytype, rhs: anytype) bool {
    return order(lhs, rhs) == .lt;
}

test "less_than" {
    try testing.expect(less_than(deref("abcd"), deref("bee")));
    try testing.expect(!less_than(deref("bee"), deref("abcd")));
    try testing.expect(!less_than(deref("abc"), deref("abc")));
    try testing.expect(less_than(deref("abc"), deref("abc0")));
    try testing.expect(!less_than(deref("abc0"), deref("abc")));
    try testing.expect(!less_than(deref(""), deref("")));
    try testing.expect(less_than(deref(""), deref("a")));
    try testing.expect(!less_than(deref("a"), deref("")));
}

/// Compares two iterators lexicographically, returning `true` if `lhs` is less than or equal to
/// `rhs`
pub fn less_than_eql(lhs: anytype, rhs: anytype) bool {
    return order(lhs, rhs) != .gt;
}

test "less_than_eql" {
    try testing.expect(less_than_eql(deref("abcd"), deref("bee")));
    try testing.expect(!less_than_eql(deref("bee"), deref("abcd")));
    try testing.expect(less_than_eql(deref("abc"), deref("abc")));
    try testing.expect(less_than_eql(deref("abc"), deref("abc0")));
    try testing.expect(!less_than_eql(deref("abc0"), deref("abc")));
    try testing.expect(less_than_eql(deref(""), deref("")));
    try testing.expect(less_than_eql(deref(""), deref("a")));
    try testing.expect(!less_than_eql(deref("a"), deref("")));
}

/// Compares two iterators lexicographically, returning `true` if `lhs` is greater than `rhs`
pub fn greater_than(lhs: anytype, rhs: anytype) bool {
    return order(lhs, rhs) == .gt;
}

test "greater_than" {
    try testing.expect(!greater_than(deref("abcd"), deref("bee")));
    try testing.expect(greater_than(deref("bee"), deref("abcd")));
    try testing.expect(!greater_than(deref("abc"), deref("abc")));
    try testing.expect(!greater_than(deref("abc"), deref("abc0")));
    try testing.expect(greater_than(deref("abc0"), deref("abc")));
    try testing.expect(!greater_than(deref(""), deref("")));
    try testing.expect(!greater_than(deref(""), deref("a")));
    try testing.expect(greater_than(deref("a"), deref("")));
}

/// Compares two iterators lexicographically, returning `true` if `lhs` is greater than or equal
/// to `rhs`
pub fn greater_than_eql(lhs: anytype, rhs: anytype) bool {
    return order(lhs, rhs) != .lt;
}

test "greater_than_eql" {
    try testing.expect(!greater_than_eql(deref("abcd"), deref("bee")));
    try testing.expect(greater_than_eql(deref("bee"), deref("abcd")));
    try testing.expect(greater_than_eql(deref("abc"), deref("abc")));
    try testing.expect(!greater_than_eql(deref("abc"), deref("abc0")));
    try testing.expect(greater_than_eql(deref("abc0"), deref("abc")));
    try testing.expect(greater_than_eql(deref(""), deref("")));
    try testing.expect(!greater_than_eql(deref(""), deref("a")));
    try testing.expect(greater_than_eql(deref("a"), deref("")));
}

/// Returns true, if for all items it is true that `lt(ctx, items[n-1], items[n]) == true`
pub fn is_sorted(_it: anytype, ctx: anytype, lt: *const fn (
    @TypeOf(ctx),
    IteratorItem(@TypeOf(_it)),
    IteratorItem(@TypeOf(_it)),
) bool) bool {
    var it = iterator(_it);
    var prev = it.next() orelse return true;
    while (it.next()) |curr| : (prev = curr) {
        if (lt(ctx, curr, prev))
            return false;
    }

    return true;
}

test "is_sorted" {
    try testing.expect(is_sorted(deref(&[_]i32{}), {}, std.sort.asc(i32)));
    try testing.expect(is_sorted(deref(&[_]i32{10}), {}, std.sort.asc(i32)));
    try testing.expect(is_sorted(deref(&[_]i32{ 1, 2, 3, 4, 5 }), {}, std.sort.asc(i32)));
    try testing.expect(is_sorted(deref(&[_]i32{ -10, 1, 1, 1, 10 }), {}, std.sort.asc(i32)));

    try testing.expect(is_sorted(deref(&[_]i32{}), {}, std.sort.desc(i32)));
    try testing.expect(is_sorted(deref(&[_]i32{-20}), {}, std.sort.desc(i32)));
    try testing.expect(is_sorted(deref(&[_]i32{ 3, 2, 1, 0, -1 }), {}, std.sort.desc(i32)));
    try testing.expect(is_sorted(deref(&[_]i32{ 10, -10 }), {}, std.sort.desc(i32)));

    try testing.expect(is_sorted(deref(&[_]i32{ 1, 1, 1, 1, 1 }), {}, std.sort.asc(i32)));
    try testing.expect(is_sorted(deref(&[_]i32{ 1, 1, 1, 1, 1 }), {}, std.sort.desc(i32)));

    try testing.expect(!is_sorted(deref(&[_]i32{ 5, 4, 3, 2, 1 }), {}, std.sort.asc(i32)));
    try testing.expect(!is_sorted(deref(&[_]i32{ 1, 2, 3, 4, 5 }), {}, std.sort.desc(i32)));

    try testing.expect(is_sorted(deref("abcd"), {}, std.sort.asc(u8)));
    try testing.expect(is_sorted(deref("zyxw"), {}, std.sort.desc(u8)));

    try testing.expect(!is_sorted(deref("abcd"), {}, std.sort.desc(u8)));
    try testing.expect(!is_sorted(deref("zyxw"), {}, std.sort.asc(u8)));

    try testing.expect(is_sorted(deref("ffff"), {}, std.sort.asc(u8)));
    try testing.expect(is_sorted(deref("ffff"), {}, std.sort.desc(u8)));
}

/// Given a function `fn(T) R`, return a new function with the same semantics, but with the
/// signature `fn(void, T) R`. This is useful when you have functions that don't take a `ctx` but
/// still want to pass them to `ziter` function without wrapping them yourself.
/// ```
/// const ascii_digits = range(u8, 0, 255)
///     .filter({}, void_ctx(std.ascii.isDigit));
/// ```
pub fn void_ctx(
    comptime func: anytype,
) fn (void, ParamType(@TypeOf(func), 0)) ReturnType(@TypeOf(func)) {
    return struct {
        fn f(_: void, arg: ParamType(@TypeOf(func), 0)) ReturnType(@TypeOf(func)) {
            return func(arg);
        }
    }.f;
}

/// Given some `value`, this function will try to turn it into an iterator. The transformations
/// are as follows:
/// ```
/// *[N]T, []T -> ziter.Slice([]T)
/// ?T         -> ziter.One(T)
/// E!T        -> ziter.One(T)
/// *Iterator  -> Iterator
/// Iterator   -> Iterator
/// ```
pub fn iterator(value: anytype) Iterator(@TypeOf(value)) {
    return switch (@typeInfo(@TypeOf(value))) {
        .Pointer => |info| switch (info.size) {
            .One => switch (@typeInfo(info.child)) {
                .Array => slice(value),
                else => value.*,
            },
            .Slice => slice(value),
            else => value,
        },
        .Optional => optional(value),
        .ErrorUnion => error_union(value),
        else => value,
    };
}

/// The return type of `iterator`
pub fn Iterator(comptime T: type) type {
    const Res = switch (@typeInfo(T)) {
        .Pointer => |info| switch (info.size) {
            .One => switch (@typeInfo(info.child)) {
                .Array => Slice(ToSlice(T)),
                else => info.child,
            },
            .Slice => Slice(ToSlice(T)),
            else => T,
        },
        .Optional => |info| One(info.child),
        .ErrorUnion => |info| One(info.payload),
        else => T,
    };

    typecheckIterator(Res);
    return Res;
}

/// Returns the type of the items an iterator returns.
pub fn IteratorItem(comptime _It: type) type {
    const It = Iterator(_It);
    typecheckIterator(It);
    return std.meta.Child(ReturnType(@TypeOf(It.next)));
}

test "IteratorItem" {
    try testing.expectEqual(void, IteratorItem(struct {
        pub fn next(_: @This()) ?void {}
    }));
    try testing.expectEqual(u8, IteratorItem(struct {
        pub fn next(_: @This()) ?u8 {
            return 1;
        }
    }));
    try testing.expectEqual(?u8, IteratorItem(struct {
        pub fn next(_: @This()) ??u8 {
            return 1;
        }
    }));
}

fn typecheckIterator(comptime It: type) void {
    const invalid_iterator = @typeName(It) ++ " is no a valid iterator";
    if (!@hasDecl(It, "next"))
        @compileError(invalid_iterator ++ ": Missing next function");

    const NextItem = struct {};
    const NextFn = @TypeOf(It.next);
    const expected = @typeName(fn (*It) ?NextItem);
    const wrong_next_func = invalid_iterator ++
        ": expected " ++ expected ++
        ", found " ++ @typeName(NextFn);

    switch (@typeInfo(NextFn)) {
        .Fn => |info| {
            if (@typeInfo(info.return_type orelse void) != .Optional)
                @compileError(wrong_next_func);
            if (info.params.len != 1)
                @compileError(wrong_next_func);
        },
        else => @compileError(wrong_next_func),
    }
}

/// Simular to `std.testing.expectEqualSlices` but for iterators.
pub fn expectEqual(expected_it: anytype, actual_it: anytype) !void {
    var e_it = expected_it;
    var a_it = actual_it;

    while (true) {
        const expected = e_it.next();
        const actual = a_it.next();
        try testing.expectEqual(expected, actual);

        // The `exceptEqual` before ensures that both iterators end with `null` and the same time
        // so we can just check one and return.
        if (expected == null)
            return;
    }
}

/// Same as `expectEqual` but iterates the iterators in reverse order.
pub fn expectEqualReverse(expected_it: anytype, actual_it: anytype) !void {
    var e_it = expected_it;
    var a_it = actual_it;

    while (true) {
        const expected = e_it.next_back();
        const actual = a_it.next_back();
        try testing.expectEqual(expected, actual);

        // The `exceptEqual` before ensures that both iterators end with `null` and the same time
        // so we can just check one and return.
        if (expected == null)
            return;
    }
}

/// Same as `expectEqual` but randomly pick between forward and backwards iteration. Good for
/// fuzzing backwards and forward iteration logic.
pub fn expectEqualRandomOrder(
    random: std.rand.Random,
    expected_it: anytype,
    actual_it: anytype,
) !void {
    var e_it = expected_it;
    var a_it = actual_it;

    while (true) {
        const back = random.boolean();
        const expected = if (back) e_it.next_back() else e_it.next();
        const actual = if (back) a_it.next_back() else a_it.next();
        try testing.expectEqual(expected, actual);

        // The `exceptEqual` before ensures that both iterators end with `null` and the same time
        // so we can just check one and return.
        if (expected == null)
            return;
    }
}

fn ReturnType(comptime F: type) type {
    return switch (@typeInfo(F)) {
        .Fn => |info| info.return_type.?,
        .Pointer => |info| switch (info.size) {
            .One => @typeInfo(info.child).Fn.return_type.?,
            else => unreachable,
        },
        else => unreachable,
    };
}

fn ParamType(comptime F: type, comptime n: usize) type {
    return switch (@typeInfo(F)) {
        .Fn => |info| info.params[n].type.?,
        .Pointer => |info| switch (info.size) {
            .One => @typeInfo(info.child).Fn.params[n].type.?,
            else => unreachable,
        },
        else => unreachable,
    };
}
