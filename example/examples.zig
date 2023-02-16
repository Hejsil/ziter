const iter = @import("../ziter.zig");
const std = @import("std");

test "ascii" {
    const ascii_digits = iter.range(u8, 0, 255)
        .filter({}, iter.void_ctx(std.ascii.isDigit));

    const ascii_alpha = try iter.range(u8, 0, 255)
        .filter({}, iter.void_ctx(std.ascii.isAlphabetic))
        .collect_no_allocator(std.BoundedArray(u8, 255){});

    try iter.expectEqual(iter.deref("0123456789"), ascii_digits);
    try std.testing.expectEqualStrings(
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz",
        ascii_alpha.slice(),
    );
}

test "Fibonacci" {
    const fib = Fibonacci{};

    const fib_sum_first_5 = fib.take(5).sum(usize);
    const fib_first_alphabetic = fib.map({}, to_u8)
        .find({}, iter.void_ctx(std.ascii.isAlphabetic));

    try std.testing.expectEqual(@as(usize, 7), fib_sum_first_5);
    try std.testing.expectEqual(@as(?u8, 'Y'), fib_first_alphabetic);
}

pub const Fibonacci = struct {
    c: usize = 0,
    n: usize = 1,

    pub fn next(it: *@This()) ?usize {
        const curr = it.c;
        it.c = it.n;
        it.n = curr + it.n;
        return curr;
    }

    pub usingnamespace iter;
};

fn to_u8(_: void, item: usize) u8 {
    return @truncate(u8, item);
}
