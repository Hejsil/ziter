const iter = @import("../ziter.zig");
const std = @import("std");

const debug = std.debug;
const mem = std.mem;

pub fn SpanIter(comptime Span: type) type {
    const Array = @Type(.{
        .Array = .{
            .child = @typeInfo(Span).Pointer.child,
            .sentinel = @typeInfo(Span).Pointer.sentinel,
            .len = 0,
        },
    });

    return struct {
        span: Span = &Array{},

        // HACK: Cannot use &it.span[0] here
        // --------------------------------vvvvvvvvvvvvvvvvvvvvvvvvvvvv
        pub fn next(it: *@This()) ?@TypeOf(&@intToPtr(*Span, 0x10).*[0]) {
            if (it.span.len == 0)
                return null;

            defer it.span = it.span[1..];
            return &it.span[0];
        }

        pub fn len_hint(it: @This()) iter.LengthHint {
            return .{ .min = it.span.len, .max = it.span.len };
        }

        pub const call = iter.call_method;
    };
}

/// Creates an iterator that iterates over all the items of an array or slice.
pub fn span(s: anytype) SpanIter(mem.Span(@TypeOf(s))) {
    return .{ .span = mem.span(s) };
}

comptime {
    const c = "a".*;
    var v = "a".*;
    var sc = span(&c);
    var sv = span(&v);

    debug.assert(@TypeOf(sc.next()) == ?*const u8);
    debug.assert(@TypeOf(sv.next()) == ?*u8);
}

test "span" {
    const items = "abcd";
    iter.test_it(span(items[0..]), .{ .min = 4, .max = 4 }, &[_]*const u8{ &items[0], &items[1], &items[2], &items[3] });
    iter.test_it(span(items[1..]), .{ .min = 3, .max = 3 }, &[_]*const u8{ &items[1], &items[2], &items[3] });
    iter.test_it(span(items[2..]), .{ .min = 2, .max = 2 }, &[_]*const u8{ &items[2], &items[3] });
    iter.test_it(span(items[3..]), .{ .min = 1, .max = 1 }, &[_]*const u8{&items[3]});
    iter.test_it(span(items[4..]), .{ .min = 0, .max = 0 }, &[_]*const u8{});
}
