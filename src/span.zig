const iter = @import("../ziter.zig");
const std = @import("std");

const debug = std.debug;
const mem = std.mem;

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

        pub fn len_hint(it: @This()) iter.LengthHint {
            return .{ .min = it.span.len, .max = it.span.len };
        }

        pub const call = iter.call_method;
    };
}

/// Creates an iterator that iterates over all the items of an array or slice.
pub fn span(s: anytype) iter.Deref(Span(mem.Span(@TypeOf(s)))) {
    return iter.deref(span_by_ref(s));
}

test "span" {
    const items = "abcd";
    iter.test_it(span(items[0..]), .{ .min = 4, .max = 4 }, items[0..]);
    iter.test_it(span(items[1..]), .{ .min = 3, .max = 3 }, items[1..]);
    iter.test_it(span(items[2..]), .{ .min = 2, .max = 2 }, items[2..]);
    iter.test_it(span(items[3..]), .{ .min = 1, .max = 1 }, items[3..]);
    iter.test_it(span(items[4..]), .{ .min = 0, .max = 0 }, items[4..]);
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
    iter.test_it(span_by_ref(items[0..]), .{ .min = 4, .max = 4 }, refs[0..]);
    iter.test_it(span_by_ref(items[1..]), .{ .min = 3, .max = 3 }, refs[1..]);
    iter.test_it(span_by_ref(items[2..]), .{ .min = 2, .max = 2 }, refs[2..]);
    iter.test_it(span_by_ref(items[3..]), .{ .min = 1, .max = 1 }, refs[3..]);
    iter.test_it(span_by_ref(items[4..]), .{ .min = 0, .max = 0 }, refs[4..]);
}
