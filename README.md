# ziter

A iterator library for Zig.

```zig
const std = @import("std");
const it = @import("ziter");

fn add(a: usize, b: usize) usize { return a + b; }
fn add_pair(p: [2]usize) usize { return p[0] + p[1]; }
fn is_div_by_3(n: usize) bool { return n % 3 == 0; }

test "" {
    const result = it.range(usize, 0, 100)
        .pipe(it.sliding_window, .{2})
        .pipe(it.map, .{add_pair})
        .pipe(it.filter, .{is_div_by_3})
        .pipe(it.fold, .{@as(usize, 0), add});

    std.testing.expectEqual(@as(usize, 3267), result);
}
```

