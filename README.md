# ziter

A iterator library for Zig.

```zig
const std = @import("std");
const it = @import("ziter");

fn add(a: usize, b: usize) usize { return a + b; }
fn addPair(p: [2]usize) usize { return p[0] + p[1]; }
fn isDivBy3(n: usize) bool { return n % 3 == 0; }

test "" {
    const result = it.range(usize, 0, 100)
        .pipe(it.slidingWindow, .{2})
        .pipe(it.map, .{addPair})
        .pipe(it.filter, .{isDivBy3})
        .pipe(it.fold, .{@as(usize, 0), add});

    try std.testing.expectEqual(@as(usize, 3267), result);
}
```

