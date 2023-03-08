const std = @import("std");

pub fn build(b: *std.Build) void {
    const optimize = b.standardOptimizeOption(.{});
    const target = b.standardTargetOptions(.{});

    const module = b.addModule("ziter", .{ .source_file = .{ .path = "ziter.zig" } });

    const test_step = b.step("test", "Run all tests in all modes.");
    const main_tests = b.addTest(.{
        .root_source_file = .{ .path = "ziter.zig" },
        .target = target,
        .optimize = optimize,
    });

    const example_tests = b.addTest(.{
        .root_source_file = .{ .path = "example/examples.zig" },
        .target = target,
        .optimize = optimize,
    });
    example_tests.addModule("ziter", module);

    test_step.dependOn(&main_tests.step);
    test_step.dependOn(&example_tests.step);

    const readme_step = b.step("readme", "Remake README.");
    const readme = readMeStep(b);
    readme.dependOn(test_step);
    readme_step.dependOn(readme);

    const all_step = b.step("all", "Build everything and runs all tests");
    all_step.dependOn(test_step);
    all_step.dependOn(readme_step);

    b.default_step.dependOn(all_step);
}

fn readMeStep(b: *std.Build) *std.Build.Step {
    const s = b.allocator.create(std.build.Step) catch unreachable;
    s.* = std.build.Step.init(.custom, "ReadMeStep", b.allocator, struct {
        fn make(_: *std.build.Step) anyerror!void {
            @setEvalBranchQuota(10000);

            const file = try std.fs.cwd().createFile("README.md", .{});
            const stream = file.writer();
            try stream.print(@embedFile("example/README.md.template"), .{
                @embedFile("example/examples.zig"),
            });
        }
    }.make);
    return s;
}
