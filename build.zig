const std = @import("std");

pub fn build(b: *std.Build) void {
    const optimize = b.standardOptimizeOption(.{});
    const target = b.standardTargetOptions(.{});

    const module = b.addModule("ziter", .{ .root_source_file = b.path("ziter.zig") });

    const test_step = b.step("test", "Run all tests in all modes.");
    const main_tests = b.addTest(.{
        .root_source_file = b.path("ziter.zig"),
        .target = target,
        .optimize = optimize,
    });
    const run_main_tests = b.addRunArtifact(main_tests);

    const example_tests = b.addTest(.{
        .root_source_file = b.path("example/examples.zig"),
        .target = target,
        .optimize = optimize,
    });
    const run_example_tests = b.addRunArtifact(example_tests);
    example_tests.root_module.addImport("ziter", module);

    test_step.dependOn(&run_main_tests.step);
    test_step.dependOn(&run_example_tests.step);

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
    const s = b.allocator.create(std.Build.Step) catch unreachable;
    s.* = std.Build.Step.init(.{
        .id = .custom,
        .name = "ReadMeStep",
        .owner = b,
        .makeFn = struct {
            fn make(_: *std.Build.Step, _: std.Progress.Node) anyerror!void {
                @setEvalBranchQuota(10000);
                const file = try std.fs.cwd().createFile("README.md", .{});
                const stream = file.writer();
                try stream.print(@embedFile("example/README.md.template"), .{
                    @embedFile("example/examples.zig"),
                });
            }
        }.make,
    });
    return s;
}
