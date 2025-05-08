pub fn build(b: *std.Build) void {
    const optimize = b.standardOptimizeOption(.{});
    const target = b.standardTargetOptions(.{});

    const module = b.addModule("ziter", .{
        .root_source_file = b.path("ziter.zig"),
        .target = target,
        .optimize = optimize,
    });

    const test_step = b.step("test", "Run all tests in all modes.");
    const main_tests = b.addTest(.{ .root_module = module });
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

    const all_step = b.step("all", "Build everything and runs all tests");
    all_step.dependOn(test_step);

    b.default_step.dependOn(all_step);
}

const std = @import("std");
