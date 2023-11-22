go_library(
    name = "warn",
    srcs = [
        "multifile.go",
        "types.go",
        "warn.go",
        "warn_bazel.go",
        "warn_bazel_api.go",
        "warn_bazel_operation.go",
        "warn_control_flow.go",
        "warn_cosmetic.go",
        "warn_docstring.go",
        "warn_macro.go",
        "warn_naming.go",
        "warn_operation.go",
    ],
    visibility = [
        "//buildifier:all",
        "//buildifier/utils:all",
        "//warn/docs:all",
    ],
    deps = [
        "//build",
        "//bzlenv",
        "//edit",
    ],
)

go_test(
    name = "warn_test",
    srcs = [
        "types_test.go",
        "warn_bazel_api_test.go",
        "warn_bazel_test.go",
        "warn_control_flow_test.go",
        "warn_cosmetic_test.go",
        "warn_docstring_test.go",
        "warn_macro_test.go",
        "warn_naming_test.go",
        "warn_operation_test.go",
        "warn_test.go",
    ],
    deps = [
        ":warn",
        "//build",
        "//tables",
        "//testutils",
    ],
)
