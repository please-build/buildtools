go_library(
    name = "utils",
    srcs = [
        "diagnostics.go",
        "flags.go",
        "tempfile.go",
        "utils.go",
    ],
    visibility = ["//buildifier:all"],
    deps = [
        "//build",
        "//warn",
    ],
)

go_test(
    name = "utils_test",
    srcs = ["utils_test.go"],
    deps = [":utils"],
)
