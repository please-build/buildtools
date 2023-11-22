go_library(
    name = "bzlenv",
    srcs = ["bzlenv.go"],
    visibility = ["//warn:all"],
    deps = ["//build"],
)

go_test(
    name = "bzlenv_test",
    srcs = ["bzlenv_test.go"],
    deps = [
        ":bzlenv",
        "//build",
    ],
)
