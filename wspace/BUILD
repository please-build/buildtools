go_library(
    name = "wspace",
    srcs = ["workspace.go"],
    visibility = [
        "//buildifier:all",
        "//edit:all",
    ],
    deps = ["//build"],
)

go_test(
    name = "wspace_test",
    srcs = ["workspace_test.go"],
    deps = [":wspace"],
)
