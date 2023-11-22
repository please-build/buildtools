go_library(
    name = "tables",
    srcs = [
        "jsonparser.go",
        "tables.go",
    ],
    visibility = [
        "//build:all",
        "//buildifier:all",
        "//buildozer:all",
        "//edit:all",
        "//warn:all",
    ],
)

go_test(
    name = "tables_test",
    srcs = ["jsonparser_test.go"],
    deps = [":tables"],
)
