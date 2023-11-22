go_library(
    name = "edit",
    srcs = [
        "buildozer.go",
        "default_buildifier.go",
        "edit.go",
        "fix.go",
        "types.go",
    ],
    visibility = [
        "//buildozer:all",
        "//edit/safe:all",
        "//unused_deps:all",
        "//warn:all",
    ],
    deps = [
        "///third_party/go/github.com_golang_protobuf//jsonpb",
        "///third_party/go/github.com_golang_protobuf//proto",
        "//api_proto",
        "//build",
        "//build_proto:api_proto",
        "//file",
        "//labels",
        "//lang",
        "//tables",
        "//wspace",
    ],
)
