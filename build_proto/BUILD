go_library(
    name = "api_proto",
    srcs = ["build.gen.pb.go"],
    visibility = [
        "//edit:all",
        "//generatetables:all",
        "//lang:all",
    ],
    deps = [
        "///third_party/go/google.golang.org_protobuf//reflect/protoreflect",
        "///third_party/go/google.golang.org_protobuf//runtime/protoimpl",
    ],
)
