load("@crates//:defs.bzl", "all_crate_deps")
load("@rules_rust//rust:defs.bzl", "rust_library")

rust_library(
    name="cairo-vm",
    srcs=glob(["**/*.rs"]),
    data=[],
    visibility=["//visibility:public"],
    deps=all_crate_deps(normal=True),
    proc_macro_deps=all_crate_deps(proc_macro=True),
    edition="2021",
    crate_features=["std", "with_mimalloc"],
)
