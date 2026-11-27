# Rustlyn documentation

| Document | Contents |
|---|---|
| [analyzer.md](analyzer.md) | `rustlyn-analyzer`: blast radius, value graph, failability, Unity, NuGet; the CLI tools and extension traits |
| [status.md](status.md) | What works: validation on Roslyn's sources, the self-build, and what each component supports |
| [architecture.md](architecture.md) | The crates, the pipeline, and the design decisions taken from Roslyn |
| [performance.md](performance.md) | Batch compile benchmark against `csc`, where the time goes, memory |
| [editor.md](editor.md) | `rustlyn-ide` and `rustlyn-ffi`: layered editor services, project loading (including Unity), the `rln_*` API |
| [differences-from-roslyn.md](differences-from-roslyn.md) | Known, deliberate differences from Roslyn and the C# spec |
| [roadmap.md](roadmap.md) | What's next, and the list of milestones so far |
| [development.md](development.md) | Building, testing, environment variables, examples, and the `tools/` harnesses |

Harness-specific documentation lives next to each harness:
[bench](../tools/bench/README.md), [cav](../tools/cav/README.md),
[diag](../tools/diag/README.md), [oss](../tools/oss/README.md).
