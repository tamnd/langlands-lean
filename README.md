# langlands-lean

The Lean 4 code of the langlands project. The project states the Langlands program in Lean, proves the known parts, from class field theory to the local Langlands correspondence for $GL_2$, and works on the open parts as research bets.

**The general conjectures of the program are not proved.** This package states them, and it proves only the results that have a proof in the literature. A statement of an open conjecture is a `def ... : Prop`. It is never a theorem and never an axiom.

The map of the project, the milestones and the site are in [tamnd/langlands](https://github.com/tamnd/langlands). The site is [langlands.tamnd.com](https://langlands.tamnd.com). The `lgl` command that reads the records of this package is in [tamnd/langlands-agent](https://github.com/tamnd/langlands-agent).

## Layout

| Directory | Content |
|---|---|
| `Langlands/Statements/` | the statements of the program, one file for each part, pinned in `manifests/statements.sha256` |
| `Langlands/Fidelity/` | checks F1 to F3 of the fidelity battery: special cases, a known example and a known non-example for each statement |
| `Langlands/Bridge/` | proofs that a statement here is equivalent to a statement of another project |
| `Langlands/Ported/` | files from other Apache-2.0 projects, with their licence header and a provenance line |
| `Langlands/WIP/` | unfinished work, not imported by `Langlands.lean` |

## Build

You need [elan](https://github.com/leanprover/elan). The toolchain is in `lean-toolchain`.

```sh
lake exe cache get
lake build
sh scripts/scan.sh
```

The workflow `build` also writes `records/lean.json` with `scripts/Export.lean`. That record has the kind, the file, the type and the axioms of each declaration. `lgl index` in tamnd/langlands reads it.

## Trust

Each proof in the main tree uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. The workflow `build` checks this on each push. The workflow `trust` replays the package each week in the Lean kernel with `leanchecker`, and checks it again with lean4lean and nanoda.

## Pins

| Item | Pin |
|---|---|
| Lean | v4.35.0 |
| Mathlib | v4.35.0 |

## Licence

Apache-2.0. See [LICENSE](LICENSE).
