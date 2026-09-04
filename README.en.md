# Mathematics in Lean — Notes and Solutions

[🇷🇺 Русский](README.md) · 🇬🇧 English

## What this is

This repo holds my personal notes and exercise solutions for the
[*Mathematics in Lean*](https://leanprover-community.github.io/mathematics_in_lean)
textbook, worked through while learning Lean 4 and Mathlib. Code comments
are written in Russian: this isn't a library or a showcase of idiomatic
style, it's a working notebook for someone learning as they go. The bar
is "the proof is correct and the notes will still be useful to me in six
months," not production code quality.

Many exercises are solved more than once with different tactics, on
purpose, to compare approaches and see which one is clearer.

Repo layout and conventions live in [CLAUDE.md](CLAUDE.md) (written as
config for Claude Code, but it doubles as plain documentation — it
explains how files map to the book's chapters/sections and how to add
new ones).

## Thanks

Huge thanks to the authors of *Mathematics in Lean* — Jeremy Avigad,
Patrick Massot, and the rest of the contributors — for a wonderful,
carefully crafted textbook, and to the Lean/Mathlib community for
making all of this possible.

## Disclaimer

This is a learning repo, not a reference solution set. Some proofs are
probably not the most elegant, and some comments may be imprecise or
out of date — I'm just figuring things out as I go. Sorry if something's
off, and pull requests/issues are welcome if you spot a mistake.

## Building

- Build everything: `lake build`
- Build/check a single file: `lake build Mil.Basics.A_2_1`
  (module path, dots not slashes, no `.lean`)
- After a fresh clone (or a toolchain bump), fetch the prebuilt Mathlib
  `.olean` cache, otherwise the first build compiles all of Mathlib:
  `lake exe cache get`

The Lean version is pinned in `lean-toolchain` and managed by `elan`;
the Mathlib version is pinned in `lakefile.toml`.

## Structure

Files are organized by book chapter, with section numbers matching the
textbook's numbering (`Mil/<Chapter>/A_<chapter>_<section>.lean`):

| Book chapter | Directory |
| --- | --- |
| 2. Basics | `Mil/Basics` |
| 3. Logic | `Mil/Logic` |
| 4. Sets and Functions | `Mil/SetsAndFunctions` |
| 5. Elementary Number Theory | `Mil/ElementaryNumberTheory` |
| 6. Discrete Mathematics | `Mil/DiscreteMathematics` |
| 7. Structures | `Mil/Structures` |
| 8. Hierarchies | `Mil/Hierarchies` |
| 9. Groups and Rings | `Mil/GroupsAndRings` |
| 10. Linear Algebra | `Mil/LinearAlgebra` |
| 11. Topology | `Mil/Topology` |
| 12. Differential Calculus | `Mil/DifferentialCalculus` |
| 13. Integration and Measure Theory | `Mil/IntegrationAndMeasureTheory` |

## License

[Unlicense](LICENSE) — do whatever you want with this code.
