# Mathematics in Lean — notes and solutions

[🇷🇺 Русский](README.md) · 🇬🇧 English

My notes and exercise solutions for the
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean)
textbook, worked through while learning Lean 4 and Mathlib. Code
comments are in Russian.

Some exercises are solved more than once with different tactics, to
compare approaches. File layout and conventions are in
[CLAUDE.md](CLAUDE.md).

Thanks to the textbook's authors — Jeremy Avigad, Patrick Massot, and
everyone else who worked on it — and to the Mathlib community.

Sorry if something's off.

## Building

- `lake build` — build everything
- `lake build Mil.Basics.A_2_1` — build/check a single file
  (module path, dots not slashes, no `.lean`)
- `lake exe cache get` — after a fresh clone or a toolchain bump,
  fetch the Mathlib cache, otherwise the first build compiles all of
  Mathlib

The Lean version is pinned in `lean-toolchain`, the Mathlib version
in `lakefile.toml`.

## Structure

Files are laid out by book chapter: `Mil/<Chapter>/A_<chapter>_<section>.lean`,
e.g. `Mil/Basics/A_2_1.lean` is section 2.1.

Chapters: Basics (2), Logic (3), Sets and Functions (4), Elementary
Number Theory (5), Discrete Mathematics (6), Structures (7),
Hierarchies (8), Groups and Rings (9), Linear Algebra (10), Topology
(11), Differential Calculus (12), Integration and Measure Theory (13).

## License

[Unlicense](LICENSE).
