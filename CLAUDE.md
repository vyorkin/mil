# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

Personal solutions and notes (comments in Russian) for [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean), a Lean 4 / Mathlib textbook. This is a learning repo, not a library — code quality bar is "correct proof + useful notes for future review," not production style.

## Commands

- Build everything: `lake build`
- Build/check a single file: `lake build Mil.Basics.A_2_1` (module path, dots not slashes, no `.lean`)
- Fetch prebuilt Mathlib `.olean` cache (do this once after a fresh clone or after bumping the toolchain, otherwise the first build compiles all of Mathlib): `lake exe cache get`
- Toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.21.0`) and managed by `elan`; Mathlib version is pinned in `lakefile.toml` (`rev = "v4.21.0"`).
- There is no test suite and no linter beyond what `lake build` itself reports (Lean errors/warnings, and the `weak.linter.mathlibStandardSet` lints enabled in `lakefile.toml`).
- Prefer the `lean-lsp` MCP tools (`lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`, etc.) over `lake build` for iterating on a proof in progress — they're much faster since they talk to the running LSP instead of recompiling.

## Module structure

Files are organized by book chapter, mirroring the book's section numbers:

```
Mil.lean                          -- top-level import list (must import each chapter file below)
Mil/Basics.lean                   -- imports every Mil/Basics/A_2_*.lean
Mil/Basics/A_2_1.lean … A_2_5.lean
Mil/Logic.lean                    -- imports every Mil/Logic/A_3_*.lean
Mil/Logic/A_3_1.lean … A_3_6.lean
Mil/SetsAndFunctions.lean          -- imports every Mil/SetsAndFunctions/A_4_*.lean
Mil/SetsAndFunctions/A_4_1.lean, A_4_2.lean
```

Naming: `A_<chapter>_<section>.lean`, matching the book's numbering (e.g. `A_4_1.lean` is book section 4.1). Each chapter has one aggregator file (`Mil/<Chapter>.lean`) that just imports all of that chapter's section files, and `Mil.lean` imports each chapter aggregator.

**When adding a new section file**, wire it into both levels:
1. Add `import Mil.<Chapter>.A_<ch>_<sec>` to `Mil/<Chapter>.lean`.
2. If it's a brand-new chapter, create `Mil/<Chapter>.lean` and add `import Mil.<Chapter>` to `Mil.lean`.

## File conventions

- Each section file opens with a `-- N.M. Title` comment matching the book heading, then follows the book's order of examples/exercises.
- Exercises are often solved multiple times with different tactics/approaches, each as a separate `example`, with a short Russian comment above noting the approach (e.g. "Антисимметрия", "Прямое конструирование пруф-терма") and sometimes a self-critique of which approach is better.
- Related examples/exercises are grouped in `namespace My1`, `My2`, ... blocks per file to avoid name clashes between independent proof attempts.
- `#check` lines are used liberally as inline documentation of a lemma's signature (`#check mem_inter_iff -- (a b : Set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b`) right before it's used — keep this pattern when introducing a new Mathlib lemma.
- Comments capture *why* a tactic/approach was chosen or what mistake was made, not what the code does — keep new comments in that spirit and in Russian, consistent with the existing notes.
