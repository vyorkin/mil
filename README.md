# Mathematics in Lean — конспекты и решения

🇷🇺 Русский · [🇬🇧 English](README.en.md)

Мои конспекты и решения упражнений из учебника
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean)
— прохожу его, чтобы разобраться с Lean 4 и Mathlib. Комментарии в коде
на русском.

Часть упражнений решена по несколько раз разными тактиками — сравниваю
подходы. Структура файлов и правила по коду — в [CLAUDE.md](CLAUDE.md).

Спасибо авторам учебника — Jeremy Avigad, Patrick Massot и всем, кто
над ним работал, — и сообществу Mathlib.

Сорян, если чо.

## Сборка

- `lake build` — собрать всё
- `lake build Mil.Basics.A_2_1` — собрать/проверить один файл
  (путь модуля через точки, без `.lean`)
- `lake exe cache get` — после клона или смены тулчейна забрать кэш
  Mathlib, иначе первая сборка перекомпилирует весь Mathlib

Версия Lean зафиксирована в `lean-toolchain`, версия Mathlib —
в `lakefile.toml`.

## Структура

Файлы разложены по главам книги: `Mil/<Глава>/A_<глава>_<секция>.lean`,
например `Mil/Basics/A_2_1.lean` — секция 2.1.

Главы: Basics (2), Logic (3), Sets and Functions (4), Elementary Number
Theory (5), Discrete Mathematics (6), Structures (7), Hierarchies (8),
Groups and Rings (9), Linear Algebra (10), Topology (11), Differential
Calculus (12), Integration and Measure Theory (13).

## Лицензия

[Unlicense](LICENSE).
