# Mathematics in Lean — конспекты и решения

🇷🇺 Русский · [🇬🇧 English](README.en.md)

## О чём этот репозиторий

Здесь лежат мои личные конспекты и решения упражнений из учебника
[*Mathematics in Lean*](https://leanprover-community.github.io/mathematics_in_lean)
— я прохожу его, чтобы разобраться с Lean 4 и Mathlib. Комментарии
в коде написаны по-русски: это не библиотека и не образцовый код,
а рабочий дневник человека, который учится. Планка качества —
«доказательство корректно и заметки будут полезны мне самому, когда
я вернусь перечитать это через полгода», а не production-стиль.

Многие упражнения решены по нескольку раз разными тактиками —
специально, чтобы сравнить подходы и понять, какой яснее.

Структура репозитория и правила по работе с кодом — в [CLAUDE.md](CLAUDE.md)
(это конфиг для Claude Code, но он же годится как обычная документация:
там расписано, как устроены файлы по главам/секциям книги и как
добавлять новые).

## Благодарности

Огромное спасибо авторам *Mathematics in Lean* — Джереми Авигаду
(Jeremy Avigad), Патрику Массо (Patrick Massot) и остальным
участникам проекта — за прекрасный, тщательно продуманный учебник,
а также сообществу Lean/Mathlib за то, что делает всё это возможным.

## Дисклеймер

Это учебный репозиторий, а не референсное решение. Где-то доказательства
наверняка не самые изящные, где-то комментарии могут быть неточными
или устаревшими — я просто разбираюсь по ходу дела. Если что-то не так —
извините, и добро пожаловать в issues/PR, если заметите ошибку.

## Сборка

- Собрать всё: `lake build`
- Собрать/проверить один файл: `lake build Mil.Basics.A_2_1`
  (путь модуля через точки, без `.lean`)
- После свежего клона (или смены тулчейна) — забрать готовый кэш
  Mathlib `.olean`, иначе первая сборка перекомпилирует весь Mathlib:
  `lake exe cache get`

Версия Lean зафиксирована в `lean-toolchain` и управляется через `elan`;
версия Mathlib зафиксирована в `lakefile.toml`.

## Структура

Файлы организованы по главам книги, номера секций соответствуют
нумерации в учебнике (`Mil/<Глава>/A_<глава>_<секция>.lean`):

| Глава книги | Директория |
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

## Лицензия

[Unlicense](LICENSE) — делайте с этим кодом что хотите.
