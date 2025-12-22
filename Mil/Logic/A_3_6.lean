import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic

-- 3.6. Последовательности и сходимость.

namespace My1

-- Определение из Зорича:
--
-- Число a называется пределом числовой последовательности s : ℕ → ℝ,
-- если для любого ε существует номер N такой, что при всех n > N имеем
-- |s n - a| < ε.

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end My1

-- Нам ещё пригодится это определение.
export My1 (ConvergesTo)

namespace My2

-- ext
--
-- Тактика ext применяет леммы об экстенсиональности, которые
-- помечены аттрибутом @[ext].

example : (fun x y : ℝ ↦ (x + y) ^ 2)
        = (fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2) := by
  ext
  ring

-- congr
--
-- Позволяет доказать уравнение между двумя выражениями путем
-- согласования тех частей, которые различаются.
-- В примере ниже это позволяет избавиться от модуля.

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

-- Это "тактика конгруэнтности", она сравнивает левую и правую части цели
-- вида f as = f bs и раскладывает равенство на подцели для аргументов,
-- где стороны отличаются.
--
-- Как работает:
--
-- Если цель имеет вид f a₁ … aₙ = f b₁ … bₙ, то congr
-- снимает общий f и порождает подцели aᵢ = bᵢ только для
-- тех аргументов, где Lean не может сам их отождествить.
--
-- congr k ограничивает глубину рекурсивного спуска: сколько
-- "слоёв функций" можно разбирать. Это нужно, когда дефолтный congr
-- лезет слишком глубоко и генерит неудобные/ложные подцели.


-- convert
--
-- Берёт терм и пытается подогнать его тип к текущей цели, достраивая
-- равенства на всех местах, где тип e и цель отличаются
-- по структуре (через тактику congr!). При этом она рекурсивно идёт по
-- синтаксическому дереву термов и генерирует подцели для несоответствующих подвыражений.

#check mul_lt_mul_right -- : (a0 : 0 < a) : (b < c) → (b * a < c * a)

example {a : ℝ} (h : 1 < a) : a < a * a := by
  -- Форма, которая должна быть:
  -- (a0 : 0 < a) : (1 < a) → (1 * a < a * a)
  --                (1 < a)        a < a * a
  --                 -----         ---------
  --                   ^               ^
  --                   Что есть по факту
  -- Чего нет:
  -- 1) a = 1 * a  - структурно отличается (синтаксически)
  -- 2) 0 < a      - посылка
  --
  -- Тактика convert попросит нас доказать все несоответствующие подвыражения.
  -- В нашем случае оно одно: a vs 1 * a.
  -- Ну и посылки (0 < a) конечно тоже попросит доказать.
  convert (mul_lt_mul_right _).2 h
  --                        ^
  -- Ещё заметь, что вооот тут мы использовали подчёркивание,
  -- поэтому Lean нас попросил доказать это (a0 : 0 < a) утверждение.
  · rw [one_mul]
  · exact lt_trans zero_lt_one h

-- Использование тактики convert можно рассматривать как
-- альтернативу обратному рассуждению.

end My2

namespace My3

-- variable (s t : ℕ → ℝ) (a b c : ℝ)

-- def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
--   ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

-- lim (s n ↦ a) = a, фактически это:
-- ∀ ε > 0, ∃ N, ∀ n ≥ N, |a - a| < ε
-- ∀ ε > 0, ∃ N, ∀ n ≥ N,       0 < ε
theorem convergesTo_const (a : ℝ) : ConvergesTo (fun (_ : ℕ) ↦ a) a := by
  unfold ConvergesTo
  dsimp
  intro ε hε
  use 0 -- C первого же номера уже выполняется.
  intro n hn
  -- rw [sub_self, abs_zero]
  simp
  exact hε

-- Свойства сходящихся последовательностей.

-- (lim s n = a) →
-- (lim t n = b) →
--
-- 1. lim (s n + t n) = a + b
-- 2. lim (s n * t n) = a * b
-- 3. lim (s n)/(t n) = a / b ← b ≠ 0

-- Бумажные доказательствa из Зорича
-- (слегка дополненные моими комментариями).

-- Будем считать эти определения равносильными:
--
-- (conv sₙ = a) ⇔ (lim sₙ = a)
--
-- ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

-- Введём такие обозначения:
--
-- Δ(sₙ) = |sₙ - a|
-- Δ(tₙ) = |tₙ - b|
--
-- Тогда:
--
-- 1. Сумма
-- Для lim (sₙ + tₙ) = a + b имеем
--
-- |(a + b) - (sₙ + tₙ)| ≤ Δ(sₙ) + Δ(tₙ)
--
-- Для sₙ и tₙ имеем соотв. определения сходимости:
-- ∀ ε > 0, ∃ Nₛ, ∀ n ≥ N, Δ(sₙ) < ε
-- ∀ ε > 0, ∃ Nₜ, ∀ n ≥ N, Δ(tₙ) < ε
-- которые верны для любого ε. Возьмём в качестве такого числа ε/2,
-- т.е. пусть задано число ε/2 > 0, тогда верно, что ∃ N, ∀ n ≥ N, Δ(sₙ) < ε/2.
-- Тогда при n > max Nₛ Nₜ имеем:
-- |(a + b) - (sₙ + tₙ)| < ε

-- 2. Произведение

-- 3. Частное

-- 4. Умножение на константу

-- ConvergesTo (fun n ↦ c * s n) (c * a)
-- cs : ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε
-- ⊢ ∀ ε > 0, ∃ N, ∀ n ≥ N, |c * s n - c * a| < ε

-- Моё доказательство.
theorem convergesTo_add' {s t : ℕ → ℝ} {a b : ℝ}
  (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
  ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  unfold ConvergesTo; dsimp
  unfold ConvergesTo at ct cs
  intro ε hε
  -- Основная идея такого доказательства в том, что ε/2 + ε/2 = ε.
  have hε2 : ε/2 > 0 := by linarith
  rcases cs (ε/2) hε2 with ⟨Ns, hs⟩
  rcases ct (ε/2) hε2 with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hnm
  have h₁ : n ≥ Ns := le_of_max_le_left hnm  -- (h : max a b ≤ c) : a ≤ c
  have h₂ : n ≥ Nt := le_of_max_le_right hnm -- (h : max a b ≤ c) : b ≤ c
  have hh := add_lt_add (hs n h₁) (ht n h₂)
  norm_num at hh
  -- Проще всего менять/преобразовывать цель "вычислительным доказательством" (proof by calc).
  -- Не стесняйся его применять, ибо в каждом его (не)равенстве ты можешь перейти в
  -- тактик-мод и работать в нём.
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by congr; ring
    _ ≤ |s n - a| + |t n - b| := abs_add_le (s n - a) (t n - b)
    _ < ε := by assumption

  -- have h' : |s n + t n - (a + b)| ≤ |s n - a| + |t n - b| :=
  --   abs_add_le

-- h1 : |s n - a| < ε/2
-- h2 : |t n - b| < ε/2

-- |s n - a| + |t n - b| < ε/2 + ε/2

-- a + b < c + d

#check add_lt_add -- (h₁ : a < b) (h₂ : c < d) : a + c < b + d
#check abs_add_le -- (a b : α) : |a + b| ≤ |a| + |b|

#check le_of_max_le_left  -- (h : max a b ≤ c) : a ≤ c
#check le_of_max_le_right -- (h : max a b ≤ c) : b ≤ c

-- Доказательство автора.
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
  (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
  ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  have ngeNs : n ≥ Ns := le_of_max_le_left hn  -- (h : max a b ≤ c) : a ≤ c
  have ngeNt : n ≥ Nt := le_of_max_le_right hn -- (h : max a b ≤ c) : b ≤ c
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by congr; ring
    _ ≤ |s n - a| + |t n - b| := abs_add (s n - a) (t n - b)
    _ < ε / 2 + ε / 2 := add_lt_add (hs n ngeNs) (ht n ngeNt)
    _ = ε := by norm_num

#check abs_of_neg    -- a < 0 → |a| = -a
#check abs_of_nonneg -- 0 ≤ a → |a| =  a

theorem convergesTo_mul_const'
  {s : ℕ → ℝ} {a : ℝ} (c : ℝ)
  (cs : ConvergesTo s a) :
  ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · have hh := convergesTo_const 0
    convert hh
    · rw [h]; ring
    · rw [h]; ring
  · have acpos : 0 < |c| := abs_pos.mpr h
    unfold ConvergesTo at *; dsimp
    intro ε hε; try dsimp
    -- Я не додумался выбрать в качестве "любого ε" число: ε / |c|.
    -- Я использовал ε, которое взяли из цели.
    rcases cs ε hε with ⟨Ns, hs⟩
    use Ns
    intro n hn
    have hs' := hs n hn
    rw [← mul_sub c]
    rw [abs_mul]

    -- Здесь всё правильно, но это тупик, тк вверху
    -- ты сделал не правильный выбор ε.

    sorry

#check abs_of_nonneg  -- (h : 0 ≤ a) : |a| = a
#check abs_pos_of_pos -- (h : 0 < a) : 0 < |a|

#check mul_pos    -- 0 < a → 0 < b → 0 < a * b
#check mul_nonneg -- 0 ≤ a → 0 ≤ b → 0 ≤ a * b
#check mul_sub    -- a * (b + c) = a * b + a * c

-- Доказательство автора.
theorem convergesTo_mul_const
  {s : ℕ → ℝ} {a : ℝ} (c : ℝ)
  (cs : ConvergesTo s a) : ConvergesTo (fun n ↦ c * s n) (c * a) := by
  -- unfold ConvergesTo at *; dsimp
  by_cases h : c = 0
  · -- c = 0
    have hh := convergesTo_const 0 -- ∀ ε > 0, ∃ N, ∀ n ≥ N, |0 - 0| < ε
    -- show ∀ ε > 0, ∃ N, ∀ n ≥ N, |c * s n - c * a| < ε
    -- unfold ConvergesTo at hh; dsimp at hh
    convert hh
    · rw [h]; ring
    · rw [h]; ring
  · -- c ≠ 0
    have acpos : 0 < |c| := abs_pos.mpr h -- 0 < |a| ↔ a ≠ 0
    intro ε εpos; dsimp
    -- Делимое и делитель положительные - дробь положительная.
    -- (ha : 0 < a) (hb : 0 < b) : 0 < a / b
    have εcpos : 0 < ε / |c| := by apply div_pos εpos acpos
    -- Выбирем в качестве "любого ε" число ε / |c|.
    rcases cs (ε / |c|) εcpos with ⟨Ns, hs⟩
    use Ns
    intro n ngt
    have hgtz : |s n - a| < ε / |c| := hs n ngt
    calc
      |c * s n - c * a| = |c| * |s n - a| := by rw [← abs_mul, mul_sub]
      -- (bc : b < c) (a0 : 0 < a) : a * b < a * c
      --
      -- hgtz  : |s n - a| < ε / |c|
      -- acpos : 0 < |c|
      --
      -- (bc : |s n - a| < (ε / |c|)) (a0 : 0 < |c|) :
      -- |c| * |s n - a| < |c| * (ε / |c|)
      _ < |c| * (ε / |c|) := mul_lt_mul_of_pos_left hgtz acpos
      -- (hb : b ≠ 0) : b * (a / b) = a
      _ = ε := mul_div_cancel₀ _ (ne_of_lt acpos).symm
      --                          --------------------
      --                                   ^^
      --                           (h : a < b) : b ≠ a

#check ne_of_lt -- : (h : a < b) : a ≠ b
#check mul_div_cancel -- : (a : G₀) (hb : b ≠ 0) : b * (a / b) = a
#check mul_lt_mul_of_pos_left -- : (bc : b < c) (a0 : 0 < a) : a * b < a * c

-- Упражнение.
-- Convergent sequence is eventually bounded in absolute value.
theorem exists_abs_le_of_convergesTo' {s : ℕ → ℝ} {a : ℝ}
  (cs : ConvergesTo s a) : ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  unfold ConvergesTo at cs
  -- Выбираем ε = 1, 1 > 0
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  show ∀ (n : ℕ), N ≤ n → |s n| < |a| + 1
  intro n hn
  have hh := h n hn
  rw [add_comm, ← add_neg_lt_iff_lt_add]
  sorry

-- Проблемы:
-- 1. На шарю за congr.
--    Вот так можно:
--    |s n| = |s n - a + a| := by congr.
--     s n - 0 = s n - (a + a)
-- 2.

-- Доказательство автора.
theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ}
  (cs : ConvergesTo s a) : ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n ngt
  calc
    |s n| = |(s n - a) + a| := by
      congr
      show s n = s n - a + a -- Снял модуль
      abel
    _ ≤ |s n - a| + |a| := (abs_add _ _) -- |a + b| ≤ |a| + |b|
    _ = |a| + |s n - a| := by rw [add_comm]
    _ < |a| + 1 := by linarith [h n ngt] -- Потому что |s n - a| < 1

-- In fact, the theorem could be strengthened to
-- assert that there is a bound b that holds for all values of n.

theorem aux' {s t : ℕ → ℝ} {a : ℝ}
  (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
  ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos; dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have h₁  : 0 ≤ |s N₀| := abs_nonneg (s N₀)
  have hN₀ : N₀ ≤ N₀ := le_refl N₀
  have h₂  : |s N₀| < B := h₀ N₀ hN₀
  --
  -- lt_of_le_of_lt : (hab : a ≤ b) (hbc : b < c)     : a < c
  --                       ^             ^                ^
  --                    h₁ : 0 ≤ |s N₀|  |                |
  --                                  h₂ : |s N₀| < B : 0 < B
  --
  have Bpos : 0 < B := lt_of_le_of_lt h₁ h₂
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  -- unfold ConvergesTo at ct cs
  rcases ct (ε / B) pos₀ with ⟨N₁, h₁⟩
  use N₁
  intro n hN₁; norm_num
  -- have hN₁ : N₁ ≤ N₁ := le_refl N₁
  replace h₁ := h₁ n hN₁; norm_num at h₁

  -- have h₃ := h₀ n
  rw [abs_mul]

  -- Вот тут если посмотреть на h₀ и h₁, то сразу
  -- можно догадаться что делать дальше.

  sorry

#check abs_mul -- |a * b| = |a| * |b|

-- (h₁ : a < b) (h₂ : c < d) (a0 : 0 ≤ a) (c0 : 0 ≤ c) : a * c < b * d
#check mul_lt_mul''

-- Что пошло не так:
-- 1. Не догадался использовать max N₀ N₁, так же как
--    мы это делали при доказательстве сходимости суммы.
-- 2. Не увидел, что можно воспользоваться mul_lt_mul'' : a * c < b * d,
--    показав необходимые посылки.

-- Догадался по ε * (ε / B), но не увидел, что для этого нужно обеспечить
-- одновременную справедливость для обоих утверждений.

-- Доказатльство автора (разбор).
theorem aux {s t : ℕ → ℝ} {a : ℝ}
  (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
  ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n ngt
  have ngeN₀ : n ≥ N₀ := le_of_max_le_left ngt
  have ngeN₁ : n ≥ N₁ := le_of_max_le_right ngt
  calc
    |s n * t n - 0| = |s n| * |t n - 0| := by rw [sub_zero, abs_mul, sub_zero]
    _ < B * (ε / B) := by
      have hh₁ : |s n| < B := h₀ n ngeN₀
      have hh₂ : |t n - 0| < ε / B := h₁ n ngeN₁
      have hh₃ : 0 ≤ |s n| := abs_nonneg (s n)
      have hh₄ : 0 ≤ |t n - 0| := abs_nonneg (t n - 0)
      -- (hh₁ : a < b) (hh₂ : c < d) (hh₃ : 0 ≤ a) (hh₄ : 0 ≤ c) : a * c < b * d
      apply mul_lt_mul'' hh₁ hh₂ hh₃ hh₄
    _ = ε := mul_div_cancel₀ _ (ne_of_lt Bpos).symm

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
  (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
  ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    have hh := convergesTo_add ct (convergesTo_const (-b))
    convert hh
    ring
  have hh := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert hh using 1
  · ext; ring
  ring

-- TODO: Вернуться сюда позже и передоказать
-- все недоказанные теоремы о сходимости последовательностей.

-- Упражнение.
-- TODO:

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by sorry
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by sorry
  have absb : |s N - b| < ε := by sorry
  have : |a - b| < |a - b| := by sorry
  exact lt_irrefl _ this

end My3

namespace My4

variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end My4
