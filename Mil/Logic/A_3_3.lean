import Mathlib

-- 3.3. Отрицание.

-- Эти определения нам понадобятся, поэтому повторим их тут.

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) := ∃ a, FnUb f a
def FnHasLb (f : ℝ → ℝ) := ∃ a, FnLb f a

variable (f : ℝ → ℝ)
variable (a b : ℝ)

namespace My1

#check lt_asymm  -- (a < b) → ¬(b < a)
#check lt_irrefl -- ∀ a, ¬(a < a)

-- Покажем, что из lt_assym следует lt_irrefl .
example (h : a < b) : ¬(b < a) := by
  intro h'
  have haa : a < a := lt_trans h h'
  -- have nhaa := lt_irrefl a
  -- exact nhaa haa
  exact lt_irrefl a haa

-- Здесь гипотеза h это утверждение, обратное существованию верхней грани ф-ции f.
example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  unfold Not
  intro fnub
  unfold FnHasUb FnUb at fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a  with ⟨x, hx⟩
  --      ^ Это эквивалентно этому:
  -- replace h := h a
  -- rcases h with ⟨x, hx⟩

  have : f x ≤ a := fnuba x
  -- Имеем следующие 2 утверждения, которые оба истинны:
  -- f x > a,                 f x ≤ a
  -- Codomain(f x) = (a, +∞), Codomain(f x) = (-∞, a]
  -- Но эти интервалы вообще не пересекаются.
  linarith

end My1

namespace My2

-- Упражнения.

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro h'
  unfold FnHasLb FnLb at h'
  rcases h' with ⟨a, h0⟩
  rcases h a with ⟨x, h1⟩
  have := h0 x
  linarith

#check lt_asymm  -- (a < b) → ¬(b < a)
#check lt_irrefl -- ∀ a, ¬(a < a)

#check le_refl -- (a : α) : a ≤ a

example : ¬FnHasUb (fun x ↦ x) := by
  unfold FnHasUb FnUb; dsimp
  intro h
  rcases h with ⟨a, h'⟩
  have h0 := h' a
  sorry

-- Разбора решения автора.
example : ¬FnHasUb fun x ↦ x := by
  unfold FnHasUb FnUb; dsimp
  rintro ⟨a, ha⟩
  -- Ключевая идея:
  have h : a + 1 ≤ a := ha (a + 1)
  nth_rw 2 [← add_zero a] at h
  -- h : a + 1 ≤ a + 0
  rw [add_le_add_iff_left] at h
  have h' : ¬(1 ≤ (0:ℝ)) := by
    -- Здесь используем стандартный факт 0 < 1
    have : (0:ℝ) < 1 := by exact zero_lt_one
    -- Из 0 < 1 следует ¬ (1 ≤ 0)
    exact not_le_of_gt this
  exact h' h

-- Почему я не справился:
-- 1. Не догадался до a + 1 ≤ a, из которого можно легко получить 1 ≤ 0,
--    отрицание которого легко сконструировать самостоятельно (см док-во-разбор выше).
-- 2. Плохо понимаю как работает тактика linarith.
-- 3. Плохо понимаю как в целом доказывать противоречивость для неравнеств.

-- Работа над ошибками:

#check not_le_of_gt -- (hab : a < b) : ¬b ≤ a

example : ¬FnHasUb fun x ↦ x := by
  rintro ⟨a, ha⟩;
  unfold FnUb at ha; dsimp at ha
  have h := ha (a + 1)
  -- Можно закончить прямо сейчас используя linarith.
  -- А можно сконструировать противоречие самому, без автоматики.
  nth_rw 2 [← add_zero a] at h
  rw [add_le_add_iff_left] at h
  have h' : ¬ (1:ℝ) ≤ 0 := by
    have hz : (0:ℝ) < 1 := zero_lt_one
    exact not_le_of_gt hz
  exact h' h

--  Оригинальное решение автора.
example : ¬FnHasUb fun x ↦ x := by
  rintro ⟨a, ha⟩
  have : a + 1 ≤ a := ha (a + 1)
  linarith

end My2

namespace My3

#check (not_le_of_gt : a > b → ¬(a ≤ b))
#check (not_lt_of_ge : a ≥ b → ¬(a < b))
#check (lt_of_not_ge : ¬(a ≥ b) → (a < b))
#check (le_of_not_gt : ¬(a > b) → (a ≤ b))

-- Упражнения.

-- def Monotone (f : α → β) : Prop :=
--   ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

example (h : Monotone f) (h' : f a < f b) : a < b := by
  unfold Monotone at h
  apply lt_of_not_ge
  unfold Not; intro h0
  have h1 := h h0
  linarith

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  unfold Monotone Not; intro h0
  have h1 := h0 h
  linarith

-- Упражнение.

-- Можно доказать отрицание квантора всеобщности сконструировав контрпример.

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun _ : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    have g : f a ≤ f b := le_refl _
    unfold Monotone
    intros
    exact g
  have h' : f 1 ≤ f 0 := le_refl _
  have h1 : ∀ {a b : ℝ}, f a ≤ f b → a ≤ b := h monof
  have h2 := @h1 1 0 h'
  linarith

-- Слегка доработанная версия.
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun _ : ℝ ↦ (0:ℝ)
  have monof : Monotone f := by
    intro a b leab
    -- В этом месте я не доагадался, что это
    -- неравенство выполняется по определению функции.
    rfl
  have h' : f 1 ≤ f 0 := le_refl _
  have h1 :  (1:ℝ) ≤ 0 := @h f monof 1 0 h'
  -- Можно закончить сразу тактикой linairth,
  -- а можно и сконструировать отрицание, используя факт о том, что 0 < 1.
  have h2 : ¬(1:ℝ) ≤ 0 := by exact not_le.mpr zero_lt_one
  contradiction

-- Решение автора.
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0:ℝ)
  have monof : Monotone f := by intro a b leab; rfl
  have h₁ : f 1 ≤ f 0 := le_refl _
  have h₂ : (1:ℝ) ≤ 0 := h monof h₁
  linarith

-- Упражнение.

#check le_of_not_gt -- {a b : α}, ¬(b < a) → a ≤ b
#check lt_irrefl

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro hx
  replace h := h x
  replace h := h hx
  revert h
  exact lt_irrefl x

end My3

namespace My4

variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x hpx
  have hex : ∃ x, P x := ⟨x, hpx⟩
  contradiction

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rintro ⟨x, hpx⟩
  have hnpx := h x
  contradiction

-- *
example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  unfold Not at h'
  have hnpx : ∃ x, ¬P x := ⟨x, h''⟩
  exact h' hnpx

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  rcases h with ⟨x, hnpx⟩
  intro h'
  have hpx := h' x
  contradiction

-- Ещё упражнения.

example (h : ¬¬Q) : Q := by
  by_contra h'
  exact h h'

#check not_not

example (h : Q) : ¬¬Q := by exact not_not.mpr h

#check (lt_of_not_ge : ¬(a ≥ b) → (a < b))

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  unfold FnHasUb FnUb at h
  intro c
  by_contra h'
  apply h
  use c
  intro x
  by_contra h''
  replace h'' : ¬(c ≥ f x) := h''
  unfold Not at h''
  -- ((c ≥ f x) → False) → c < f x
  -- ((a ≥ b  ) → False) → a < b
  have h0 : c < f x := lt_of_not_ge h''
  replace h0 : f x > c := h0
  have h1 : ∃ x, f x > c := ⟨x, h0⟩
  exact h' h1


end My4

namespace My5

-- Тактика push_neg.

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  unfold FnHasUb FnUb
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  -- unfold FnHasUb FnUb at h
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

-- Упражнение.
example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  unfold Monotone at h
  push_neg at h
  exact h

end My5

namespace My6

-- Тактика contrapose!
-- Трансформирует цель A → B в ¬A → ¬B.
--                           ^ Закон контрапозиции.
-- https://en.wikipedia.org/wiki/Contraposition
--
-- Суть в следующем:
-- Если из истинности некоторого утверждения следует истинность другого,
-- то в случае ложности второго утверждения первое никак не может быть
-- истинным, поскольку иначе было бы истинным и второе.

-- Для contrapose / contrapose! ты должен указать гипотезу с который
-- ты будешь делать эту логическую контрапозицию.

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x/2
  constructor <;> linarith

end My6

namespace My7

-- ex falso quodlibet - принцип взрыва / дедуктивный взрыв.
--
-- https://en.wikipedia.org/wiki/Principle_of_explosion
-- https://ru.wikipedia.org/wiki/%D0%9F%D1%80%D0%B8%D0%BD%D1%86%D0%B8%D0%BF_%D0%B2%D0%B7%D1%80%D1%8B%D0%B2%D0%B0
-- См "Доказательство" вот тут ^
-- ^
-- Любое утверждение может быть доказано из противоречия.
-- Из противоречия следует всё что угодно.
-- Из противоречия можно доказать любое утверждение.

-- TL;DR:
-- P ∧ ¬P - Исходное противоречие
-- Q - Любое утверждение (единороги существуют)
-- P ∨ Q - Введение "или"
-- P ∨ Q, ¬P => Q - Дизъюнктивный силлогизм

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬(0 < 0) := lt_irrefl 0
  contradiction

end My7
