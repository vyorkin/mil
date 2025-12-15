import Mathlib
import Mathlib.Data.Real.Basic

-- 3. Логика.

-- 3.1. Импликация и квантор существования.

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ,
  0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

-- Нам помогут доказать эту лемму чуть позже.
theorem my_lemma : ∀ x y ε : ℝ,
  0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  sorry

section

variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end

namespace My1
-- Можно использовать неявные аргументы.
theorem my_lemma2 : ∀ {x y ε : ℝ},
  0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  sorry

section

variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

-- Теперь можно не писать a b δ.
#check my_lemma2 h₀ h₁ ha hb
-- Можно частично применить только к паре гипотез-аргументов.
#check my_lemma2 h₀ h₁
end

end My1

namespace My2

-- Похоже на первую встречу с тактикой intro в этой книге.
theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  sorry

#check abs_mul -- |a * b| = |a| * |b|
#check abs_nonneg -- 0 ≤ |a|
#check mul_le_mul -- (h₁ : a ≤ b) (h₂ : c ≤ d) (c0 : 0 ≤ c) (b0 : 0 ≤ b) : a * c ≤ b * d
#check mul_lt_mul_right -- (a0 : 0 < a) : b * a < c * a ↔ b < c
#check one_mul --  1 * a = a

#check le_of_lt -- (hab : a < b) : a ≤ b

#check add_le_add_left -- a ≤ b → ∀ c, c + a ≤ c + b
#check add_lt_add_left -- (bc : b < c) (a : α) : a + b < a + c

-- Завершить доказательство, используя следующие теоремы:
-- abs_mul, mul_le_mul, abs_nonneg, mul_lt_mul_right, and one_mul.
theorem my_lemma4' :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := abs_mul x y
    _ ≤ |x| * ε := by
      apply mul_le_mul (le_refl _)
      · exact le_of_lt ylt
      · exact abs_nonneg y
      · exact abs_nonneg x

    -- Вот с этой частью доказательства неравенства
    -- я не справился самостоятельно, оставалось чуть-чуть и
    -- я не допёр для применения тактики linarith:
    --
    -- _ < 1 * ε := by
    --   --  mul_lt_mul_right : (a0 : 0 < a) : (b * a < c * a) ↔ b < c
    --   --  mul_lt_mul_right : (a0 : 0 < ε) : (b * ε < c * ε) ↔ b < c
    --   rw [mul_lt_mul_right epos]
    --   linarith

    -- Альтернативный вариант (мой):
    _ < 1 * ε := by
      rw [mul_lt_mul_right]
      · linarith
      · assumption

    -- Момент, когда я свернул не туда.
    -- Вместо linarith я стал пробовал транзитивность.
    --   · show |x| < 1
    --     -- В этом точно есть смысл?
    --     -- UPDATE: Нет, нужно было просто использовать linarith.
    --     trans ε
    --     · assumption
    --     · show ε < 1
    --       sorry
    --   · assumption
    _ = ε := one_mul ε

-- lt_of_le' : b ≠ a → a ≤ b → a < b

-- epos : 0 + 1 < ε + 1
-- ele1 : ε + 1 ≤ 1 + 1
-- ⊢ ε < 1

-- Итак:
theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := abs_mul x y
    _ ≤ |x| * ε := by
      apply mul_le_mul (le_refl _)
      · exact le_of_lt ylt
      · exact abs_nonneg y
      · exact abs_nonneg x

    -- _ < 1 * ε := by
    --   rw [mul_lt_mul_right]
    --   · linarith only [xlt, ele1]
    --   · assumption

    -- Доказательство без linarith:
    _ < 1 * ε := by
      -- |x| < ε ≤ 1 ⇒ |x| < 1
      have hx1 : |x| < 1 := lt_of_lt_of_le xlt ele1
      exact (mul_lt_mul_right epos).2 hx1

    -- Ещё один вариант с by_contra:
    -- _ < 1 * ε := by
    --   -- Сначала отдельная лемма: из |x| < ε и ε ≤ 1 следует |x| < 1
    --   have hx1 : |x| < 1 := by
    --     -- Используем стандартный трюк: либо |x| < 1, либо |x| ≥ 1
    --     by_contra h
    --     -- h : ¬ |x| < 1, то есть 1 ≤ |x|
    --     have h1 : 1 ≤ |x| := le_of_not_gt h
    --     -- Из xlt : |x| < ε получаем 1 < ε
    --     have h2 : 1 < ε := lt_of_le_of_lt h1 xlt
    --     -- Из ele1 : ε ≤ 1 и h2 : 1 < ε получаем противоречие 1 < 1
    --     have : 1 < (1 : ℝ) := lt_of_lt_of_le h2 ele1
    --     exact lt_irrefl _ this
    --   -- Теперь переводим неравенство через mul_lt_mul_right
    --   -- (mul_lt_mul_right epos) : (|x| * ε < 1 * ε) ↔ (|x| < 1)
    --   exact (mul_lt_mul_right epos).2 hx1

    _ = ε := one_mul ε

end My2

namespace My3

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

section
variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnUb f a) (hgb : FnUb g b)
        : FnUb (fun x ↦ f x + g x) (a + b) := by
  -- Раскроет определение FnUb потому, что внутри него ∀ x.
  intro x
  -- Эта тактика упрощает "по определению".
  -- В нашем случае упрощает лямбду, выполняя подстановку.
  dsimp
  -- Тоже самое можно было бы сделать так:
  -- change f x + g x ≤ a + b

  -- (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d
  apply add_le_add
  · apply hfa
  · apply hgb

-- Упражнения.

example (hfa : FnLb f a) (hgb : FnLb g b)
  : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  · apply hfa
  · apply hgb

example (nnf : FnLb f 0) (nng : FnLb g 0)
  : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  dsimp
  apply mul_nonneg
  · apply nnf
  · apply nng

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a)
  : FnUb (fun x ↦ f x * g x) (a * b) := by
  intro x; dsimp
  apply mul_le_mul
  · apply hfa
  · apply hgb
  · apply nng
  · apply nna

end

end My3

namespace My4

-- Если мы докажем одну из теорем выше не просто для ℝ, а для набора тайпклассов,
-- то она будет работать для типов, которые являются их инстансами.

variable {α : Type*} {R : Type*}
  [AddCommMonoid R] [PartialOrder R]
  [IsOrderedCancelAddMonoid R]

#check add_le_add -- {α : Type u} [Add α] [Preorder α] [AddLeftMono α] [AddRightMono α]
--                   {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d

def FnUb (f : α → R) (a : R) : Prop := ∀ x, f x ≤ a

-- Теорема add_le_add принимает (h₁ : a ≤ b) и (h₂ : c ≤ d).
-- Мы её их и передаём, только у нас они завёрнуты в определения
-- h₁ := FnUb f a = f x ≤ a
-- h₂ := FbUb g b = g x ≤ b

theorem fnUb_add {f g : α → R} {a b : R}
                 (hfa : FnUb f a) (hgb : FnUb g b)
                : FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

end My4

namespace My5

-- def Monotone (f : α → β) : Prop :=
--   ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

-- Определение Monotone f в точности соответствует тому,
-- что написано справа от `:`.
example (f : ℝ → ℝ) (h : Monotone f)
        : ∀ {a b}, a ≤ b → f a ≤ f b := @h

section

variable (f g : ℝ → ℝ)

example (mf : Monotone f) (mg : Monotone g) : Monotone (fun x ↦ f x + g x) := by
  -- Разворачивает отпределения
  unfold Monotone
  -- Хотя intro тоже развернуло бы
  intro a b -- a ≤ b → (fun x ↦ f x + g x) a ≤ (fun x ↦ f x + g x) b
  dsimp     -- a ≤ b → f a + g a ≤ f b + g b
  intro h   -- f a + g a ≤ f b + g b
  apply add_le_add -- (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d
  · apply mf h
  · apply mg h

-- Когда доказательство настолько тривиальное, то лучше сразу
-- сконструировать терм, а не доказывать в тактик-мод.
example (mf : Monotone f) (mg : Monotone g) : Monotone (fun x ↦ f x + g x) :=
  fun _a _b h ↦ add_le_add (mf h) (mg h)

end

end My5

namespace My6

-- Упражнения.

variable (f g : ℝ → ℝ)

#check mul_le_mul_of_nonneg_left -- (h : b ≤ c) (a0 : 0 ≤ a) : a * b ≤ a * c

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b h; dsimp
  show c * f a ≤ c * f b
  -- (h : b ≤ c) (a0 : 0 ≤ a) : a * b ≤ a * c
  apply mul_le_mul_of_nonneg_left
  · exact mf h
  · assumption

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  fun _ _ h => mul_le_mul_of_nonneg_left (mf h) nnc

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intro a b h; dsimp
  apply mf
  apply mg
  exact h

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  fun _ _ h => mf (mg h)

end My6

namespace My7

-- Функция называется чётной,   если ∀ x, f( x) =  f(-x)
--
-- Функция называется нечётной, если ∀ x, f(-x) = -f( x)
--                    или тоже самое ∀ x, f( x) = -f(-x)
--
-- https://en.wikipedia.org/wiki/Even_and_odd_functions

def FnEven (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)
def FnOdd (f : ℝ → ℝ) : Prop := ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g)
        : FnEven fun x ↦ f x + g x := by
  intro x
  -- Можешь раскрывать определения, если тебе так проще.
  unfold FnEven at ef
  unfold FnEven at eg
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]

-- Упражнения.

-- Если обе ф-ции нечётные, то их произведение – чётная функция.
example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro a
  -- Без dsimp не получится переписать rw [of, og].
  -- Лямбда абстракция не даст это сделать, потому что не получится
  -- найти термы вида f x и g x в выражении цели.
  -- Зацени:
  -- (fun x ↦ f x * g x)
  -- Видишь они там есть, но они зависят от конкретного x,
  -- которых тут - связанная переменная. Т.е. это не любой x.
  -- Тактика rw (rewrite) работает на синтаксическом уровне и она
  -- не будет разворачивать определения или редуцировать термы.
  -- Есть тактика erw, которая делает в этом смысле чуть больше,
  -- чем rw, но не намного.
  dsimp
  unfold FnOdd at of og
  rw [of, og]
  rw [neg_mul_neg]

-- Произведение чётной и нечётной функций - нечётная функция.
example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro a; dsimp;
  unfold FnEven at ef; unfold FnOdd at og
  rw [ef, og]
  rw [← mul_neg]

-- Композиция (последовательное применение) нечётной и чётной функций – чётная функция.
example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro a; dsimp
  unfold FnEven at ef; unfold FnOdd at og
  rw [ef, og, neg_neg]

-- Когда научишься замечать кванторы существования – ты будешь находить их везде.

end My7
