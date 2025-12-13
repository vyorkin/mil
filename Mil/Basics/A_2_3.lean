-- 2.3. Using Theorems and Lemmas

import Mathlib

namespace My1
variable (a b c : ℝ)

-- Рассмотрим следующие 2 леммы:

-- Вот для этой существует две версии - с явными и неявными аргументами.
#check (le_refl : ∀ a : ℝ, a ≤ a)

-- Для этой только с неявными.
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

end My1

namespace My2
-- Если мы определим вот такие переменные
variable (a b c : ℝ)
-- И гипотезы:
variable (h₀ : a ≤ b) (h₁ : b ≤ c)
-- То сможем их использовать вот так:
#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
-- И вот так:
#check (le_trans h₀ h₁ : a ≤ c)
-- Можно частично применить:
#check (le_trans h₀ : b ≤ c → a ≤ c)
end My2

variable (a b c d e f g : ℝ)

-- Тактика apply пытается смэтчить следствие "применяемой" теоремы с текущей целью.
-- Если получается это сделать, то тебе нужно будет доказать
-- гипотезы "применённой" теоремы, они станут новыми целями.
-- Ну а если прям в точности мэтч, то можно писать `exact theorem` вместо `apply theorem`.
-- Ниже примеры её использования.

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  · apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

-- Даже в тактик-мод не обязательно это делать. Можно прям вот так:
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

-- Вот тоже самое:
example (x : ℝ) : x ≤ x := by apply le_refl
example (x : ℝ) : x ≤ x := le_refl x

#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  apply lt_of_le_of_lt
  · exact h₀
  · have h₄ : b < d := lt_of_lt_of_le h₁ h₂
    exact lt_trans h₄ h₃

-- Можно либо писать эти точки для каждой подцели,
-- либо просто уменьшить отступ, чтобы работать со следующей подцелью.
-- И то и другое - ок.

namespace My3

open Real

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith
-- ^ Тактика linarith справляется с линейной арифметикой.
example (h₀ : 2 * a ≤ 3 * b) (h₁ : 1 ≤ a) (h₂ : d = 2) : d + a ≤ 5 * b := by
  linarith

-- А ещё ей можно передавать список неравенств в
-- качестве аргументов и онa будет их использовать.
example (h : 1 ≤ a) (h₀ : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h₀]
  --         ^ exp b ≤ exp c

end My3

open Real

-- Вот некоторые полезные теоремы из Mathlib, которые могут быть
-- полезны для доказательства неравенств на вещественных числах.

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)

#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)

-- Используя теоремы с iff можно переписывать (rw) так же,
-- как и с использованием теорем о равенствах. Например:
example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h

-- .1 или .mp  - modus ponens
-- .2 или .mpr - modus ponens reversed

example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  · apply le_refl

namespace My4

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  apply add_le_add -- (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d
  · apply le_refl
  · rw [exp_le_exp]
    apply add_le_add
    · apply le_refl
    · exact h₀

-- Тактика norm_num вычисляет числовые выражения в целях и гипотезах и
-- сводит задачу к проверке равенства/неравенства двух нормализованных чисел.

example : (0 : ℝ) < 1 := by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by
    rw [add_comm]
    apply add_pos
    · exact exp_pos a
    norm_num
  apply log_le_log h₀
  apply add_le_add
  · apply le_refl
  rw [exp_le_exp]
  exact h

end My4

example : 0 ≤ a ^ 2 := by
  -- apply?
  exact sq_nonneg a

example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  apply tsub_le_tsub
  · apply le_refl
  apply exp_le_exp.mpr h

-- Некоторые автоматические штуки из Lean плохо понимают эквивалентность
-- отношений ≥ и ≤, поэтому в Mathlib предпочитают использовать ≤ вместо ≥.

example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2 := by
    calc
      a^2 - 2*a*b + b^2 = (a - b)^2 := by
        ring
      (a - b)^2 ≥ 0 := by
        apply pow_two_nonneg
  calc
    2*a*b = 2*a*b + 0 := by
      ring
    -- Вот тут можно не писать by:
    2*a*b + 0 ≤ 2*a*b + (a^2 - 2*a*b + b^2) :=
   -- add_le_add (le_refl (2*a*b)) h
      add_le_add (le_refl    _   ) h -- Можно написать _, Lean сам выведет.
    2*a*b + (a^2 - 2*a*b + b^2) = a^2 + b^2 := by
      ring

example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2 := by
    calc
      a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
      (a - b)^2 ≥ 0 := by apply pow_two_nonneg
  linarith

#check two_mul_le_add_sq -- 2*a*b ≤ a^2 + b^2
#check abs_le' -- |a| ≤ b ↔ a ≤ b ∧ -a ≤ b

#check add_le_add_left -- (bc : b ≤ c) (a : α) : a + b ≤ a + c

-- Вот этими не получается воспользоваться
-- потому, что как будто ℝ не MulLeftMono и не MulLeftReflectLE
-- (failed to synthesize instance of ...)
#check mul_le_mul_iff_left  -- a * b ≤ a * c ↔ b ≤ c
#check mul_le_mul_iff_right -- b * a ≤ c * a ↔ b ≤ c

#check le_div_iff₀ -- (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b

-- Мои рассуждения на первой попытке.
example (a b : ℝ) : |a * b| ≤ (a^2 + b^2) / 2 := by
  rw [abs_le']
  constructor
  · -- Избавиться от /2, умножить обе части на 2, перейти к
    -- 2*a*b ≤ a^2 + 2*a*b + b^2 - 2*a*b
    -- 2*a*b ≤ (a - b)^2 + 2*a*b
    -- 0 + 2*a*b ≤ (a - b)^2 + 2*a*b
    -- apply add_le_add (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d
    -- · 0 ≤ (a - b)^2 := by apply pow_two_nonneg
    -- · 2*a*b ≤ 2*a*b := by le_refl
    -- calc
    --   a*b ≤ (a^2 + b^2)/2 := by sorry
    sorry
  · sorry

example (a b : ℝ) : |a * b| ≤ (a^2 + b^2) / 2 := by
  have two_gt_zero : (2 : ℝ) > 0 := by norm_num
  rw [abs_le']
  constructor
  · rw [le_div_iff₀ two_gt_zero]
    calc
      a*b*2 = 0 + 2*a*b := by ring
      _ ≤ (a - b)^2 + 2*a*b := by
        apply (add_le_add (pow_two_nonneg _) (le_refl _))
      _ = a^2 + b^2 := by ring
  · rw [le_div_iff₀ two_gt_zero]
    calc
      -(a*b)*2 = 0 + - 2*a*b := by ring
      _ ≤ (a + b)^2 + - 2*a*b := by
        apply (add_le_add (pow_two_nonneg _) (le_refl _))
      _ = a^2 + b^2 := by ring

-- С чем не справился с первого раза:
-- 1) Не нашёл теорему с помощью которой можно избавиться от /2,
-- умножив обе части на 2: rw [le_div_iff₀ h].
-- 2) Я искал по ключевому слову le_mul_, а нужно было попробовать поискать по le_div_.
-- 3) Потому что не было скобок перед `-` я не увидел сложение в вычитании:
--    (a + b)^2 - 2*a*b = (a + b)^2 + (- 2*a*b).

-- Здесь вычислительное доказательство может быть удобнее и короче,
-- нежели доказательство в тактик-мод.

-- https://github.com/avigad/mathematics_in_lean_source/issues/138#issuecomment-3558928980

theorem fact1 : a*b*2 ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  · calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  · linarith

theorem fact2 : -(a*b)*2 ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 + 2*a*b + b^2
  · calc
    a^2 + 2*a*b + b^2 = (a + b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  · linarith

example : |a*b| ≤ (a^2 + b^2)/2 := by
  have h : (0 : ℝ) < 2 := by norm_num
  apply abs_le'.mpr
  constructor
  · rw [le_div_iff₀ h]
    apply fact1
  · rw [le_div_iff₀ h]
    apply fact2
