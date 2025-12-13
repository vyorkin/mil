-- 2.4. More examples using apply and rw

import Mathlib

variable (a b c d e f x y w z : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

#check (lt_min_iff : a < min b c ↔ (a < b) ∧ (a < c))
#check (min_lt_iff : min a b < c ↔ (a < c) ∨ (b < c))

#check (le_min_iff : c ≤ min a b ↔ (c ≤ a) ∧ (c ≤ b))
#check (min_le_iff : min a b ≤ c ↔ (a ≤ c) ∨ (b ≤ c))

#check (min_le_min : a ≤ c → b ≤ d → min a b ≤ min c d)

#check (min_le_of_left_le : a ≤ c → min a b ≤ c)
#check (min_le_of_right_le : b ≤ c → min a b ≤ c)

#check (min_eq_left_iff : min a b = a ↔ a ≤ b)
#check (min_eq_right_iff : min a b = b ↔ b ≤ a)

#check (min_eq_iff : min a b = c ↔ (a = c ∧ a ≤ b) ∨ (b = c ∧ b ≤ a))

#check (le_max_left a b : a ≤ max a b)
#check (le_max_right a b : b ≤ max a b)
#check (max_le : a ≤ c → b ≤ c → max a b ≤ c)

-- Из-за того, что нет скобок все эти значки мешаются в кучу
-- и сложновато глазами распарсить отдельные конъюнкты/дизъюнкты.
-- Поэтому ты просто не видишь, что можно применить эту теорему,
-- как будто пробгаешь быстро взглядом и пропускаешь. Поставь скобки -
-- тебе будет легче заметить то, на что не обращал внимания.
#check (max_le_iff : max a b ≤ c ↔ (a ≤ c) ∧ (b ≤ c))
#check (le_max_iff : a ≤ max b c ↔ (a ≤ b) ∨ (a ≤ c))

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    · apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    · apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    · apply min_le_right
    apply min_le_left
  apply le_antisymm
  · apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  apply le_antisymm
  · apply max_le
    · apply le_max_right
    · apply le_max_left
  apply max_le
  · apply le_max_right
  · apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    · apply min_le_iff.mpr
      · left
        apply min_le_left
    · apply min_le_min
      · apply min_le_right
      · apply le_rfl
  apply le_min
  · apply le_min_iff.mpr
    · constructor
      · apply min_le_left
      · apply min_le_of_right_le
        apply min_le_left
  apply min_le_of_right_le
  apply min_le_right

example : max (max a b) c = max a (max b c) := by
  apply le_antisymm
  · apply max_le
    · apply max_le_max
      · exact le_rfl
      · exact le_max_left _ _
    · rw [le_max_iff]
      right
      exact le_max_right _ _
  · apply max_le
    · rw [le_max_iff]
      left
      exact le_max_left _ _
    · apply max_le
      · rw [le_max_iff]
        left
        exact le_max_right _ _
      · rw [le_max_iff]
        right
        exact le_rfl

#check add_neg_cancel_right

-- Операция min дистрибутивна относительно max так же как и
-- умножение относительно сложения, ну и наоборот -
-- max относительно min тоже дистрибутивна.

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_right
    apply min_le_left
  · apply add_le_add_right
    apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  · have h : min (a + c) (b + c) =
             min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
    rw [h]
    apply add_le_add_right
    rw [sub_eq_add_neg]
    apply le_trans
    · apply aux
    · rw [add_neg_cancel_right, add_neg_cancel_right]

-- Моя следующая фундаментальная ошибка в том, что
-- я перестаю пользоваться интуицией когда перехожу к формальному доказательству.
-- Я перестаю видеть смысл за символами и начинаю оперировать ими
-- согласно установленному множеству правил-теорем, используя этакий
-- шизофреничный способ мышления перебором вариантов.
-- (Объяснение ниже - хуета?)
-- В начале должно быть интуитивное глубокое понимание формулировки
-- теоремы и некоторая идея доказательства. Например, увидеть,
-- что в теореме ниже с двух сторон по сути:
--
-- min a b = a                                      a + c = min (a + c) (b + c)
--     ∨        => {a | b} + c = {a + c | b + c} <=
-- min a b = b                                      b + c = min (a + c) (b + c)
--
-- Бля, как будто этот аски-арт только путает, но похуй.
--
-- Затем надо понять, что это похоже на хвост
-- add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c
-- И начать преобразовывать к этому виду другую сторону неравенства.
-- Да, на несколько шагов вперёд ты в голове не можешь это осмыслить,
-- у тебя тупо не хватит ОЗУ, но ты можешь сделать шаг и посмотреть на ситуацию, в
-- в которую он тебя приведёт: Тупик или нет? Как двигаться дальше? Чем можешь воспользоваться?
--
-- Короче, тут тонкая грань:
-- Идея первого шага может быть похожа на хвост той теоремы,
-- с помощью которой можно начать обратное рассуждение.
-- Это похоже на подход, когда ты перебираешь варианты, но "это другое".

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  rw [← add_neg_cancel_right (min (a + c) (b + c)) c]
  rw [add_assoc, ← add_comm (-c), ← add_assoc]
  apply add_le_add_right
  apply le_min -- (!1)
  · nth_rw 2 [← add_neg_cancel_right a (-c)]
    rw [neg_neg]
    rw [add_assoc, add_comm (-c), ← add_assoc]
    apply add_le_add_right
    apply min_le_left
  nth_rw 2 [← add_neg_cancel_right b (-c)]
  rw [neg_neg]
  rw [add_assoc, add_comm (-c), ← add_assoc]
  apply add_le_add_right
  apply min_le_right

-- Я доказал, но доказательство выглядит ужасающе.
-- Вот чего я не увидел:
--
-- 1) Снова не заметил что вычитание это сложение, поэтому на шаге (!1)
--    применил le_min вместо rw [sub_eq_add_neg]. Дальше всё могло быть (и было бы) иначе.
-- 2) Не нашёл sub_add_cancel : a - b + b = a,
--    вместо неё использовал неудобную add_neg_cancel_right.
--    Я её не нашёл потому, что просто не искал, а использовал только те,
--    которые мне встречались ранее по мере прохождения книги.
-- 3) Недооцениваю введение промежуточных гипотез.
--    Что проще понятнее выглядит / проще читается?
--    а)
--      rw [← add_neg_cancel_right (min (a + c) (b + c)) c]
--      rw [add_assoc, ← add_comm (-c), ← add_assoc]
--    b)
--      have h : min (a + c) (b + c) =
--               min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
--      rw [h]

-- https://github.com/avigad/mathematics_in_lean_source/issues/348
#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| :=
  sorry

theorem whatever : |a| - |b| ≤ |a - b| := by
  rw [tsub_le_iff_right]
  -- apply?
  sorry

-- Divisibility

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left
  -- exact dvd_mul_left x y

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    · rw [← mul_assoc]
      apply dvd_mul_of_dvd_left
      apply dvd_mul_left
    apply dvd_mul_left
  apply dvd_pow h
  linarith

variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply dvd_antisymm
  repeat
    repeat rw [← gcd_eq_nat_gcd]
    rw [gcd_comm]
