-- 2.1. Calculating

import Mathlib

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_assoc c b a]
  rw [mul_comm c (b * a)]
  rw [mul_assoc b a c]

-- No arguments

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm]
  rw [mul_comm a c]
  rw [mul_assoc]

example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

-- Partial pattern

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm a]
  rw [mul_assoc b c]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm a]
  rw [mul_assoc b]
  rw [mul_comm a]

-- Using facts from local context

example (a b c d e f : ℝ)
  (h₁ : a * b = c * d)
  (h₂ : e = f) : a * (b * e) = c * (d * f) := by
  rw [h₂]
  rw [← mul_assoc]
  rw [h₁]
  rw [mul_assoc]

-- Try with sub_self

example (a b c d e f : ℝ)
  (h : b * c = e * f) : ((a * b) * c) * d = a * e * f * d := by
  rw [mul_assoc a b c]
  rw [h]
  rw [← mul_assoc]

example (a b c d : ℝ)
  (hyp₁ : c = b * a - d)
  (hyp₂ : d = a * b) : c = 0 := by
  rw [hyp₂] at hyp₁
  rw [mul_comm] at hyp₁
  rw [sub_self (a * b)] at hyp₁
  exact hyp₁

-- Multiple rewrites & sections

section

variable (a b c d e f : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

example
  (h₁ : a * b = c * d)
  (h₂ : e = f) : a * (b * e) = c * (d * f) := by
  rw [h₂, ← mul_assoc, h₁, mul_assoc]

end

example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

-- Calc

example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

section

variable (a b c d : ℝ)

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [mul_add, add_mul, add_mul]
  rw [add_assoc, ← add_assoc (b * c)]
  rw [add_comm (b * c) (a * d)]
  rw [← add_assoc, ← add_assoc]


example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc
    (a + b) * (c + d) = a * c + b * c + (a * d + b * d) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * c + (b * c + a * d + b * d) := by
      rw [add_assoc, ← add_assoc (b * c)]
    _ = a * c + (a * d + b * c + b * d) := by
      rw [add_comm (b * c) (a * d)]
    _ = a * c + a * d + b * c + b * d := by
      rw [← add_assoc, ← add_assoc]
end

section
variable (a b c : ℝ)

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw [pow_two, pow_two]
  rw [add_mul, mul_sub, mul_sub]
  rw [mul_comm b a]
  rw [add_sub]
  rw [add_comm]
  rw [add_sub]
  rw [add_comm]
  rw [← add_sub]
  rw [sub_self]
  rw [add_zero]

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

end

section
variable (a b c : ℝ)

-- Тактика ring позволяет доказывать равенства для любого
-- коммутативного кольца. Для этого требуется, чтобы эти
-- равенства напрямую следовали только из аксиом кольца, без
-- необходимости дополнительно использовать локальные гипозы.

example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  -- Сначала самостоятельно используем наши локальные,
  -- тк ring их не умеет использовать.
  rw [hyp, hyp']
  -- Только теперь можно применить ring.
  ring
end

example (a b c : ℕ) (h : a + b = c) :
  (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
