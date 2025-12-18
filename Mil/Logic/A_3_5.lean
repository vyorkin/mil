import Mathlib

-- 3.5. Дизъюнкция.

namespace My1

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  have hx : x ^ 2 ≥ 0 := pow_two_nonneg x -- (a : R) : 0 ≤ a ^ 2
  linarith [hx]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 := Or.inl h
example (h : y < -1) : y > 0 ∨ y < -1 := Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  -- Знакомься - второй "режим работы" тактики rcases:
  rcases le_or_gt 0 y with h | h -- a ≤ b ∨ b < a
  · rw [abs_of_nonneg h] -- (h : 0 ≤ a) : |a| = a
    show x < y → (x < y ∨ x < -y)
    intro h
    left
    exact h
  · rw [abs_of_neg h] -- |a| = -a
    intro h
    right
    exact h

end My1
