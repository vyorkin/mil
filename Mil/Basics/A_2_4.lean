-- 2.4. More examples using apply and rw

import Mathlib

variable (a b c d e f : ℝ)

#check (lt_min_iff : a < min b c ↔ a < b ∧ a < c)
#check (min_lt_iff : min a b < c ↔ a < c ∨ b < c)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

#check (le_min_iff : c ≤ min a b ↔ c ≤ a ∧ c ≤ b)
#check (min_le_iff : min a b ≤ c ↔ a ≤ c ∨ b ≤ c)

#check (min_le_min : a ≤ c → b ≤ d → min a b ≤ min c d)

#check (min_le_of_left_le : a ≤ c → min a b ≤ c)
#check (min_le_of_right_le : b ≤ c → min a b ≤ c)

#check (min_eq_left_iff : min a b = a ↔ a ≤ b)
#check (min_eq_right_iff : min a b = b ↔ b ≤ a)

#check (min_eq_iff : min a b = c ↔ a = c ∧ a ≤ b ∨ b = c ∧ b ≤ a)

#check (le_max_left a b : a ≤ max a b)
#check (le_max_right a b : b ≤ max a b)
#check (max_le : a ≤ c → b ≤ c → max a b ≤ c)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

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
    apply le_max_left
  apply max_le
  · apply le_max_right
  apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    · apply min_le_iff.mpr
      · left
        apply min_le_left
    apply min_le_min
    · apply min_le_right
    apply le_rfl
  apply le_min
  · apply le_min_iff.mpr
    · constructor
      · apply min_le_left
      apply min_le_of_right_le
      apply min_le_left
  apply min_le_of_right_le
  apply min_le_right

#check add_neg_cancel_right

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_right
    apply min_le_left
  apply add_le_add_right
  apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
  rw [← add_neg_cancel_right (min (a + c) (b + c)) c]
  rw [add_assoc, ← add_comm (-c), ← add_assoc]
  apply add_le_add_right
  apply le_min
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
