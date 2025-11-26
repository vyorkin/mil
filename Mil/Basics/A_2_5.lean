-- 2.5. Proving Facts about Algebraic Structures

import Mathlib

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

#check x < y
#check (lt_irrefl x : ¬(x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
-- Lattice = PartialOrder + {Sup, Inf}

variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y -- infinum/meet
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)

#check x ⊔ y -- supremum/join
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

-- Use: le_refl, le_trans
#check le_refl
#check le_trans

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · apply le_inf
    · apply inf_le_right
    apply inf_le_left
  apply le_inf
  · apply inf_le_right
  apply inf_le_left

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat apply le_inf inf_le_right inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · change x ⊓ y ⊓ z ≤ x
      -- apply inf_le_of_left_le
      apply le_trans inf_le_left
      -- apply le_trans inf_le_left
      · apply inf_le_left
    apply inf_le_inf
    · apply inf_le_right
    apply le_refl
  apply le_inf
  · apply le_inf
    · apply inf_le_left
    change x ⊓ (y ⊓ z) ≤ y
    apply inf_le_of_right_le
    · apply inf_le_left
  change x ⊓ (y ⊓ z) ≤ z
  apply inf_le_of_right_le
  · apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · apply sup_le
    · apply le_sup_right
    apply le_sup_left
  apply sup_le
  · apply le_sup_right
  apply le_sup_left

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  · apply sup_le le_sup_right le_sup_left
  apply sup_le le_sup_right le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    · change x ⊔ y ≤ x ⊔ (y ⊔ z)
      apply sup_le_sup_left
      · apply le_sup_left
    · change z ≤ x ⊔ (y ⊔ z)
      apply le_sup_of_le_right
      · apply le_sup_right
  apply sup_le
  · apply le_sup_of_le_left
    · apply le_sup_left
  apply sup_le_sup_right
  · apply le_sup_right

-- TODO: Rewrite using calc & trans tactics

#check inf_comm
#check inf_assoc
#check sup_comm
#check sup_assoc

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  apply le_inf
  · apply le_refl
  apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · apply le_refl
    apply inf_le_left
  apply le_sup_left

#check inf_sup_self
#check sup_inf_self

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

-- inf_sup_right
-- (x ⊔ y) ⊓ z
-- x *
-- y
-- z   *
--
-- ((x ⊓ z) ⊔ y) ⊓ z
-- x
-- y   *
-- z *   *

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)

#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))

-- distributive lattice
-- 1) x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)
-- 2) x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)

end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) :
  a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) :
  a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry
end
