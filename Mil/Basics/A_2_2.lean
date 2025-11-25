-- 2.2. Proving Identities in Algebraic Structures

import Mathlib

example (a b c : ℕ) (h : a + b = c) :
  (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]

-- CommRing

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring
example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring
example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

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
end

namespace MyRing

variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by
  rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by
  rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_neg_cancel, add_zero]

theorem add_left_cancel₁ {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← add_neg_cancel_left a b, add_comm (-a), ← add_assoc]
  rw [← add_neg_cancel_right c a, add_comm c a]
  rw [h]

theorem add_left_cancel₂ {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← add_neg_cancel_right b a, add_comm b a]
  rw [← add_neg_cancel_right c a, add_comm c a]
  rw [h]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b]
  rw [← add_neg_cancel_right c b]
  rw [h]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel₂ h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 + 0 * a := by
    rw [← add_mul, add_zero, zero_add]
  rw [add_right_cancel h]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [← neg_add_cancel_right b a]
  rw [add_comm]
  rw [← add_assoc]
  rw [h]
  rw [zero_add]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [← neg_add_cancel_left b a, add_comm b a]
  rw [h, add_zero]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  rw [add_comm, add_neg_cancel]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

example (a b : ℝ) : a - b = a + -b := rfl
example (a b : ℝ) : a - b = a + -b := by rfl

theorem self_sub (a : R) : a - a = 0 := by
  rw [← add_neg_cancel a]
  rw [sub_eq_add_neg]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two]
  rw [add_mul]
  rw [one_mul]

variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

lemma aux₁ (a b : G) : a = (b⁻¹ * b) * a := by
  nth_rw 1 [← one_mul a]
  rw [← inv_mul_cancel]

lemma aux₂ (a : G) : 1 = a⁻¹ * (1 * a) := by
  nth_rw 1 [← inv_mul_cancel a]
  nth_rw 2 [← one_mul a]

theorem inv_inv_eq (a : G) : a⁻¹⁻¹ = a := by
  nth_rw 2 [← one_mul a]
  rw [← inv_mul_cancel a⁻¹]
  rw [mul_assoc]
  rw [inv_mul_cancel]
  rw [mul_one]

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  rw [← inv_mul_cancel a⁻¹]
  rw [inv_inv_eq]

theorem mul_one (a : G) : a * 1 = a := by
  rw [aux₁ a a⁻¹]
  rw [← inv_mul_cancel a]
  rw [← mul_assoc]
  nth_rw 1 [mul_assoc a⁻¹⁻¹ a⁻¹]
  nth_rw 1 [inv_mul_cancel]
  nth_rw 1 [mul_assoc a⁻¹⁻¹ 1]
  rw [one_mul]

theorem mul_inv_comm (a : G) : a * a⁻¹ = a⁻¹ * a := by
  rw [mul_inv_cancel]
  rw [inv_mul_cancel]

-- mul_comm?

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  -- nth_rw 2 [aux₁ a b]
  -- nth_rw 2 [aux₁ b a]
  -- nth_rw 1 [← one_mul (a * b)⁻¹]
  -- nth_rw 1 [← inv_mul_cancel b]
  -- nth_rw 4 [aux₁ b b]
  -- nth_rw 2 [mul_assoc]
  sorry

end MyRing
