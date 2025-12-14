-- 2.5. Proving Facts about Algebraic Structures

import Mathlib

namespace My1

variable {α : Type*} [PartialOrder α]
variable (x y z : α)

-- Нестрогий частичный порядок
#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

-- Стpогий частичный порядок
#check x < y
#check (lt_irrefl x : ¬(x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

end My1

namespace My2

-- Решётка это структура, которая расширяет частичный порядок
-- операциями ⊓ и ⊔: Lattice = PartialOrder + {Inf, Sup}
-- Операция inf: x ⊓ y на некотором
variable {α : Type*} [Lattice α]
-- это аналог min x y на ℝ,
-- а операция sup: x ⊔ y это аналог max x y на ℝ.

variable (x y z : α)

#check x ⊓ y -- infinum/meet
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)

#check x ⊔ y -- supremum/join
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

-- Примеры решёток:
-- 1. min, max на любом полностью упорядоченном множестве, типа ℤ или ℝ (порядок задан ≤)
-- 2. ∩, ∪ на множестве подмножеств вложенных друг в друга (порядок задан ⊆)

end My2

namespace My3

variable {α : Type*} [Lattice α]
variable (x y z : α)

#check le_refl  -- a ≤ a
#check le_trans -- a ≤ b → b ≤ c → a ≤ c

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · apply le_inf
    · apply inf_le_right
    · apply inf_le_left
  · apply le_inf
    · apply inf_le_right
    · apply inf_le_left

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat apply le_inf inf_le_right inf_le_left

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat simp only [le_inf, inf_le_right, inf_le_left]

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · show x ⊓ y ⊓ z ≤ x
      -- apply inf_le_of_left_le
      apply le_trans inf_le_left
      exact inf_le_left
    · apply inf_le_inf
      · apply inf_le_right
      · exact le_refl z
  · apply le_inf
    · apply le_inf
      · exact inf_le_left
      · show x ⊓ (y ⊓ z) ≤ y
        apply inf_le_of_right_le
        exact inf_le_left
    · show x ⊓ (y ⊓ z) ≤ z
      apply inf_le_of_right_le
      exact inf_le_right

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

end My3

namespace My4

variable {α : Type*} [Lattice α]
variable (x y z : α)

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

end My4

namespace My5

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

-- x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z

--                    (a ⊔ b) ⊓ (a ⊔ c) ≤ a ⊔ (b ⊓ c)
--                    (x ⊔ y) ⊓ (x ⊔ z)

-- distributive lattice
-- 1) x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)
-- 2) x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)

-- TODO: Показать, что не всякая решётка дистрибутивна
-- by providing an explicit description of a nondistributive lattice with finitely many elements.

-- В задаче ниже нужно показать, что эти дистрибувности друг из друга следуют.
-- Короче показать, что верно "туда-сюда".

end My5

namespace My6

variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
        : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  apply le_antisymm
  · apply le_inf
    · show a ⊔ (b ⊓ c) ≤ a ⊔ b
      apply sup_le
      · exact le_sup_left
      · show b ⊓ c ≤ a ⊔ b
        exact inf_right_le_sup_left
    · apply sup_le
      · exact le_sup_left
      · show b ⊓ c ≤ a ⊔ c
        exact inf_left_le_sup_left
  · show (a ⊔ b) ⊓ (a ⊔ c) ≤ a ⊔ (b ⊓ c)
    -- rw [sup_inf_left]
    -- rw [inf_sup_right] at h
    sorry

    -- надо присоединить c помощью le_sup_left, le_sup_right
    -- что-то справа и тогда я смогу применить гипотезу h,
    -- переписать справа-налево цель.
    -- как присоединить? это же не равенство, ты не перепишешь.
    -- как превратить в равенство?
    -- анти-антисимметрия - симметрия?

    -- (a ⊓ b) ⊔ (c ⊓ a)

    -- apply inf_le_of_right_le
    -- show a ⊔ c ≤ a ⊔ (b ⊓ c)
    -- apply le_sup_of_le_right
    -- simp only [le_inf_iff, sup_le_iff, le_refl, and_true]

#check (eq_of_le_of_ge : a ≤ b → b ≤ a → a = b)
-- #check (sup_comm : a ⊔ b = b ⊔ a)

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
        : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  -- rw [sup_inf_left] at h
  --       ^^^^^^
  -- Так нельзя переписать потому, что мы работаем с обычными,
  -- а не с дистрибутивными решётками.
  sorry

-- Вернуться сюда позже.
-- Читай внимательно описание задачи. Мне не ясна формулировка и
-- не понятно чего от меня хочет автор.
end My6

namespace My7

-- Можно комбинировать аксиоматические структуры (наборы аксиом).
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  sorry

example (h : 0 ≤ b - a) : a ≤ b := by
  sorry

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  sorry

end My7

namespace My8

variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  sorry

-- Автор рекомендует использовать эту теорему:
#check nonneg_of_mul_nonneg_left

end My8
