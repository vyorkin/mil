import Mathlib

-- 3.4. Конъюнкция и "туда-сюда".

namespace My1

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  -- rw доказывает цель используя рефлексивность ≤
  rw [h]
  -- calc y ≤ x := by rw [h]

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  · intro h
    apply h₁
    show y ≤ x
    rw [le_iff_lt_or_eq] -- (y ≤ x) ↔ (y < x) ∨ (y = x)
    rw [h]
    right
    rfl

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

-- Вот это интересное доказательство, обрати внимание.
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  ⟨h₀, h⟩

end My1

namespace My2

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : (x ≤ y ∧ x ≠ y) → ¬(y ≤ x) := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : (x ≤ y ∧ x ≠ y) → ¬(y ≤ x) :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬(y ≤ x) := by
  -- В отличии от rcases это оставит гипотезу h в контексте.
  have ⟨h₀, h₁⟩ := h
  -- ^ Похоже это (полностью?) аналогично:
  -- obtain ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁

-- Ну и паттерн-матчинг у нас есть:

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
      contrapose! h₁
      exact le_antisymm h₀ h₁

-- And.left / And.right

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  apply h.right
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')

-- Упражнение.
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  constructor
  · exact h.left
  · contrapose! h
    intro h'
    exact dvd_antisymm h' h -- m ∣ n → n ∣ m → m = n

end My2

namespace My3

example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5/2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, (x < z) ∧ (z < y)) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, (x < z) ∧ (z < y)) → x < y :=
  fun ⟨z, xltz, zlty⟩ ↦ lt_trans xltz zlty

end My3

namespace My4

example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5/2
  constructor <;> norm_num

example : ∃ m n : ℕ,
  (4 < m) ∧ (m < n) ∧ (n < 10) ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

end My4
