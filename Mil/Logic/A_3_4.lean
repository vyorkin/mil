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
  -- ^
  -- Ну типа в цели у нас "меньше или равно" (y < x ∨ y = x),
  -- а всё это "или" можно получить из правого его дизъюнкта (y = x),
  -- ну и если мы перепишем x = y, то получим y = y, a это rfl.

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  · intro h
    apply h₁
    show y ≤ x
    rw [le_iff_lt_or_eq] -- (y ≤ x) ↔ (y < x) ∨ (y = x)
    right
    rw [h]

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

example {x y : ℝ} : (x ≤ y ∧ x ≠ y) → (x ≤ y ∧ ¬y ≤ x) := by
  rintro ⟨h₀, h₁⟩
  -- Заметь, что use здесь доказывает левый конъюнкт и
  -- нам остаётся доказать правый
  use h₀
  show ¬y ≤ x
  exact fun h' ↦ h₁ (le_antisymm h₀ h')

end My4

namespace My5
  -- iff

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl -- rfl тут работает как rw,
    --            а rw доказывает "равно" в "меньше или равно".
    rfl
  · contrapose!
    exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩
  --                 ^ Конструирует неравенство

-- Упражнение.

example {x y : ℝ} : (x ≤ y ∧ ¬y ≤ x) ↔ (x ≤ y ∧ x ≠ y) := by
  constructor
  · rintro ⟨h₀, h₁⟩
    use h₀
    contrapose! h₁
    rw [h₁]
  · rintro ⟨h₀, h₁⟩
    use h₀
    contrapose! h₁
    exact le_antisymm h₀ h₁

-- Упражнение.

-- Предлагается доказать вспомогательную лемму, используя:
-- linarith, pow_two_nonneg, and pow_eq_zero.

#check pow_two_nonneg -- : 0 ≤ a ^ 2
#check pow_eq_zero    -- : a ^ n = 0 → a = 0

#check mul_self_add_mul_self_eq_zero -- a * a + b * b = 0 ↔ a = 0 ∧ b = 0

-- Моё доказательство.
theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by
    replace h : x*x + y*y = 0 := by linarith
    rw [mul_self_add_mul_self_eq_zero] at h
    replace h := h.left
    rw [← mul_self_eq_zero] at h
    rw [sq]
    assumption
  pow_eq_zero h'

#check aux -- (x ^ 2 + y ^ 2 = 0) -> x = 0

example (x y : ℝ) : (x ^ 2 + y ^ 2 = 0) ↔ (x = 0 ∧ y = 0) := by
  constructor
  · intro h
    have h₀ := @aux x y h
    rw [add_comm] at h
    have h₁ := @aux y x h
    exact ⟨h₀, h₁⟩
  -- · intro h
  --   rcases h with ⟨h₀, h₁⟩
  --   rw [h₀, h₁]
  -- ^ Эти 3 строчки выше эквивалетны вот этой одной:
  · rintro ⟨rfl, rfl⟩
    norm_num

theorem aux'' {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by
    have hx := pow_two_nonneg x
    have hy := pow_two_nonneg y
    linarith [hx, hy]
  pow_eq_zero h'

-- Доказательство автора.
theorem aux' {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  -- К сожалению я пока не настолько хорошо понимаю как
  -- тактика linarith способна доказывать такие цели.
  pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · exact aux' h
    · rw [add_comm] at h
      exact aux h
  · rintro ⟨rfl, rfl⟩ -- Это хороший трюк
    norm_num

end My5

namespace My6

example (x : ℝ) : |x + 3| < 5 → (-8 < x ∧ x < 2) := by
  rw [abs_lt] -- |a| < b ↔ -b < a ∧ a < b
  show ((-5 < x + 3) ∧ (x + 3 < 5)) → (-8 < x ∧ x < 2)
  intro h
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff] -- (k ∣ m.gcd n) ↔ (k ∣ m ∧ k ∣ n)
  constructor <;> norm_num

-- Упражнение.

-- Note that push_neg won’t unfold definitions for you,
-- so the rw [Monotone] in the proof of the theorem is needed

theorem not_monotone_iff {f : ℝ → ℝ}
  : ¬(Monotone f) ↔ (∃ x y, (x ≤ y) ∧ (f x > f y)) := by
  rw [Monotone]
  -- Аналогично:
  -- unfold Monotone
  push_neg
  rfl

-- Моё доказательство.
example : ¬Monotone fun x : ℝ ↦ -x := by
  unfold Monotone
  push_neg
  -- Не догадался использовать not_monotone_iff, хотя
  -- она была тебе дана сразу выше. Но моё полностью эквивалетно.
  use 0
  use 1
  norm_num

-- Доказательство автора.
example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [not_monotone_iff] -- ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y
  use 0, 1
  -- ^^^^^^ Вот так оказывается тоже можно
  norm_num

end My6

namespace My7

-- Partial Order ≤: transitive, reflexive, antisymmetric.
-- Preorder ≤:      transitive, reflexive.

-- Partial Order = Preorder + antisymmetry

variable {α : Type*} [PartialOrder α]
variable (a b c : α)

-- Для отношения предпорядка (≤) Lean аксиоматизирует
-- отношение строго предпорядка (<) через вот такое iff:
#check lt_iff_le_not_ge -- a < b ↔ a ≤ b ∧ ¬b ≤ a

example : a < b ↔ (a ≤ b ∧ ¬b ≤ a) := by
  rw [lt_iff_le_not_ge]

-- Упражнения.

example : ¬(a < a) := by
  rw [lt_iff_le_not_ge]
  push_neg
  exact id

-- Первое док-во.
example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_ge] -- a < b ↔ a ≤ b ∧ ¬b ≤ a
  show (a ≤ b ∧ ¬b ≤ a) → (b ≤ c ∧ ¬c ≤ b) → a ≤ c ∧ ¬c ≤ a
  rintro ⟨h₀, h₁⟩ ⟨h₂, h₃⟩
  show a ≤ c ∧ ¬c ≤ a
  constructor
  · exact le_trans h₀ h₂
  · contrapose! h₃
    show c ≤ b
    exact le_trans h₃ h₀

-- Без show и комментариев.
example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_ge]
  rintro ⟨h₀, h₁⟩ ⟨h₂, h₃⟩
  constructor
  · exact le_trans h₀ h₂
  · contrapose! h₃
    exact le_trans h₃ h₀

end My7
