import Mathlib

-- 3.5. Дизъюнкция.

namespace My1

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  have hx : x ^ 2 ≥ 0 := pow_two_nonneg x -- (a : R) : 0 ≤ a ^ 2
  linarith [hx]
  -- ^ То же самое можно было бы сделать без введения вспомогательной
  -- гипотезы - сразу "инлайн", как в примере ниже.

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 := Or.inl h
example (h : y < -1) : y > 0 ∨ y < -1 := Or.inr h

example : x < |y| → (x < y ∨ x < -y) := by
  -- Знакомься - второй "режим работы" тактики rcases:
  --      le_or_gt :                  (a b : α) a ≤ b ∨ b < a
  rcases (le_or_gt 0 y) with h | h -- (0 y : α) 0 ≤ y ∨ y < 0
  -- Автор рассматривает эти 2 неравенства 0 ≤ y и y < 0, чтобы
  -- воспользоваться соответствующими теоремами про модуль числа и
  -- избавиться от модуля.
  · rw [abs_of_nonneg h] -- (h : 0 ≤ a) : |a| = a
    show x < y → (x < y ∨ x < -y)
    intro h
    left
    exact h
  · rw [abs_of_neg h] -- |a| = -a
    intro h
    right
    exact h

-- В случае "или" лучше (?) использовать cases:
-- 1. Кейсы имеют название, соответствующее конструктору.
-- 2. Гипотеза вводится ближе к месту использования.
-- 3. Кейсы можно доказывать в любом порядке.
--
-- Тогда возникает вопрос: почему автор предпочитает rcases h with h' | h'.

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

-- Если тебе пофиг в каком порядке доказывать кейсы, то
-- используй тактику next.

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

-- Паттерн-матчинг тоже работает.

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
  | Or.inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  | Or.inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

-- В этой книге мы обычно будет использовать rcases для дизъюнкций.

end My1

namespace MyAbs

#check le_or_gt -- (a b : α) : a ≤ b ∨ b < a

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]; linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]; linarith
  · rw [abs_of_neg h]

-- #check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
-- #check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)

-- Моё доказательство.
theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    rcases le_or_gt 0 x with h₁ | h₁
    · rw [abs_of_nonneg h₁]
      apply add_le_add_left
      apply le_abs_self
    · rw [abs_of_neg h₁]
      rcases le_or_gt 0 y with h₂ | h₂
      · rw [abs_of_nonneg h₂]
        apply add_le_add_right
        linarith
      · rw [abs_of_neg h₂]; linarith
  · rw [abs_of_neg h]
    rcases le_or_gt 0 y with h₁ | h₁
    · rw [abs_of_nonneg h₁]
      rcases le_or_gt 0 x with h₂ | h₂
      · rw [abs_of_nonneg h₂]; linarith
      · rw [abs_of_neg h₂]; linarith
    · rw [abs_of_neg h₁]
      rcases le_or_gt 0 x with h₂ | h₂
      · rw [abs_of_nonneg h₂]; linarith
      · rw [abs_of_neg h₂]; linarith

-- Доказательство автора.
theorem abs_add' (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    linarith [le_abs_self x, le_abs_self y]
  · rw [abs_of_neg h]
    linarith [neg_le_abs_self x, neg_le_abs_self y]

-- Я опять не догадался, что можно было ещё почти в самом начале
-- воспользоваться linarith и дать ей две доказанные выше теоремы.
-- Она бы справилась, но почему и как именно она справляется для меня не очевидно,
-- поэтому я её и недооцениваю.

-- Ещё упражнения.

#check lt_iff_le_not_ge -- a < b ↔ (a ≤ b ∧ ¬b ≤ a)
#check abs_choice -- (x : α) : |x| = x ∨ |x| = -x

-- Моё доказательство.
theorem lt_abs : x < |y| ↔ (x < y ∨ x < -y) := by
  constructor
  -- Как позже выяснилось, можно было обойтись без abs_choice
  -- и без множественных переписываний по гипотезе hy.
  · rcases abs_choice y with hy | hy
    · intro hxy
      rw [hy] at hxy
      left
      exact hxy
    · intro hxy
      rw [hy] at hxy
      right
      exact hxy
  · intro h
    rcases h with hy | hy
    · rcases le_or_gt 0 y with h | h
      · rw [abs_of_nonneg h]
        exact hy
      · rw [abs_of_neg h]
        linarith
    · rcases le_or_gt 0 y with h | h
      · rw [abs_of_nonneg h]
        linarith
      · rw [abs_of_neg h]
        exact hy

-- Доказательство автора.
theorem lt_abs' : x < |y| ↔ (x < y ∨ x < -y) := by
  -- Заметь как он начинает не с разбиения би-импликации, а
  -- с введение гипотез о двух неравенствах: 0 ≤ y и y < 0.
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h] -- (h : 0 ≤ a) : |a| = a
    constructor
    · intro h'
      left
      exact h'
    · intro h'
      rcases h' with h' | h'
      · exact h'
      · linarith
  rw [abs_of_neg h]
  constructor
  · intro h'
    right
    exact h'
  · intro h'
    rcases h' with h' | h'
    · linarith
    · exact h'

-- Моё доказательство.
theorem abs_lt : |x| < y ↔ (-y < x ∧ x < y) := by
  constructor
  · rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
      intro h'
      constructor
      · linarith
      · exact h'
    · rw [abs_of_neg h]
      intro h'
      constructor <;> linarith
  · rcases le_or_gt 0 x with h | h
    · rw [abs_of_nonneg h]
      intros; linarith
    · rw [abs_of_neg h]
      intros; linarith

-- Доказательство автора.
theorem abs_lt' : |x| < y ↔ -y < x ∧ x < y := by
  -- Он начинает со снятия модуля раскидкой по кейсами.
  -- Это позволяем ему не пользоваться 4 раза парой теорем про модуль.
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    constructor
    · intro h'
      constructor
      · linarith
      exact h'
    · intro h'
      rcases h' with ⟨h1, h2⟩
      exact h2
  · rw [abs_of_neg h]
    constructor
    · intro h'
      constructor
      · linarith
      · linarith
    · intro h'
      linarith

end MyAbs

namespace My2

-- Тактики rcases и rintro можно использовать с вложенными дизъюнкциями.

#check lt_trichotomy -- (a b : α) : (a < b) ∨ (a = b) ∨ (b < a)

-- Для rcases вариантов может быть больше двух, как в следующем примере.
example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right
    exact xgt

variable (m n k : ℕ)

-- Вложенный дестракчеринг и переписывание с rfl работает и для дизъюнкций.
example (h : (m ∣ n) ∨ (m ∣ k)) : m ∣ n * k := by
  -- Иногда лучше использовать simp only вместо unfold.
  simp only [Dvd.dvd] at *
  -- rcases h with ⟨a, h₀⟩ | ⟨b, h₁⟩
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    -- apply dvd_mul_right
    -- exact dvd_mul_right _ _
    exact dvd_mul_right m (a * k) -- (a b : α) : a ∣ a * b
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

end My2

namespace My3

variable (x y z : ℝ)

-- Упражнения.

-- Сможешь ли ты это доказать в одну строчку?
-- Используй rcases чтобы распаковать гипотезу и разбить её по кейсам.
-- Используй <;> и linarith для доказательства каждой ветки.
example (h : ∃ x y, (z = x ^ 2 + y ^ 2) ∨ (z = x ^ 2 + y ^ 2 + 1)) : z ≥ 0 := by
  rcases h with ⟨a, b, h | h⟩ <;> linarith [pow_two_nonneg a, pow_two_nonneg b]

-- Смог. В одну длинную строчку.

-- Для вещественных чисел существует следующий факт/теорема:

#check eq_zero_or_eq_zero_of_mul_eq_zero -- a * b = 0 → (a = 0 ∨ b = 0)

-- Область целостности (или целостное кольцо, или область цельности или просто область) —
-- понятие коммутативной алгебры: ассоциативное коммутативное кольцо без делителей нуля
-- (произведение никакой пары ненулевых элементов не равно 0).

-- https://en.wikipedia.org/wiki/Integral_domain
-- https://ru.wikipedia.org/wiki/%D0%9E%D0%B1%D0%BB%D0%B0%D1%81%D1%82%D1%8C_%D1%86%D0%B5%D0%BB%D0%BE%D1%81%D1%82%D0%BD%D0%BE%D1%81%D1%82%D0%B8

-- Используй его, чтобы доказать следующие 2 утверждения.

#check mul_one

-- Попытка 1.
example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  rw [sq] at h
  rw [← mul_one 1] at h
  rw [mul_self_inj_of_nonneg] at h
  · left
    exact h
  · rw [mul_one] at h
    sorry
  · linarith

-- Попытка 2.
example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  left
  rcases lt_trichotomy (x * x) 0 with xlt | xeq | xgt
  · linarith
  · rcases eq_zero_or_eq_zero_of_mul_eq_zero xeq with h' | h'
    · linarith
    · linarith
  · rw [← sq] at xgt
    -- ...
    sorry

-- До чего не догадался:
--
-- 1. Увидеть, что:
--      x ^ 2 = 1
--    ⇔ x ^ 2 - 1 ^ 2 = 0
--    ⇔ (x + 1) * (x - 1)
--    ⇒ x = 1 ∨ x = -1
--    ^ по предлагаемой теореме выше
--
-- 2. Или заметить, что:
--    (x = 1) ∨ (x = -1) ⇔ (x - 1 = 0) ∨ (x + 1 = 0)
--    И тут уже можно было бы доказывать обратным
--    рассуждением, тк у нас есть про это та самая теорема выше:
--    a * b = 0 → a = 0 ∨ b = 0

-- РНО:

#check sub_eq_zero_of_eq      -- : a = b → (a - b = 0)
#check pow_two_sub_pow_two    -- : a ^ 2 - b ^ 2 = (a + b) * (a - b)
#check add_eq_zero_iff_eq_neg -- : a + b = 0 ↔ a = -b

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h₀ : x ^ 2 - 1 = 0 := sub_eq_zero_of_eq h
  have h₁ : (x + 1) * (x - 1) = 0 := by
    rw [← mul_one 1, ← sq] at h₀
    rw [← pow_two_sub_pow_two]
    assumption
  -- (a * b = 0) → (a = 0) ∨ (b = 0)
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h₁ with h' | h'
  · right
    rw [add_eq_zero_iff_eq_neg] at h'
    assumption
  · left
    rw [sub_eq_zero] at h'
    assumption

-- Доказательство автора.
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h₀ : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h₁ : (x + 1) * (x - 1) = 0 := by
    rw [← h₀]
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h₁ with h' | h'
  · right
    exact eq_neg_iff_add_eq_zero.mpr h' -- a = -b ↔ (a + b = 0)
  · left
    exact eq_of_sub_eq_zero h' -- (h : a - b = 0) : a = b

-- Моё доказательство.
example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h₀ : x ^ 2 - y ^ 2 = 0 := sub_eq_zero_of_eq h
  have h₁ : (x + y) * (x - y) = 0 := by rw [← pow_two_sub_pow_two]; assumption
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h₁ with h' | h'
  · right
    rw [add_eq_zero_iff_eq_neg] at h'
    assumption
  · left
    rw [sub_eq_zero] at h'
    assumption

-- Доказательство автора.
example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring
  -- a * b = 0 → a = 0 ∨ b = 0
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

end My3

namespace My4

-- Элемент a является левым делителем нуля, если существует
-- ненулевой b такой, что ab = 0, и, соответственно,
-- правым делителем нуля, если существует ненулевой b,
-- при котором ba = 0.

-- Теорема eq_zero_or_eq_zero_of_mul_eq_zero говорит о том, что для
-- вещественных чисел (ℝ) не существует (не тривиальных) делителей нуля.
--
-- Коммутативное кольцо с таким свойством называется
-- областью целостности (integral domain).

-- Доказательства двух соответствующих теорем выше должны работать
-- и для области целостности R.

variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h₀ : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h₁ : (x + 1) * (x - 1) = 0 := by
    rw [← h₀]
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h₁ with h' | h'
  · right
    exact eq_neg_iff_add_eq_zero.mpr h' -- a = -b ↔ (a + b = 0)
  · left
    exact eq_of_sub_eq_zero h' -- (h : a - b = 0) : a = b

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring
  -- a * b = 0 → a = 0 ∨ b = 0
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

end My4

namespace My5

-- Исключённое третье.

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

-- Тактика by_cases h : P делает тоже самое, что и cases em P.
-- Только в отличии от cases em P, она позвляет дать название
-- гипотезе, которая будет включена в каждую ветку.
-- Если не указать своё имя, то линь назовёт эту гипотезу h.

example (P : Prop) : ¬¬ P → P := by
  intro h
  by_cases h' : P
  · assumption
  · contradiction

-- Упражнение.

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases h' : P
    · right
      exact h h'
    · left; assumption
  · intro h hp
    cases h
    · contradiction
    · assumption

end My5
