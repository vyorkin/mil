import Mathlib

-- 3.2. Квантор существования.

namespace My1

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  -- C помощью тактики use предъявляем конкретный объект.
  use 5/2
  show (2 < 5/2) ∧ (5/2 < 3)
  -- Нормализует (вычисляет) числовое выражение,
  -- которое в нашем случае сводится к True ∧ True.
  norm_num

-- Тактика use умеет принимать доказательства вместе с объектом.
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h1 : 2 < (5:ℝ)/2 := by norm_num
  have h2 : (5:ℝ)/2 < 3 := by norm_num
  -- ^ Тут нам приходится аннотировать тип, тк Lean не может его вывести.
  use 5/2, h1, h2

-- Тактика use пытается использовать все доступные в контексте гипотезы.
-- Здесь мы напрямую конструируем пруф-терм, не переходя в тактик-мод.
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  have h : 2 < (5:ℝ)/2 ∧ (5:ℝ)/2 < 3 := by norm_num
  ⟨5/2, h⟩

-- Проще можно было бы написать так.
example : ∃ x : ℝ, 2 < x ∧ x < 3 := ⟨5/2, by norm_num⟩

end My1

namespace My2

-- Функция ограничена сверху/снизу числом a.
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

-- У функции существует (хотя бы одна) верхняя/нижняя грань.
def FnHasUb (f : ℝ → ℝ) := ∃ a, FnUb f a
def FnHasLb (f : ℝ → ℝ) := ∃ a, FnLb f a

--

variable {f g : ℝ → ℝ}
variable {a b c : ℝ}

-- Если
-- (hfa) числo a является верхней гранью для f,
-- (hgb) числo b является верхней гранью для g,
-- то верхней гранью ф-ции h x ↦ f x + g x будет число a + b.

theorem fnUb_add (hfa : FnUb f a) (hgb : FnUb g b)
  : FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

-- Можно использовать fnUb_add, чтобы доказать что если у f и g есть
-- верхние грани, то и у их суммы существует верхняя грань.

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb (fun x ↦ f x + g x) := by
  -- С помощью rcases мы распаковываем квантор существования,
  -- достаём из него a, для которой верно утверждение ha,
  -- ну и само утверждение ha тоже достаём.
  rcases ubf with ⟨a, ha⟩
  -- ^ Это аналогично использованию obtain или have:
  -- obtain ⟨a, ha⟩ := ubf
  -- have   ⟨a, ha⟩ := ubf
  rcases ubg with ⟨b, hb⟩
  -- unfold FnUb at ha hb
  unfold FnHasUb FnUb; dsimp
  use a + b
  show ∀ (x : ℝ), f x + g x ≤ a + b
  -- (ha : FnUb f a) (hb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b)
  --       ^             ^
  --       Как раз эти гипотезы у нас есть в контексте.
  apply fnUb_add ha hb

-- Более кратко и менее наглядно:
theorem exFnUb_add (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb (fun x ↦ f x + g x) := by
  rcases ubf with ⟨a, ha⟩
  rcases ubg with ⟨b, hb⟩
  use a + b
  apply fnUb_add ha hb

-- Упражнения.

#check add_le_add -- : (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d

theorem fnLb_add (hfa : FnLb f a) (hgb : FnLb g b)
  : FnLb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  rcases lbf with ⟨a, ha⟩
  rcases lbg with ⟨b, hb⟩
  unfold FnLb at ha hb; unfold FnHasLb FnLb; dsimp
  use a + b
  show ∀ (x : ℝ), a + b ≤ f x + g x
  apply fnLb_add ha hb

theorem exFnLb_add (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  rcases lbf with ⟨a, ha⟩; rcases lbg with ⟨b, hb⟩
  use a + b; apply fnLb_add ha hb

#check mul_right_inj        -- : (a * b = a * c) ↔ b = c
#check mul_right_cancel     -- : (a * b = c * b) → a = c
#check mul_right_cancel_iff -- : (b * a = c * a) ↔ b = c

#check mul_left_cancel      -- : (a * b = a * c) → b = c
#check mul_left_cancel₀     -- : (ha : a ≠ 0)
--                               (h : a * b = a * c) : b = c

-- Моя неудачная попытка.
example (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb (fun x ↦ c * f x) := by
  rcases ubf with ⟨a, ha⟩
  unfold FnUb at ha; unfold FnHasUb
  -- Момент когда я свернул не туда.
  -- Это бессмысленно, тк тут я говорю, что такой верхней гранью будет число a,
  -- но интуитивно понятно, что для эта функция ограничена сверху числом c * a.
  use a
  -- Если бы я раскрыл определение чуть раньше, то
  -- было бы больше шансов заметить как можно получить
  -- два произведения с двух сторон неравенства, про которое у нас уже
  -- были задачи и тогда я возможно смог найти соответствующую теорему.
  unfold FnUb; dsimp
  show ∀ (x : ℝ), c * f x ≤ a

  -- intro x; replace ha := ha c
  -- rw [← mul_one a]
  -- apply mul_le_mul

  -- intro x; replace ha := ha x
  -- show c * f x ≤ a
  -- rw [← mul_one a]
  -- show c * f x ≤ a * 1
  -- apply mul_le_mul

  sorry

-- Ошибки:
-- 1. Разворачивай определения как можно раньше, это повышает шансы заметить паттерн.
-- 2. В use можно и нужно использовать алгебраические выражения,
--    а не только переменные из контекста.
-- 3. Ищи подходящие теоремы, ищи лучше.

-- Работа над ошибками.
example (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb (fun x ↦ c * f x) := by
  rcases ubf with ⟨a, ha⟩
  unfold FnUb at ha; unfold FnHasUb FnUb; dsimp
  use c * a
  intro x
  -- (h : b ≤ c) (a0 : 0 ≤ a) : a * b ≤ a * c
  apply mul_le_mul_of_nonneg_left
  · exact ha x
  · assumption

-- Доказательство автора.
example (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb (fun x ↦ c * f x) := by
  rcases ubf with ⟨a, ubfa⟩
  use c * a
  intro x
  exact mul_le_mul_of_nonneg_left (ubfa x) h

end My2

-- Эти определения ещё нам пригодятся.
export My2 (FnUb FnLb FnHasUb FnHasLb fnUb_add)

namespace My3

-- Тактика rcases позволяет рекурсивно распаковывать всякие
-- определения и выражения, именно поэтому "эр"-кейсэс (r - recursive).

-- Тактика rintro = intro + rcases.
example : FnHasUb f → FnHasUb g → FnHasUb (fun x ↦ f x + g x) := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

-- Можно мэтчить аргументы. Эквивалетно rintro.
example : FnHasUb f → FnHasUb g → FnHasUb (fun x ↦ f x + g x) :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩

-- obtain

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb (fun x ↦ f x + g x) := by
  obtain ⟨a, ubfa⟩ := ubf -- rcases ubf with ⟨a, ubfa⟩
  obtain ⟨b, ubgb⟩ := ubg -- rcases ubg with ⟨b, ubgb⟩
  -- ^ Тут использование obtain эквивалетно использованию have:
  -- have ⟨a, ubfa⟩ := ubf
  -- have ⟨b, ubgb⟩ := ubg
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  -- Здесь intro это название кейса (имя конструктора квантора существования).
  -- Тактика case задаёт имена для только что введённых в контекст термов: a ubfa.
  case intro a ubfa =>
    cases ubg
    case intro b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  -- Тактика next позволяет не писать конструктор intro и задаёт имена для
  -- только что введённых в контекст термов a ubfa (аналогично case).
  next a ubfa =>
    cases ubg
    next b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  match ubf, ubg with
  | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
    exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
  match ubf, ubg with
  | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
    ⟨a + b, fnUb_add ubfa ubgb⟩

end My3

namespace My4

variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) := ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
  SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  unfold SumOfSquares
  use a * c - b * d, a * d + b * c
  ring

-- Мы будем довольно часто распаковывать квантор сущ. и использовать
-- утверждение внутри него, чтобы переписывать цель (гипотезы в контексте).
-- Поэтому проще использовать следующий шорткат с rfl.

theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
  SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩ -- rfl сразу переписывает цель утверждением xeq из ∃ a b, xeq
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring

section
variable {a b c : ℕ}

-- Кванторы существования, как и кванторы всеобщности
-- спрятаны всюду за определениями. Умей их видеть.

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq⟩
  rcases divbc with ⟨e, ceq⟩
  -- Не всегда сразу понятно как развернуть определение, скрытое за нотацией.
  -- Например, тут нужно разворачивать сразу два определения:
  unfold Dvd.dvd Nat.instDvd; dsimp
  rw [ceq, beq]
  use d * e
  ring

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, rfl⟩; rcases divbc with ⟨e, rfl⟩
  use d * e; ring

-- Упражнение.

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨d, rfl⟩;
  rcases divac with ⟨e, rfl⟩
  use d + e
  ring

end

end My4

namespace My5

open Function

-- Функция f : α → β называется сюрьективной, если ∀ b, ∃ a, f a = b.

-- def Surjective (f : α → β) : Prop :=
--   ∀ b, ∃ a, f a = b

example {c : ℝ} : Surjective (fun x ↦ x + c) := by
  unfold Surjective; dsimp; intro b
  use b - c
  ring

#check mul_div_cancel₀ -- (a : G₀) (hb : b ≠ 0) : b * (a / b) = a

-- Упражнение.
example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  unfold Surjective; intro b; dsimp
  use b / c
  rw [mul_div_cancel₀]
  assumption -- exact h

end My5

namespace My6

-- В примере ниже тактика ring не справится самостоятельно.
-- Мы используем field_simp, которая помогает избавиться от знаменателей.

example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]
  ring

open Function

example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  unfold Surjective at h
  rcases h 2 with ⟨x, hx⟩ -- obtain ⟨x, hx⟩ := h 2
  use x
  rw [hx]
  norm_num

end My6

namespace My7

open Function

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  unfold Surjective at surjg surjf
  intro c
  dsimp
  rcases surjg c with ⟨b, hb⟩
  rcases surjf b with ⟨a, ha⟩
  use a
  rw [ha]
  assumption -- exact hb

end My7
