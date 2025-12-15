import Mathlib

-- 3.2. Квантор существования.

namespace My1

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  -- C помощью тактики use предъявляем конкретный объект.
  use 5 / 2
  show (2 < 5/2) ∧ (5/2 < 3)
  -- Нормализует (вычисляет) числовое выражение,
  -- которое в нашем случае сводится к True ∧ True.
  norm_num

-- Тактика use умеет принимать доказательства вместе с объектом.
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h1 : 2 < (5:ℝ)/2 := by norm_num
  have h2 : (5:ℝ)/2 < 3 := by norm_num
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
-- для f верхней гранью является числo a,
-- для g верхней гранью является числo b,
-- то верхней гранью ф-ции h x ↦ f x + g x будет число a + b.

theorem fnUb_add (hfa : FnUb f a) (hgb : FnUb g b)
  : FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

-- Можно использовать fnUb_add, чтобы доказать что если f и g есть
-- верхние грани, то и у их суммы существует верхняя грань.

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb (fun x ↦ f x + g x) := by
  -- С помощью rcases мы распаковываем квантор существования,
  -- достаём из него a, для которой верно утверждение ha,
  -- ну и само утверждение ha тоже достаём.
  rcases ubf with ⟨a, ha⟩
  -- ^ Это аналогично использованию obtain:
  -- obtain ⟨a, ha⟩ := ubf
  rcases ubg with ⟨b, hb⟩
  use a + b
  unfold FnUb
  unfold FnUb at ha hb
  dsimp
  show ∀ (x : ℝ), f x + g x ≤ a + b
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
  use a + b
  unfold FnLb; dsimp
  unfold FnLb at ha hb
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
  unfold FnUb at ha; unfold FnHasUb
  unfold FnUb; dsimp
  use c * a
  intro x
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

-- А тактика rintro это intro + rcases.
example : FnHasUb f → FnHasUb g → FnHasUb (fun x ↦ f x + g x) := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩

-- Можно мэтчить аргументы.
example : FnHasUb f → FnHasUb g → FnHasUb (fun x ↦ f x + g x) :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩


end My3
