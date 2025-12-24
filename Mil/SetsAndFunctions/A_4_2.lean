import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- 4.2. Функции.

namespace My1

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

-- Если у нас есть функция (f : α → β) и (s : Set β) - образ функции, то
-- f ⁻¹' s := preimage f s := { x | f x ∈ s } - проoбраз (обратный образ) этой функции.
--
-- Выражение x ∈ f ⁻¹' s это тоже, что и f x ∈ s.

-- Короче прообраз (обратный образ) функции это множество всех элементов
-- области определения функции (Set α), которые отображаются в (Set β).
--
-- https://ru.wikipedia.org/wiki/%D0%9E%D0%B1%D1%80%D0%B0%D0%B7_(%D0%BC%D0%B0%D1%82%D0%B5%D0%BC%D0%B0%D1%82%D0%B8%D0%BA%D0%B0)

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext x
  rfl

-- Образ функции f:
-- image f s = f '' s := { y | ∃ x, x ∈ s ∧ f x = y }.
--
-- Поэтому гипотезу образа можно распаковать так:
-- y ∈ ⟨ev_x, x_in_s, fx_eq_y⟩.

-- Дистрибутивность образа.
--
-- Более подробное док-во, чем в книге, чтобы можно было
-- наглядно посмотреть что происходит на каждом шаге.
example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y
  constructor
  · intro h
    unfold image at h
    obtain ⟨x, h', heq⟩ := h
    rw [← heq]
    rcases h' with xs | xt
    · show f x ∈ f '' s ∪ f '' t
      left
      unfold image
      use x, xs
      -- ^ Делает следующее:
      -- f x ∈ {x | ∃ x ∈ s, f x = x}
      -- f x ∈ {x | f x = x}
    · show f x ∈ f '' s ∪ f '' t
      right
      use x, xt
  · intro h
    -- Сразу переписываем с помощью последнего уравнения
    -- из тройки, используя тактику rfl.
    rcases h with ⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩
    · --          { y | ∃ x, x ∈ s ∧ f x = y }
      --          ----------------------------
      --                      ^^^
      use x -- Раскрывает определение образа.
      exact ⟨Or.inl xs, rfl⟩
    · use x
      exact ⟨Or.inr xt, rfl⟩

-- Оригинальный пример из книги.
example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y
  constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    · right
      use x, xt
  · rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
    · use x, Or.inl xs
    · use x, Or.inr xt

-- Эта лемма позвляет тебе построить образ.
-- Если у тебя есть это:
-- (f : α → β) {s : Set α} {x : α} (h : x ∈ s)
-- то применяя эту лемму ты получишь f '' s:
-- f x ∈ f '' s := f x ∈ { y | ∃ x, x ∈ s ∧ f x = y }
#check mem_image_of_mem -- Конструктор образа ф-ции.

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs -- Раскрывает определение подмножества.
  show x ∈ f ⁻¹' (f '' s)
  -- f ⁻¹' s = { x | f x ∈ s }
  -- f  '' s = { y | ∃ x, x ∈ s ∧ f x = y }
  -- use x, xs
  apply mem_image_of_mem f xs

-- Упражнение.
--
-- Это упражнение требует уметь строить
-- образ из следующих 2-х фактов: f : α → β и x ∈ s.
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    unfold image at h
    -- s ⊆ t := ∀ x ∈ s, x ∈ t
    --
    -- Надо сконструировать вот это:
    -- x ∈ {x | ∃ a ∈ s, f a = x}
    -- Тогда получим это:
    -- f x ∈ v
    --
    -- f ⁻¹' v = { x | f x ∈ v }
    --
    -- Почему не справился:
    -- Я не разобрался как строить образ.
    sorry
  · sorry

-- Образ и прообраз (f '' s и f ⁻¹' t) являются примером соответствия Галуа
-- между 2 множествами, где частичный порядок это отношение включения.
#check image_subset_iff -- f '' s ⊆ t ↔ s ⊆ f ⁻¹' t

-- Доказательство автора.
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h x xs
    have img : f x ∈ f '' s := mem_image_of_mem f xs
    exact h img
  · intro h y ymem
    -- f '' s = { y | ∃ x, x ∈ s ∧ f x = y }
    rcases ymem with ⟨x, xs, fxeq⟩
    rw [← fxeq]
    simp only [preimage, subset_def] at h
    -- h : ∀ x ∈ s, x ∈ {x | f x ∈ v}
    --                           ^
    show f x ∈ v -- Совпадают хвосты.
    apply h
    exact xs

end My1

namespace My2

variable {α β : Type*}
variable (f : α → β)

variable (s t : Set α)
variable (u v : Set β)

open Set
open Function

-- Упражнения.

  -- f ⁻¹' s = { x | f x ∈ s }
  -- f  '' s = { y | ∃ x, x ∈ s ∧ f x = y }

-- 1.a.
example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  simp only [subset_def]
  intro x h'
  unfold image preimage at h'
  obtain ⟨y, ys, heq⟩ := h'
  unfold Injective at h
  have hyx := @h y x heq
  rw [← hyx]
  exact ys

-- 1.b.
example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, ys, fxeq⟩
  rw [← h fxeq]
  exact ys

-- 2.a.
example : f '' (f ⁻¹' u) ⊆ u := by
  rintro x ⟨y, hy, hyeqx⟩
  rw [← hyeqx]
  exact hy

-- 3.a.
example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  unfold Surjective at h
  simp only [subset_def]
  intro b hbu
  obtain ⟨a, ha⟩ := h b
  use a
  constructor
  · unfold preimage
    rw [← ha] at hbu
    exact hbu
  · assumption

-- 4.a.
example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro x ⟨y, hy, hyeq⟩
  exact ⟨y, h hy, hyeq⟩

-- 5.a.
example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x h'
  exact h h'

-- 6.a.
example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  · rintro (h' | h')
    · left; assumption
    · right; assumption
  · rintro (h' | h')
    · left; assumption
    · right; assumption

-- 6.b.
example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor <;>
  · rintro (h' | h')
    · left; assumption
    · right; assumption

-- 7.a.
example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro x ⟨y, ⟨hys, hyt⟩, hyeq⟩
  unfold image
  exact ⟨⟨y, hys, hyeq⟩, ⟨y, hyt, hyeq⟩⟩

-- 8.a.
example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  unfold Injective at h
  rintro x ⟨⟨y, hys, hyeq⟩, ⟨z, hzs, hzeq⟩⟩
  unfold image
  rw [← hyeq] at hzeq
  show x ∈ {x | ∃ a ∈ s ∩ t, f a = x}
  rw [h hzeq] at hzs
  use y
  constructor
  · exact ⟨hys, hzs⟩
  · exact hyeq

-- 8.b.
-- Можно тоже самое сделать в 3 строчки.
example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro x ⟨⟨y, hys, rfl⟩, ⟨z, hzs, hzeq⟩⟩
  rw [h hzeq] at hzs
  exists y

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry

end My2

namespace My3

variable {α β : Type*} {I : Type*}
variable (A : I → Set α) (B : I → Set β)
variable (f : α → β)

open Set
open Function

-- Упражнения.

#check mem_iUnion -- (x ∈ ⋃ i, s i) ↔ (∃ i, x ∈ s i)

 -- (f : α → β) (s : Set α) (y : β) :
 -- y ∈ f '' s ↔ ∃ x ∈ s, f x = y
#check mem_image

-- 1.a. Неудачная попытка.
example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext x
  constructor
  · rintro ⟨y, hy, hyeq⟩
    unfold image
    obtain ⟨i, hyAi⟩ := mem_iUnion.mp hy
    rw [mem_iUnion]
    use i
    exact ⟨y, hyAi, hyeq⟩
  · intro h
    obtain ⟨i, hxAi⟩ := mem_iUnion.mp h
    have a := A i
    have b := B i
    rw [mem_image] at hxAi
    unfold image at *
    simp
    sorry

-- 1.b. Моё доказательство.
example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  show y ∈ f '' ⋃ i, A i ↔ y ∈ ⋃ i, f '' A i
  unfold image at *
  show y ∈ { x | ∃ a ∈ ⋃ i, A i, f a = x } ↔ y ∈ ⋃ i, { x | ∃ a ∈ A i, f a = x }
  simp
  show (∃ x, (∃ i, x ∈ A i) ∧ f x = y) ↔ ∃ i, ∃ x ∈ A i, f x = y
  constructor
  · show (∃ x, (∃ i, x ∈ A i) ∧ f x = y) → ∃ i, ∃ x ∈ A i, f x = y
    rintro ⟨x, ⟨i, hxAi⟩, hfxeqy⟩
    use i
    use x
  · show (∃ i, ∃ x ∈ A i, f x = y) → ∃ x, (∃ i, x ∈ A i) ∧ f x = y
    rintro ⟨i, ⟨x, hxAi, hfxeqy⟩⟩
    use x
    constructor
    · use i
    · exact hfxeqy

-- 1.c. Доказательство автора.
example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; simp
  constructor
  · rintro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i, x
  · rintro ⟨i, x, xAi, fxeq⟩
    exact ⟨x, ⟨i, xAi⟩, fxeq⟩

-- 2.a.
example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro b; simp
  rintro a hai haeqb i
  use a
  constructor
  · exact hai i
  · assumption

-- 3.a.
example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro b; simp
  intro h
  obtain ⟨a, ⟨haAi, hfaeqb⟩⟩ := h i
  show ∃ x, ((∀ (i : I), x ∈ A i) ∧ f x = b)
  use a
  constructor
  · intro i'
    obtain ⟨c, ⟨hcAi, hfceqb⟩⟩ := h i'
    rw [← hfaeqb] at hfceqb
    have haeqb := injf hfceqb
    rw [← haeqb]
    assumption
  · assumption

-- 3.b.
example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro b; simp
  intro h
  obtain ⟨a, ⟨haAi, hfaeqb⟩⟩ := h i
  use a
  constructor
  · intro i'
    obtain ⟨c, ⟨hcAi, hfceqb⟩⟩ := h i'
    rw [← hfaeqb] at hfceqb
    rw [← injf hfceqb]
    assumption
  · assumption

-- 4.a.
example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  sorry

-- 5.a.
example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  sorry

end My3

namespace My4

variable {α β : Type*}
variable (s : Set α) (t : Set β)
variable (f : α → β)

open Set
open Real
open Function

-- The statement `Injective f` is provably equivalent to `InjOn f univ`:
--
-- def InjOn (f : α → β) (s : Set α) : Prop :=
--   ∀ ⦃x₁ : α⦄, x₁ ∈ s → ∀ ⦃x₂ : α⦄, x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂
--
-- def Injective (f : α → β) : Prop :=
--   ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

-- InjOn f s - "f is injective on s ".
example : InjOn f s ↔ (∀ x₁ ∈ s, (∀ x₂ ∈ s, (f x₁ = f x₂) → x₁ = x₂)) :=
  Iff.refl _

-- exp x — это экспонента, то есть e^x , где e — основание натуральных логарифмов.

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  show (log x = log y) → x = y
  intro h
  calc
    x = exp (log x) := by rw [exp_log xpos] -- exp (log x) = x
    _ = exp (log y) := by rw [h]
    _ = y := by rw [exp_log ypos]

-- range f is provably equal to f '' univ.
-- Определение range f это почти тоже самое, что образ f:
-- range f            := { y | ∃ x,         f x = y }
-- image f s = f '' s := { y | ∃ x, x ∈ s ∧ f x = y }
-- Но range не требует x ∈ s, и не требует от ι (йота) чтобы он был типом из Type.
-- Йопта (ι) может быть любым Sort* как видно из определения range:
-- variable {ι : Sort*} {f : ι → α}

#check exp_pos -- (x : ℝ) : 0 < rexp x

example : range exp = { y | y > 0 } := by
  ext y
  unfold range
  constructor
  · rintro ⟨x, hexp⟩
    rw [← hexp]
    show rexp x ∈ {y | y > 0}
    apply exp_pos
  · intro ypos
    use (log y)
    rw [exp_log ypos]

-- Упражнения.

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xpos y ypos
  show √x = √y → x = y
  intro h
  show x = y
  calc
    x = √x * √x := by rw [mul_self_sqrt xpos]
    _ = √y * √y := by rw [h]
    _ = y := by rw [mul_self_sqrt ypos]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by sorry

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by sorry

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by sorry

end My4
