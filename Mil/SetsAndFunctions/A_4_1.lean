import Mathlib
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic

-- 4.1. Множества.

namespace My1

variable {α : Type*}
variable (s t u : Set α)

open Set

#check subset_def -- s ⊆ t = ∀ x ∈ s, x ∈ t
#check inter_def -- s₁ ∩ s₂ = {a | a ∈ s₁ ∧ a ∈ s₂}

-- Это просто компактная запись того, что является элементом
-- множества для всех элементов которого выполняется утверждение p.
#check mem_setOf -- a ∈ {x | p x} ↔ p a

-- Пересечение.

#check mem_inter_iff -- (a b : Set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b

example (h : s ⊆ t) : (s ∩ u) ⊆ (t ∩ u) := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  have xs' := h x xs
  exact ⟨xs', xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

-- Объединение.

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

-- Упражнение.

-- 1.
example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) := by
  intro x h
  rcases h with h₁ | h₂
  · constructor
    · exact h₁.left
    · left; exact h₁.right
  · constructor
    · exact h₂.left
    · right; exact h₂.right

-- 2.
example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) := by
  intro x h
  rcases h with ⟨hs, ht⟩ | ⟨hs, hu⟩
  · exact ⟨hs, Or.inl ht⟩
  · exact ⟨hs, Or.inr hu⟩

end My1

namespace My2

variable {α : Type*}
variable (s t u : Set α)

open Set

-- Нотация вычитания множеств:
-- x ∈ s \ t = x ∈ s ∧ x ∉ t

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  · intro xtu
    rcases xtu with xt | xu
    · exact xnt xt
    · exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  -- Заметь как распаковывается вложенное вычитание множеств.
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

-- Упражнение.

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  constructor
  · use xs
    -- Нет, ты не может делать rcases на функции,
    -- коей и является отрицание чего-либо.
    -- unfold Not at xntu
    contrapose! xntu
    left; exact xntu
  · contrapose! xntu
    right; exact xntu

end My2

namespace My3

variable {α : Type*}
variable (s t u : Set α)

open Set

-- Равенство двух множеств определяется экстенсионально.

example : s ∩ t = t ∩ s := by
  ext x
  -- Мн-ва равны (экстенсионально), если каждый элемент
  -- одного мн-ва является элементом другого.
  show x ∈ s ∩ t ↔ x ∈ t ∩ s
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

#check Set.ext -- (h : ∀ (x : α), x ∈ a ↔ x ∈ b) : a = b

example : s ∩ t = t ∩ s := Set.ext fun _x ↦
  ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

-- Альтернативный способ доказать равенство это
-- использовать антисимметрию.

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

-- Упражнения.

example : s ∩ t = t ∩ s := Subset.antisymm
  (fun _x ⟨xs, xt⟩ ↦ ⟨xt, xs⟩)
  (fun _x ⟨xt, xs⟩ ↦ ⟨xs, xt⟩)

#check mem_inter_iff -- (a b : Set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b

-- 1.a. Экстенсиональность + тактика.
example : s ∩ (s ∪ t) = s := by
  ext x
  show x ∈ s ∩ (s ∪ t) ↔ x ∈ s
  simp only [mem_inter_iff]
  constructor
  · intro h
    exact h.left
  · intro h
    constructor
    · assumption
    · simp only [mem_union]
      exact Or.inl h

-- 1.b. Антисимметрия.
example : s ∩ (s ∪ t) = s := by
  apply Subset.antisymm
  · rintro x ⟨hxs, hsut⟩; assumption
  · intro x h
    constructor
    · assumption
    · left; assumption

-- 1.c. Прямое конструирование пруф-терма.
example : s ∩ (s ∪ t) = s :=
  Subset.antisymm
    (fun _ ⟨hxs, _⟩ => hxs)
    (fun _ h => ⟨h, Or.inl h⟩)

-- 2.a. Экстенсиональность + тактика.
-- Неплохо.
example : s ∪ s ∩ t = s := by
  ext x
  constructor
  · intro h
    rcases h with hxs | ⟨hxs, _⟩ <;> assumption
  · intro h
    exact Or.inl h

-- 2.b. Антисимметрия.
-- Хорошо.
example : s ∪ s ∩ t = s := by
  apply Subset.antisymm
  · intro x h
    rcases h with hxs | ⟨hxs, _⟩ <;> assumption
  · intro x h
    exact Or.inl h

-- 2.c. Прямое конструирование пруф-терма.
-- Тут прямое создание терма не выглядит проще/понятнее.
example : s ∪ s ∩ t = s :=
  Subset.antisymm
  (fun _ h ↦ Or.elim h id And.left)
  (fun _ h ↦ Or.inl h)

-- 3.a. Экстенсиональность + тактика.
-- Пойдёт.
example : (s \ t) ∪ t = s ∪ t := by
  ext x
  constructor
  · intro h
    rcases h with ⟨hxs, hxsnt⟩ | hxt
    · exact Or.inl hxs
    · exact Or.inr hxt
  · intro h
    show x ∈ ((s \ t) ∪ t)
    show x ∈  (s \ t) ∨ (x ∈ t)
    rcases h with h | h
    · by_cases h' : x ∈ t
      · right
        exact h'
      · left
        exact ⟨h, h'⟩
    · by_cases h' : x ∈ t
      · right
        exact h'
      · contradiction

-- При доказательстве отрицания чего-либо не забывай
-- про исключённое третье, обычно это выглядит вот так:
--
-- by_cases h' : P
-- · assumption
-- · contradiction
--
-- Ну или cases em P, но лучше тактикой by_cases всё таки.

-- 3.b. Антисимметрия.
-- Лучше.
example : (s \ t) ∪ t = s ∪ t := by
  apply Subset.antisymm
  · intro x h
    rcases h with ⟨hxs, _⟩ | hxt
    · exact Or.inl hxs
    · exact Or.inr hxt
  · intro x h
    by_cases h' : x ∈ t
    · right
      exact h'
    · left
      rcases h with hxs | hxt
      · exact ⟨hxs, h'⟩
      · contradiction

-- 3.c. Прямое конструирование пруф-терма.
-- Даже не знаю, надо ли?
example : (s \ t) ∪ t = s ∪ t :=
  Subset.antisymm
    (fun _ h ↦ Or.elim h
      (fun ⟨hxs, _⟩ ↦ Or.inl hxs)
      (fun hxt ↦ Or.inr hxt))
    (fun x h ↦ Or.elim (em (x ∈ t))
      (fun ht ↦ Or.inr ht)
      (fun hnt ↦ Or.elim h
        (fun hxs ↦ Or.inl ⟨hxs, hnt⟩)
        (fun ht ↦ absurd ht hnt)))

-- 4.a. Экстенсиональность.
example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) := by
  ext x; constructor
  -- Оказывается можно использовать rintro и так:
  · rintro (⟨hxs, hxnt⟩ | ⟨hxt, hxns⟩)
    · constructor
      · left; assumption
      · contrapose! hxnt with hst
        exact hst.right
    · constructor
      · right; assumption
      · rintro ⟨hxs, _⟩
        contradiction
  · rintro ⟨hxs | hnn, hnst⟩
    · sorry
    · sorry

-- Проблемы:
--
-- 1. Если в цели отрицание, то надо уметь видеть за ним стрелку и
--    возможность вытащить отрицаемое утверждение в контекст.
-- 2. Если в цели остался False, то нужно видеть за этим возможность
--    сделать apply hnot, где hnot - какая-то гитотеза с отрицанием.
-- 3. Не знал шорткат для rintro как раскидать дизъюнкцию.

-- РНО:

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) := by
  ext x; constructor
  -- Оказывается можно использовать rintro и так:
  · rintro (⟨hxs, hxnt⟩ | ⟨hxt, hxns⟩)
    · constructor
      · left; assumption
      · contrapose! hxnt with hst
        exact hst.right
    · constructor
      · right; assumption
      · rintro ⟨hxs, _⟩
        contradiction
  · rintro (⟨hxs | hxt, hnst⟩)
    · left
      use hxs
      intro hxt
      apply hnst
      exact ⟨hxs, hxt⟩
    · right
      use hxt
      intro hxs
      apply hnst
      -- exact ⟨hxs, hxt⟩
      constructor <;> assumption
      -- ^ Прикольный трюк.

-- Доказательство автора.
example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x; constructor
  · rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    · constructor
      · left
        exact xs
      · rintro ⟨_, xt⟩
        contradiction
    · constructor
      · right
        exact xt
      · rintro ⟨xs, _⟩
        contradiction
  · rintro ⟨xs | xt, nxst⟩
    · left
      use xs
      intro xt
      apply nxst
      constructor <;> assumption
    · right; use xt; intro xs
      apply nxst
      constructor <;> assumption

end My3

namespace My4


end My4
