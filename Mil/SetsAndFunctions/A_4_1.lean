import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic

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

-- Когда видишь s \ t сразу думай о том, чтобы прийти к противоречию
-- или об использовании логической контрапозиции (contrapose! h).

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

open Set

def evens : Set ℕ := { n | Even n }
def odds : Set ℕ := { n | ¬Even n }

#check Nat.not_even_iff_odd -- : ¬Even n ↔ Odd n

example : evens ∪ odds = univ := by
  -- rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em -- p ∨ ¬p

end My4

namespace My5

open Set

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False := h

-- Инстина инстинна.
-- trivial is the canonical proof of True.
example (x : ℕ) : x ∈ (univ : Set ℕ) := trivial

-- Упражнение.

#check Nat.Prime.eq_two_or_odd -- (hp : Nat.Prime p) : p = 2 ∨ p % 2 = 1
#check (Nat.odd_iff : Odd n ↔ (n % 2 = 1))
#check (Nat.not_even_iff_odd : ¬Even n ↔ Odd n)

#check mem_setOf -- a ∈ {x | p x} ↔ p a

-- Моё доказательство.
example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  rintro n ⟨hnp, hngt2⟩
  rcases Nat.Prime.eq_two_or_odd hnp with h | h
  · rw [mem_setOf] at *
    -- Не заметил:
    -- rw [h]
    linarith
  · rw [← Nat.odd_iff] at h
    rw [← Nat.not_even_iff_odd] at h
    exact h

-- Что можно было сделать лучше:
-- 1. Использовать simp вместо `rw [mem_setOf] at *`
--    чтобы свернуть определения.
-- 2. Не заметил, что мог переписать n внутри определения используя h.

-- Доказательство.
example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  simp
  intro nprime n_gt
  rcases Nat.Prime.eq_two_or_odd nprime with h | h
  · rw [h]
    unfold Odd
    linarith
  · rw [Nat.odd_iff, h]

end My5

namespace My6

open Set

-- У нас 2 определения для простых чисел.
-- Более общее верно для любых коммутативных моноидов с нулевым элементом.

#print Prime
#print Nat.Prime

-- Для натуральных чисел верны оба определения и
-- можно переходить от одного к другому.

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end My6

namespace My7

open Set

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) :
  ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  · apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) :
  ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, not_even_x, prime_x⟩
  use x, xs

section
-- Упражнения.

variable (ssubt : s ⊆ t)

#check subset_def -- s ⊆ t = ∀ x ∈ s, x ∈ t

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) :
  ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x h
  have hxt : x ∈ t := ssubt h
  exact ⟨h₀ x hxt, h₁ x hxt⟩

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, hxs, hne, hp⟩
  have hxt : x ∈ t := ssubt hxs
  use x, hxt

end

end My7

namespace My8

open Set

variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

-- Последовательность множеств с элементами типа α:
-- s₀, s₁, s₂, ... := s : ℕ → Set α
--
-- s i - Множество с индексом i.
-- ⋃ i, s i - Объединение всех множеств этой последовательности.
-- ⋂ i, s i - Пересечение всех множеств этой последовательности.
--
-- Для индексов не обязательно использовать натуральные числа (ℕ).
-- Индекс не обязательно единственный, может быть и так:
-- s₀₁, s₀₂, ..., s₁₁, s₁₂, ..., sₙ₁, ..., sₙₙ

-- Индексированное объединение множеств: ⋃ (набирается вот так: \U).
-- Индексированное пересечение множеств: ⋂ (набирается как обычно пересечение вот так: \I).

#check mem_iUnion -- (x ∈ ⋃ i, s i) ↔ (∃ i, x ∈ s i)
#check mem_iInter -- (x ∈ ⋂ i, s i) ↔ ∀ (i : ι), x ∈ s i

-- Пересечение индексированных объединений =
-- Объединение индексированных пересечений.
example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  · rintro ⟨i, xAi, xs⟩
    exact ⟨xs, ⟨i, xAi⟩⟩

-- Дистрибутивность индексированного пересечения.
example : ⋂ i, (A i) ∩ (B i) = (⋂ i, A i) ∩ (⋂ i, B i) := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    · intro i
      exact (h i).2
  · rintro ⟨h1, h2⟩ i
    constructor
    · exact h1 i
    · exact h2 i

-- Упражнение.
-- Одно из направлений потребует классической логики.
-- Используй: by_cases xs : x ∈ s

example : s ∪ (⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_union, mem_iInter]
  constructor
  · rintro (hxs | hxai)
    · intro i
      right; assumption
    · intro i
      left; exact hxai i
  · intro h
    -- Иногда стоит попробовать рассмотреть
    -- исключённое третье чуть раньше/выше.
    by_cases hs : x ∈ s
    · left; assumption
    · right
      intro i
      rcases h i with h1 | h2
      · assumption
      · contradiction

end My8

namespace My9

open Set

-- Bounded unions & intersections.

-- Эти определения полезны, когда мы рассуждаем о множестве множеств.

-- Объединение индексированных множеств, здесь используются 2 индекса.
#check mem_iUnion₂ -- x ∈ ⋃ i, ⋃ j, s i j ↔ ∃ i j, x ∈ s i j
-- Пересечение индексированных множеств, снова 2 индекса.
#check mem_iInter₂ -- x ∈ ⋂ i, ⋂ j, s i j ↔ ∀ (i : ι) (j : κ i), x ∈ s i j
-- Сравни
#check mem_iUnion -- (x ∈ ⋃ i, s i) ↔ (∃ i, x ∈ s i)
#check mem_iInter -- (x ∈ ⋂ i, s i) ↔ ∀ (i : ι), x ∈ s i

-- Видимо объединения и пересечения множеств индексированных
-- двумя индексами называются "bounded" unions & intersections.

def primes : Set ℕ := { x | Nat.Prime x }

-- Тут два разных ∣ и |.
-- Один про нотацию определения множеств, другой - про делимость.
-- Тот, что про делимость он выглядит короче: ∣ (набирается вот так: |\).
example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  -- Раскрываем по определению экстенсиональности равенства.
  ext x
  show x ∈ (⋃ p ∈ primes, {x | p ^ 2 ∣ x}) ↔ x ∈ {x | ∃ p ∈ primes, p ^ 2 ∣ x}
  rw [mem_iUnion₂]
  -- Странная херня, но верная.
  show (∃ i, ∃ (j : i ∈ primes), x ∈ {x | i ^ 2 ∣ x}) ↔ x ∈ {x | ∃ p ∈ primes, p ^ 2 ∣ x}
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext x
  simp

#check Nat.exists_prime_and_dvd -- (hn : n ≠ 1) : ∃ p, Nat.Prime p ∧ p ∣ n

example : (⋂ p ∈ primes, { x | ¬(p ∣ x) }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋂ p ∈ primes, { x | ¬(p ∣ x) }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  intro h
  have  ⟨x, x_prime, x_div_x⟩ := Nat.exists_prime_and_dvd h
  exact ⟨x, x_prime, x_div_x⟩

-- Упражнение.

#check eq_univ_of_forall -- (∀ (x : α), x ∈ s) → (s = univ)
#check Nat.exists_infinite_primes -- ∃ p, n ≤ p ∧ Nat.Prime p

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  intro x
  simp
  have h := Nat.exists_infinite_primes x
  contrapose! h
  intro n hn hp
  have hh := h n hp
  -- Имеем противоречие на неравенствах в контексте,
  -- линейная арифметика справится.
  linarith

end My9

namespace My10

open Set

variable {α : Type*} (s : Set (Set α))

-- Если у тебя есть некоторое множество множеств s : Set (Set α),
-- то их объединение ⋃₀ имеет тип Set α и определяется как:
-- ⋃₀ : Set α := { x | ∃ t ∈ s, x ∈ t } - sUnion.
--
-- Пересечение множества множеств s : Set (Set α)
-- ⋂₀ : Set α := { x | ∀ t ∈ s, x ∈ t } - sInter.

-- Эти определения полезны, когда мы рассуждаем о множестве множеств.
#check mem_iUnion₂ -- x ∈ ⋃ i, ⋃ j, s i j ↔ ∃ i j, x ∈ s i j
#check mem_iInter₂ -- x ∈ ⋂ i, ⋂ j, s i j ↔ ∀ (i : ι) (j : κ i), x ∈ s i j

#check sUnion_eq_biUnion -- : ⋃₀ s = ⋃ i ∈ s, i
example : ⋃₀ s = ⋃ t ∈ s, t := by
  -- Раскрываем по определению экстенсиональности равенства.
  -- Левая и правая части должны выполняться для всех x.
  ext x
  rw [mem_iUnion₂]
  -- Существует такое подмножеств множества множеств, что x входит в него.
  show x ∈ ⋃₀ s ↔ ∃ i, ∃ (_ : i ∈ s), x ∈ i
  simp

#check sInter_eq_biInter -- : ⋂₀ s = ⋂ i ∈ s, i
example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  -- x входит в каждое из множества множеств.
  show x ∈ ⋂₀ s ↔ ∀ i ∈ s, x ∈ i
  simp

end My10
