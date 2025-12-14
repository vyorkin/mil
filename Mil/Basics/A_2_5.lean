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

-- inf_comm
example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat simp only [le_inf, inf_le_right, inf_le_left]

-- Идея следующего доказательства в том, что мы хотим использовать
-- более простые промежуточные утверждения.
-- Сначала мы используем le_inf: a ≤ b → a ≤ c → a ≤ b ⊓ c.
-- Следующий шаг чуть менее тривиальный, но вполне логичный:
-- тактика trans создаст 2 подцели, которые будут доказуемы потому,
-- что у нас есть теорема про `x ⊓ y ≤ x`, но мы ничего не знаем o
-- комбинациях типа x ⊓ y ⊓ z ≤ x.
--
-- Тактика trans s заменит цель ⊢ t → u на:
-- ⊢ t → s
-- ⊢ s → u
--
-- В нашем случае:
-- (x ⊓ y) ⊓ z ≤ x
--       t       u
--
-- s = x ⊓ y
-- 1. x ⊓ y ⊓ z ≤ x ⊓ y
-- 2. x ⊓ y ≤ x

-- inf_assoc
example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · show (x ⊓ y) ⊓ z ≤ x ⊓ (y ⊓ z)
    apply le_inf -- a ≤ b → a ≤ c → a ≤ b ⊓ c
    · show (x ⊓ y) ⊓ z ≤ x
      --        t        u
      --   s = x ⊓ y
      --   x ⊓ y ⊓ z ≤ x ⊓ y
      --   x ⊓ y ≤ x
      trans x ⊓ y <;> exact inf_le_left
      -- apply inf_le_of_left_le
      -- apply le_trans inf_le_left
    · apply inf_le_inf
      · apply inf_le_right
      · exact le_refl z
  · show x ⊓ (y ⊓ z) ≤ (x ⊓ y) ⊓ z
    apply le_inf -- a ≤ b → a ≤ c → a ≤ b ⊓ c
    · show x ⊓ (y ⊓ z) ≤ x ⊓ y
      apply le_inf
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
    · exact le_sup_right
    · exact le_sup_left
  · apply sup_le
    · exact le_sup_right
    · exact le_sup_left

-- sup_comm
example : x ⊔ y = y ⊔ x := by
  apply le_antisymm <;> exact sup_le le_sup_right le_sup_left

-- sup_assoc
example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    · show x ⊔ y ≤ x ⊔ (y ⊔ z)
      apply sup_le_sup_left -- (h : a ≤ b) : c ⊔ a ≤ c ⊔ b
      apply le_sup_left
    · show z ≤ x ⊔ (y ⊔ z)
      apply le_sup_of_le_right -- (h : c ≤ b) : c ≤ a ⊔ b
      apply le_sup_right
  · apply sup_le
    · apply le_sup_of_le_left
      apply le_sup_left
    · apply sup_le_sup_right
      apply le_sup_right

end My3

namespace My4

variable {α : Type*} [Lattice α]
variable (x y z : α)

-- TODO: Rewrite using calc & trans tactics

#check inf_comm  -- a ⊓ b = b ⊓ a
#check inf_assoc -- a ⊓ b ⊓ c = a ⊓ (b ⊓ c)
#check sup_comm  -- a ⊔ b = b ⊔ a
#check sup_assoc -- a ⊔ b ⊔ c = a ⊔ (b ⊔ c)

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  · apply le_inf
    · apply le_refl
    · apply le_sup_left

theorem absorb2 : x ⊔ (x ⊓ y) = x := by
  apply le_antisymm
  · apply sup_le
    · apply le_refl
    · apply inf_le_left
  · apply le_sup_left

#check inf_sup_self
#check sup_inf_self

end My4

-- Эти 2 теоремки нам пригодятся, экспортируем.
export My4 (absorb1 absorb2)

namespace My5

-- Решётка, на которой выполняются эти 2 равенства называется
-- дистрибутивной решёткой:
-- x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)
-- x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)

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

-- Левые выводятся из правых и наоборот:
#check (inf_sup_left  x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)

#check (sup_inf_left  x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))

-- TODO: Показать, что не всякая решётка дистрибутивна
-- by providing an explicit description of a nondistributive lattice with finitely many elements.

end My5

namespace My6

-- Нужно показать, что эти дистрибувности друг из друга следуют.
-- Короче показать, что верно "туда-сюда".

variable {α : Type*} [Lattice α]
variable (a b c : α)

-- Операция ⊓ связывает сильнее, чем ⊔:
--
-- example : a ⊔ (b ⊓ c) = a ⊔ b ⊓ c := by rfl
-- example : (a ⊓ b) ⊔ (a ⊓ c) = a ⊓ b ⊔ a ⊓ c := by rfl

-- Первая неудачная попытка:
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
        : a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h]
  show a ⊔ (b ⊓ c) = ((a ⊔ b) ⊓ a) ⊔ ((a ⊔ b) ⊓ c)
  rw [inf_comm (a ⊔ b) a]
  rw [inf_comm (a ⊔ b) c]
  rw [absorb1]
  show a ⊔ (b ⊓ c) = a ⊔ (c ⊓ (a ⊔ b))
  -- Вот тут я свернул не туда.
  -- Это произошло по инерции, потому что в большинстве предыддущих
  -- доказательств нужно было использовать антисимметрию.
  apply le_antisymm
  · show a ⊔ (b ⊓ c) ≤ a ⊔ (c ⊓ (a ⊔ b))
    apply sup_le_sup_left -- (h : a ≤ b) : c ⊔ a ≤ c ⊔ b
    show b ⊓ c ≤ c ⊓ (a ⊔ b)
    rw [inf_comm]
    apply inf_le_inf_left
    exact le_sup_right
  · show a ⊔ (c ⊓ (a ⊔ b)) ≤ a ⊔ (b ⊓ c)

    -- rw [inf_comm]
    -- show a ⊔ ((a ⊔ b) ⊓ c) ≤ a ⊔ (b ⊓ c)
    -- apply sup_le_sup_left
    -- apply inf_le_inf_right

    apply sup_le_sup_left
    rw [inf_comm b c]
    -- show c ⊓ (a ⊔ b) ≤ c ⊓ b
    -- apply inf_le_inf_left

    rw [h]
    show (c ⊓ a) ⊔ (c ⊓ b) ≤ c ⊓ b
    sorry
    --      a    ⊔    b    ≤ b

    -- apply sup_le -- тупик

    -- apply le_inf
    -- · show (c ⊓ a) ⊔ (c ⊓ b) ≤ c
    --   apply sup_le
    --   · exact inf_le_left
    --   · exact inf_le_left
    -- · show (c ⊓ a) ⊔ (c ⊓ b) ≤ b
    --   sorry

-- Выводы:
--
-- 1. Объясняй почему применяешь ту или иную теорему/рассуждение.
--    Если не можешь чётко объяснить, то возможно это когнитивное искажение.
--    В задаче выше я применил le_antisymm инерции, потому что в
--    большинстве предыддущих доказательств нужно было использовать антисимметрию.
--    А когда я заходил в тупик, то не отматывал доказательство до этого момента,
--    в котором свернул не туда (по инерции).
--
-- 2. Ставь скобки, всегда ставь скобки. Каждую бинарную операцию оборачивай в скобки.
--    Так ты повышаешь шансы увидеть какой-то паттерн.
--
-- 3. Держи перед глазами все теоремы, которые могут быть потенциально полезными.

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
        : a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h]
  rw [inf_comm (a ⊔ b) a]
  rw [absorb1]
  rw [inf_comm (a ⊔ b) c]
  rw [h]
  show a ⊔ (b ⊓ c) = a ⊔ (c ⊓ a ⊔ c ⊓ b)
  rw [← sup_assoc]
  show a ⊔ (b ⊓ c) = (a ⊔ (c ⊓ a)) ⊔ (c ⊓ b)
  rw [inf_comm c a]
  show a ⊔ (b ⊓ c) = (a ⊔ (a ⊓ c)) ⊔ (c ⊓ b)
  rw [absorb2]
  rw [inf_comm b c]

-- Доказательство автора.
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
         : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h]
  rw [@inf_comm _ _ (a ⊔ b)]
  rw [@inf_comm _ _ (a ⊔ b)]
  rw [absorb1]
  rw [h]
  rw [← sup_assoc]
  rw [@inf_comm _ _ c a]
  rw [absorb2]
  rw [inf_comm]

example (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))
        : a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := by
  rw [h]
  show a ⊓ (b ⊔ c) = ((a ⊓ b) ⊔ a) ⊓ ((a ⊓ b) ⊔ c)
  rw [sup_comm (a ⊓ b) a]
  rw [absorb2]
  show a ⊓ (b ⊔ c) = a ⊓ ((a ⊓ b) ⊔ c)
  rw [sup_comm (a ⊓ b) c]
  rw [h]
  show a ⊓ (b ⊔ c) = a ⊓ ((c ⊔ a) ⊓ (c ⊔ b))
  rw [← inf_assoc]
  rw [sup_comm c a]
  rw [absorb1]
  rw [sup_comm c b]

end My6

namespace My7

-- Можно комбинировать аксиоматические структуры (наборы аксиом).
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

#check sub_eq_add_neg -- a - b = a + -b

#check le_neg   -- : a ≤ -b ↔ b ≤ -a
#check neg_neg  -- : - -a = a
#check sub_self -- : a - a = 0

theorem aux₀ (h : a ≤ b) : 0 ≤ b - a := by
  rw [← sub_self b]
  repeat rw [sub_eq_add_neg]
  apply add_le_add_left
  rw [le_neg]
  rw [neg_neg]
  assumption

theorem aux₁ (h : 0 ≤ b - a) : a ≤ b := by
  rw [← sub_self b] at h
  repeat rw [sub_eq_add_neg] at h
  apply add_le_add_left at h
  have := h a
  simp at h
  assumption

#check mul_add  -- : a * (b + c) = a * b + a * c
-- #check mul_comm -- : a * b = b * a (requires CommMagma typeclass)

-- Моя неудачная попытка #1.
--
-- Я пытался найти способ применить:
-- mul_pos : 0 < a → 0 < b → 0 < a * b
example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  sorry
  -- apply aux₁
  -- show 0 ≤ b * c - (a * c)
  -- repeat rw [sub_eq_add_neg]
  -- show 0 ≤ b * c + -(a * c)
  -- apply add_nonneg
  -- · show 0 ≤ b * c
  --   trans b
  --   · assumption
  --   · apply mul_pos
  --     sorry
  -- · show 0 ≤ -(a * c)
  --   sorry

  -- apply aux₁
  -- show 0 ≤ b * c - (a * c)
  -- repeat rw [sub_eq_add_neg]
  -- show 0 ≤ b * c + -(a * c)
  -- apply add_nonneg
  -- · apply mul_nonneg
  --   · sorry
  --   · assumption
  -- · sorry

  -- · trans c
  --   · assumption
  --   · sorry
  -- · sorry
  -- rw [← sub_self (b * c)]
  -- apply add_le_add_left

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  apply aux₀ at h
  have h'' := mul_nonneg h h'
  rw [sub_mul] at h''
  apply aux₁
  assumption

-- "А ты не верил":
#check sub_mul -- : (a - b) * c = a * c - b * c

-- Она дана была нам cвыше:
#check mul_nonneg -- : (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b

-- Решение автора:
example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h'' : 0 ≤ (b - a) * c := mul_nonneg (aux₀ _ _ h) h'
  rw [sub_mul] at h''
  exact aux₁ _ _ h''

-- Что я не заметил и не сделал:
--
-- 1. Когнитивное искажение: "если мы никогда не пользовались теоремами про
--    дистрибутивность вычитания, то и здесь это не потребуется". Совершенно
--    необоснованный вывод. Не пользовались, а вот тут взяли и воспользовались.
--
-- 2. Не догадался до 0 ≤ (b - a) * c.
--    Было вот так:
--    h  : a ≤ b
--    h' : 0 ≤ c
--    ⊢ a * c ≤ b * c
--
--    Дать имена доказанным ранее теоремам я догадался.
--    Я догадался, что нужно получить слева 0, а справа произведение,
--    чтобы затем можно было применить: mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b
--
--    Но я не увидел, что из двух этих гипотез h: a ≤ b и h': 0 ≤ c можно
--    сформировать одну 0 ≤ (b - a) * c. Переписав h: a ≤ b ->> 0 ≤ b - a и
--    применив mul_nonneg : (h : 0 ≤ a) (h' : 0 ≤ b) : 0 ≤ a * b
--
--    Учись видеть за вещами вроде 0 ≤ a:
--    0 ≤ a + b - c + d * e итд, абстрагируйся от буковок ёпта.


end My7

-- Возможно пригодятся чуть ниже.
export My7 (aux₀ aux₁)

namespace My8

variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x   : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)

#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

-- dist x z ≤ dist x y + dist y z | z = x

-- 0 ≤ dist x y + dist y x
-- dist x y - dist x y ≤ dist x y + dist x y

-- dist x x ≤ dist x y + dist y x
-- 0 ≤ dist x y + dist y x
-- 0 ≤ dist x y + dist x y

-- Автор рекомендует использовать эту теорему:
#check nonneg_of_mul_nonneg_left -- (h : 0 ≤ a * b) (hb : 0 < b) : 0 ≤ a

-- Моё док-во:
example (x y : X) : 0 ≤ dist x y := by
  have h := dist_triangle x y x
  rw [dist_self, dist_comm y x] at h
  rw [nonneg_add_self_iff] at h
  -- simp at h
  assumption

-- ^^ Заметь, как ты снова не воспользовался тактикой linarith.
-- Ты её не понимаешь, поэтому не пользуешься.
-- А вот автор пользуется, см ниже.

-- Читерское:
example (x y : X) : 0 ≤ dist x y := by exact dist_nonneg

-- Доказательство автора:
example (x y : X) : 0 ≤ dist x y := by
  have : 0 ≤ dist x y + dist y x := by
    rw [← dist_self x]
    apply dist_triangle
  linarith [dist_comm x y]

end My8
