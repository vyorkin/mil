-- 2.2. Proving Identities in Algebraic Structures

import Mathlib

section
-- Кольцо это мн-во R с
-- Операциями: +, ×
-- Константами: 0, 1
-- Операцией: x → -x
-- При этом:
-- R это блять не вещественные числа,
-- R это какая-то своя буковка, у нас тут R должна быть
-- абелевой группой по сложению: ∀ a b c
--    a + b = b + a - коммутативность
--    (a + b) + c = a + (b + c) - ассоциативность
--    ∃ 0 ∈ R, a = a + 0 - сущ. нейтральный элемент
--    ∃ (-a) ∈ R, a + (-a) = 0 - сущ. обратный элемент для сложения
-- Умножение ассоциативно и дистрибутивно по сложению:
--    (a × b) × c = a × (b × c)
--    a × (b + c) = a × b + a × c
-- Сущ. нейтральный элемент для умножения:
--    ∃ 1 ∈ R, a = a × 1

-- Заметь, что кольцо не требует коммутативности умножения.
-- Потому что в общем коммутативность умножения не всегда выполняется.
-- Например, она не выполняется для матриц n×n,
-- т.е. m₁(n×n) * m₂(n×n) ≠ m₂(n×n) * m₁(n×n)

variable (R : Type*) [Ring R]

-- Квадратные скобки делают наш R инстансом тайпкласса кольца и
-- мы получаем возможность работать с R как с кольцом.

#check (add_comm : ∀ a b : R, a + b = b + a)
#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_zero : ∀ a : R, a + 0 = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))

-- Т.к. умножение не коммутативно, то нам нужны 2 леммы
-- дистрибутивности - для умножения слева и справа, и две леммы о
-- нейтральных элементах для умножения тоже слева и справа.
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)

-- Заметь, что ничего нет про умножение на ноль. Это потому,
-- что леммы a * 0 и 0 * a выводятся из этих аксиом кольца.
end

section
-- CommRing
-- Так вот, про коммутативность умножения.
-- Мы можем сделать наш R _коммутативным_ кольцом.

variable (R : Type*) [CommRing R]
variable (a b c d : R)

-- Без коммутативности это не верно.
example : c * b * a = b * (a * c) := by ring
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring
example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring
example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

-- ^ Для коротких доказательств принято писать док-во на той же строке.
-- Типа того: ... := by ring / by linarith

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw [pow_two, pow_two]
  rw [add_mul, mul_sub, mul_sub]
  rw [mul_comm b a] -- Используем коммутативность умножения
  rw [add_sub]
  rw [add_comm]
  rw [add_sub]
  rw [add_comm]
  rw [← add_sub]
  rw [sub_self]
  rw [add_zero]
end

-- Будем учиться использовать аксиомы колец.
-- Начнём с базовых/начальных аксиом и на их основе докажем
-- новые теоремы про кольца (они все есть в Mathlib,
-- мы просто заново определим свои в учебных целях).
namespace MyRing

-- Делаем R неявным аргументом.
variable {R : Type*} [Ring R]

-- Для кольца нужна лемма о нейтральном элементе и
-- обратном элементе сложения только с одной стороны,
-- тк для другой стороны оба утверждения следуют из аксиом кольца.

theorem add_zero (a : R) : a + 0 = a := by
  rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by
  rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_neg_cancel, add_zero]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b]
  rw [← add_neg_cancel_right c b]
  rw [h]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← add_neg_cancel_right b a, add_comm b a]
  rw [← add_neg_cancel_right c a, add_comm c a]
  rw [h]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 + 0 * a := by
    rw [← add_mul, add_zero, zero_add]
  rw [add_right_cancel h]

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [← neg_add_cancel_right b a]
  rw [add_comm]
  rw [← add_assoc]
  rw [h]
  rw [zero_add]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [← neg_add_cancel_left b a, add_comm b a]
  rw [h, add_zero]

-- Для числовых литералов lean 4 автоматически пытается синтезировать
-- инстанс вида: OfNat.ofNat -0 : α. И по умолчанию α = Nat, поэтому здесь нам
-- требуется явно указать R, чтобы показать что у нас за инстанс для чисел.
theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero -- (h : a + b = 0) : -a = b
  -- -0 = 0 => 0 + 0 = 0
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero -- (h : a + b = 0) : -a = b
  -- - -a = a => -a + a = 0
  -- При обратном рассуждении neg_eq_of_add_eq_zero
  -- снимает один `-` с `- - a`.
  rw [add_comm, add_neg_cancel]

-- In Lean, subtraction in a ring is provably equal
-- to addition of the additive inverse.
example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b -- a - b = a + -b

-- Тактика rfl (reflexivity) фактически разворачивает определение сложения,
-- редуцирует пока редуцируется и проверяет равны ли обе стороны равенства.
-- Это называется равенство по определению.
-- И есть ещё аналогичный пруф-терм, который называется так же - rfl.
-- Когда линь его видит, он делает ровно тоже самое, что и
-- при использовании тактики rfl. Поэтому ты можешь использовать
-- её для доказательства равенств вида:
example (a b : ℝ) : a - b = a + -b := rfl
example (a b : ℝ) : a - b = a + -b := by rfl

theorem self_sub (a : R) : a - a = 0 := by
  rw [← add_neg_cancel a]
  rw [sub_eq_add_neg]

theorem self_sub_real (a : ℝ) : a - a = 0 := by
  -- ℝ это просто конкретный инстанс кольца,
  -- поэтому можно доказать вот так:
  exact self_sub a

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two]
  rw [add_mul]
  rw [one_mul]

-- Нам не всегда требуется "сила кольца".
-- Иногда достаточно, чтобы тип был группой.

-- Удобно пользоваться аддитивной нотацией, когда группая операция коммутативна.
-- Когда коммутативноси нет, то удобнее пользоваться мультипликативной ноатцией.
-- Поэтому в Lean есть и AddGroup и Group
-- (а так же их абелевы варианты AddCommGroup, CommGroup)

-- Аддитивная группа.
variable (A : Type*) [AddGroup A]

-- Список аксиом аддитивной группы:
#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

-- Мультипликативная группа.
variable {G : Type*} [Group G]

-- Список аксиом мультипликативной группы:
#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

-- Вспомогательная лема, которая используется ниже.
lemma aux₁ (a b : G) : a = (b⁻¹ * b) * a := by
  nth_rw 1 [← one_mul a]
  rw [← inv_mul_cancel]

-- Эта лемма мне так и не пригодилась.
-- Но выглядит полезной, поэтому пока оставил.
lemma aux₂ (a : G) : 1 = a⁻¹ * (1 * a) := by
  nth_rw 1 [← inv_mul_cancel a]
  nth_rw 2 [← one_mul a]

-- Полезная вспомогательная лемма, используется ниже.
theorem inv_inv_eq (a : G) : a⁻¹⁻¹ = a := by
  nth_rw 2 [← one_mul a]
  rw [← inv_mul_cancel a⁻¹]
  rw [mul_assoc]
  rw [inv_mul_cancel]
  rw [mul_one]

-- Здесь молодец. Получилось имхо лучше, чем у автора.
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  rw [← inv_mul_cancel a⁻¹]
  rw [inv_inv_eq]

-- Доказательство здорового человека.
theorem mul_one (a : G) : a * 1 = a := by
  rw [← inv_mul_cancel a]
  rw [← mul_assoc]
  rw [mul_inv_cancel]
  rw [one_mul]
-- Не заметил, что могу заменить 1 на a⁻¹ * a и
-- сдвинув сбочки влево ассоциативностью поменять a * a⁻¹ на 1,
-- получив таким образом умножение на 1 слева, аксиома которой у нас есть.
--
-- В общем: есть у тебя есть cancel, ассоциативность и единица справа/слева, а
-- требуется доказать единицу с другой стороны, то используй assoc + cancel.

-- Доказательство курильщика.
-- Бля, делай перерывы, на это смотреть страшно.
theorem mul_one' (a : G) : a * 1 = a := by
  rw [aux₁ a a⁻¹]
  rw [← inv_mul_cancel a]
  rw [← mul_assoc]
  nth_rw 1 [mul_assoc a⁻¹⁻¹ a⁻¹]
  nth_rw 1 [inv_mul_cancel]
  nth_rw 1 [mul_assoc a⁻¹⁻¹ 1]
  rw [one_mul]

-- Вспомогательная лемма, которую я рассчитывал использовать
-- для доказательства mul_inv_rev ниже, но она оказалась не нужна.
theorem mul_inv_comm (a : G) : a * a⁻¹ = a⁻¹ * a := by
  rw [mul_inv_cancel]
  rw [inv_mul_cancel]

-- Здесь я не справился за час с чем-то.
-- Да, доказательство чуть более сложное, чем для mul_inv_cancel.
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← one_mul b⁻¹]
  rw [← inv_mul_cancel (a * b)]
  rw [mul_assoc]
  rw [mul_assoc]
  rw [mul_assoc]
  rw [← mul_assoc b b⁻¹ a⁻¹]
  rw [mul_inv_cancel]
  rw [one_mul]
  rw [mul_inv_cancel]
  rw [mul_one]

-- Основная идея такого доказательства в том, что мы должны как-то добавить
-- выражение (a * b)⁻¹ в правую часть, а всё, что появится в следствие этого
-- добавления мы должны закэнслить. Остальное детали.

-- Один из ключевых моментов, до которых я не смог догадаться
-- это сдвиг _внутренних_ скобочек ассоциативностью:
-- (a * (b * (b⁻¹ * a⁻¹))) =>
-- (a * ((b * b⁻¹) * a⁻¹))

-- Вот доказательство автора:
theorem mul_inv_rev' (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← one_mul (b⁻¹ * a⁻¹)]
  rw [← inv_mul_cancel (a * b)]
  rw [mul_assoc]
  rw [mul_assoc]
  rw [← mul_assoc b b⁻¹]
  rw [mul_inv_cancel]
  rw [one_mul]
  rw [mul_inv_cancel]
  rw [mul_one]

end MyRing
