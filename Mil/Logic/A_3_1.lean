import Mathlib
import Mathlib.Data.Real.Basic

-- 3. Логика.

-- 3.1. Импликация и квантор существования.

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ,
  0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

-- Нам помогут доказать эту лемму чуть позже.
theorem my_lemma : ∀ x y ε : ℝ,
  0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  sorry

section

variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end

namespace My1
-- Можно использовать неявные аргументы.
theorem my_lemma2 : ∀ {x y ε : ℝ},
  0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  sorry

section

variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁
#check my_lemma2 h₀ h₁ ha hb
end

end My1Gkkj

namespace My2

-- Похоже на первую встречу с тактикой intro в этой книге.
theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  sorry

#check abs_mul -- |a * b| = |a| * |b|
#check abs_nonneg -- 0 ≤ |a|
#check mul_le_mul -- (h₁ : a ≤ b) (h₂ : c ≤ d) (c0 : 0 ≤ c) (b0 : 0 ≤ b) : a * c ≤ b * d
#check mul_lt_mul_right -- (a0 : 0 < a) : b * a < c * a ↔ b < c
#check one_mul --  1 * a = a

#check le_of_lt -- (hab : a < b) : a ≤ b

#check add_le_add_left -- a ≤ b → ∀ c, c + a ≤ c + b
#check add_lt_add_left -- (bc : b < c) (a : α) : a + b < a + c

-- Завершить доказательство, используя следующие теоремы:
-- abs_mul, mul_le_mul, abs_nonneg, mul_lt_mul_right, and one_mul.
-- Этих 5 теорем достаточно или это подъёбка?
theorem my_lemma4' :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := abs_mul x y
    _ ≤ |x| * ε := by
      apply mul_le_mul (le_refl _)
      · exact le_of_lt ylt
      · exact abs_nonneg y
      · exact abs_nonneg x

    -- Вот с этой частью доказательства неравенства
    -- я не справился самостоятельно, оставалось чуть-чуть и
    -- я не допёр для применения тактики linarith:
    --
    -- _ < 1 * ε := by
    --   --  mul_lt_mul_right : (a0 : 0 < a) : (b * a < c * a) ↔ b < c
    --   --  mul_lt_mul_right : (a0 : 0 < ε) : (b * ε < c * ε) ↔ b < c
    --   rw [mul_lt_mul_right epos]
    --   linarith

    -- Альтернативный вариант (мой):
    _ < 1 * ε := by
      rw [mul_lt_mul_right]
      · linarith
      · assumption

    -- Момент, когда я свернул не туда.
    -- Вместо linarith я стал пробовал транзитивность.
    --   · show |x| < 1
    --     -- В этом точно есть смысл?
    --     -- UPDATE: Нет, нужно было просто использовать linarith.
    --     trans ε
    --     · assumption
    --     · show ε < 1
    --       sorry
    --   · assumption
    _ = ε := one_mul ε

-- lt_of_le' : b ≠ a → a ≤ b → a < b

-- epos : 0 + 1 < ε + 1
-- ele1 : ε + 1 ≤ 1 + 1
-- ⊢ ε < 1

-- Итак:
theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := abs_mul x y
    _ ≤ |x| * ε := by
      apply mul_le_mul (le_refl _)
      · exact le_of_lt ylt
      · exact abs_nonneg y
      · exact abs_nonneg x

    -- _ < 1 * ε := by
    --   rw [mul_lt_mul_right]
    --   · linarith only [xlt, ele1]
    --   · assumption

    -- Доказательство без linarith:
    _ < 1 * ε := by
      -- |x| < ε ≤ 1 ⇒ |x| < 1
      have hx1 : |x| < 1 := lt_of_lt_of_le xlt ele1
      exact (mul_lt_mul_right epos).2 hx1

    -- Ещё один вариант с by_contra:
    -- _ < 1 * ε := by
    --   -- Сначала отдельная лемма: из |x| < ε и ε ≤ 1 следует |x| < 1
    --   have hx1 : |x| < 1 := by
    --     -- Используем стандартный трюк: либо |x| < 1, либо |x| ≥ 1
    --     by_contra h
    --     -- h : ¬ |x| < 1, то есть 1 ≤ |x|
    --     have h1 : 1 ≤ |x| := le_of_not_gt h
    --     -- Из xlt : |x| < ε получаем 1 < ε
    --     have h2 : 1 < ε := lt_of_le_of_lt h1 xlt
    --     -- Из ele1 : ε ≤ 1 и h2 : 1 < ε получаем противоречие 1 < 1
    --     have : 1 < (1 : ℝ) := lt_of_lt_of_le h2 ele1
    --     exact lt_irrefl _ this
    --   -- Теперь переводим неравенство через mul_lt_mul_right
    --   -- (mul_lt_mul_right epos) : (|x| * ε < 1 * ε) ↔ (|x| < 1)
    --   exact (mul_lt_mul_right epos).2 hx1

    _ = ε := one_mul ε

end My2
