import Mathlib


variable (a b c  : ℝ)


-- 2009 東北大学入試問題より

example (h1 : a + b = c) : a^3 + b^3 + 3*a*b*c = c^3 := by
  have h1' : a + b - c = 0 :=
    calc
      _ = c - c := by rw [← h1]
      _ = 0 := by ring
  have aux : a^3 + b^3 + 3*a*b*c - c^3 = 0 :=
    calc
     _ = (a+b-c)*(a^2 + b^2 + (-c)^2 - a*b + b*c + c*a) := by ring
     _ = 0 * (a^2 + b^2 + (-c)^2 - a*b + b*c + c*a) := by rw [h1']
     _ = 0 := by ring
  calc
    _ = a^3 + b^3 + 3*a*b*c - c^3 + c^3 := by ring
    _ = 0 + c^3 := by rw [aux]
    _ = c^3 := by ring

lemma sample : a^2 + b^2 + c^2 - a*b + b*c + c*a = (1/2)*((a-b)^2 + (b + c)^2 + (c + a)^2) := by ring

example (h1 : a + b ≥ c) : a^3 + b^3 + 3*a*b*c ≥ c^3 := by
  have h1' : a + b - c ≥  0 := by
    exact sub_nonneg_of_le h1
  have aux : a^3 + b^3 + 3*a*b*c - c^3 = (a+b-c)*(a^2 + b^2 + c^2 - a*b + b*c + c*a) := by ring
  have aux2 : a^3 + b^3 + 3*a*b*c - c^3 ≥ 0 := by
    rw [aux]
    rw [sample]
    apply Left.mul_nonneg
    apply h1'
    apply Left.mul_nonneg
    norm_num
    apply Left.add_nonneg
    apply Left.add_nonneg
    apply sq_nonneg
    apply sq_nonneg
    apply sq_nonneg
  exact sub_nonneg.mp aux2



example : a^2 + b^2 + c^2 - a*b + b*c + c*a = (1/2)*(2*a^2 + 2*b^2 + 2*c^2 - 2*a*b + 2*b*c + 2*c*a) := by ring


example (h1 : a ≥ 0) (h2 : b ≥ 0): a*b ≥ 0 := by exact Left.mul_nonneg h1 h2

#loogle "mul", "le", "Real"

/-
  二次方程式の解の公式. 余力のあるものは一般的な形, a^2 - 2*b*x + c = 0 の解の公式を
  定式化して証明してみよ.
-/

-- 実数の二乗の平方根はそのものという補題は Real.sq_sqrt だった.
example (H : a ≥ 0): √a^2 = a := by exact Real.sq_sqrt H

example (H : a + b ≥ 0 ): √(a+b)^2 = |a+b| := by
  rw [Real.sq_sqrt H]
  rw [abs_of_nonneg H]


example (h1 : x^2 - 2*b*x + c = 0) (h2 : s^2 = b^2 - c)
  : x = b + s ∨ x = b - s := by
  have aux : x^2 - 2*b*x + c = (x - b + s)*(x - b - s) := by
    calc
    _ = (x - b)^2 - (b^2 - c) := by ring
    _ = (x - b)^2 - s^2 := by rw [h2]
    _ = (x - b + s)*(x - b - s) := by ring
  rw [aux] at h1
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h1 with A|B
  · right
    calc
        _  = (x - b +  s) + b - s := by ring
        _  = 0 + b - s := by rw [A]
        _ = b - s := by ring
  · left
    calc
      _ = (x - b - s) + b + s := by ring
      _ = 0 + b + s := by rw [B]
      _ = b + s := by ring


-- 単純な因数分解ではなく, 文字の置き換えなど必要とすると ring が通らなくなる.
