import Mathlib


variable (a b c  : ℝ)

-- 2009 東北大学入試問題より

example (h1 : a + b = c) : a^3 + b^3 + 3*a*b*c = c^3 := by sorry


/-
  二次方程式の解の公式. 余力のあるものは一般的な形, a^2 - 2*b*x + c = 0 の解の公式を
  定式化して証明してみよ.
-/


example (h1 : x^2 - 2*b*x + c = 0) (h2 : s^2 = b^2 - c) : x = b + s ∨ x = b - s := by sorry
