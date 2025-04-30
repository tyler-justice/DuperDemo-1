import Mathlib

/-
Lean とは何か
- Microsoft によって開発された関数型プログラミング言語である.
- 数学の種々の定理を証明「することも出来る」
-/

/-
What is Lean
- A functional programming language developed by Microsoft.
- Using Lean, we can prove some mathematical theorems.
-/

/-
Lean の特徴
- 関数型」プログラミング : プログラムは項と関数からなる.
- 項にはすべて「型」がある.
- 項から項に対応をつけるのが Lean の関数
-/

/-
A description of Lean
- "Functional" programming : A program consists of terms and functions.
- Every term has "Type".
-/

/-
Lean の「正しさ」について
- Lean は無矛盾, すなわち同時にある定理 A とその定理 A の否定が証明されることはないか?
-Lean ver. 3 までは以下のことが証明されていた.
  - Lean ver. 3 は ZFC + 到達不可能基数の存在と相対的に無矛盾, すなわち Lean が無矛盾であれば ZFC + 到達不可能基数も無矛盾, 逆も成り立つ.
  - これは ZFC + 到達不可能基数の存在を Lean の code でプログラム化し, 逆に Lean の公理を ZFC + 到達不可能基数の存在の公理で書くことに酔って示された.
- 2025 年現在 Lean の version は 4.18.
- この版の Lean の公理はまだ ZFC + 到達不可能基数の存在の公理で表すことが出来ていない (逆は出来ている)
- この問題に取り組むことは興味があるが, 自分には出来ない (指導も難しい)
-/

section

variable (a b c : ℝ)

example  : a^2 - b^2 = (a -b)*(a + b) := by ring
--  calc
--    _ = a*a + a*b - a*b - b*b := by ring
--    _ = a*(a + b) - a*b - b*b := by ring
--    _ = a*(a + b) + (-b)*(a) + (-b)*b := by ring
--    _ = a*(a + b) + (-b)*(a + b) := by ring
--    _ = (a + (-b))*(a + b) := by ring
--


example : (a + b + c)*(a^2 + b^2 + c^2 - a - b -c) = a^3 + b^3 + c^3 - 3*a*b*c := by
  sorry

end
