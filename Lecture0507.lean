import Mathlib

/-
第一回
- Intro
- 画面共有
- Live.Lean を見せる (少し時間がかかることも伝える)
-/

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
- A function in Lean is a mapping from one term to another.
-/

/-
Lean の「正しさ」について
- Lean は無矛盾, すなわち同時にある定理 A とその定理 A の否定が証明されることはないか?
- Lean ver. 3 までは以下のことが証明されていた.
  - Lean ver. 3 は ZFC + 到達不可能基数の存在と相対的に無矛盾, すなわち Lean が無矛盾であれば ZFC + 到達不可能基数も無矛盾, 逆も成り立つ.
  - これは ZFC + 到達不可能基数の存在を Lean の code でプログラム化し, 逆に Lean の公理を ZFC + 到達不可能基数の存在の公理で書くことに酔って示された.
- 2025 年現在 Lean の version は 4.18.
- この版の Lean の公理はまだ ZFC + 到達不可能基数の存在の公理で表すことが出来ていない (逆は出来ている)
- この問題に取り組むことは興味があるが, 自分には出来ない (指導も難しい)

-/

/-
	•	Does Lean have consistency, i.e., is it the case that both a theorem A and its negation cannot be proven at the same time?
	•	Up to Lean version 3, the following had been proven:
	•	Lean version 3 is relatively consistent with ZFC + the existence of an inaccessible cardinal; that is, if Lean is consistent, so is ZFC + the existence of an inaccessible cardinal, and vice versa.
	•	This was shown by encoding ZFC + the existence of an inaccessible cardinal in Lean, and conversely, expressing Lean’s axioms using the axioms of ZFC + the existence of an inaccessible cardinal.
	•	As of 2025, the current version of Lean is 4.18.
	•	The axioms of this version of Lean have not yet been fully expressed within the axioms of ZFC + the existence of an inaccessible cardinal (though the converse is possible).
	•	I find this problem interesting, but I do not feel capable of working on it myself (nor of supervising others on it).
-/

/-
Question
  Lean で定理 A をエラーを出すことなく形式化出来たとする. 一方, 定理 A の主張の反例を普通の数学 ZFC の公理から構成できたとする. この時どのようなことが結論出来るか?

Answer
  Lean で ZFC の公理を記述出来るので, 定理 A とその否定が共に Lean で証明出来る, すなわち Lean は無矛盾ではない. Lean と ZFC + 到達不可能基数の存在の無矛盾性の等価性から ZFC + 到達不可能基数も無矛盾ではないことがわかる.
-/



section

/- 以下の (a b c : ℝ ) は a b c は型 ℝ を持つという意味. この「型」の概念は言葉で説明するのが難しい. 四回の講義で感覚を掴んでもらいたい. とりあえずは a b c は実数である, と考えて欲しい-/

/-
The expression (a b c : ℝ) means that the variables a, b, and c all have type ℝ.
The concept of “type” is difficult to explain in words, and I hope students will get an intuitive sense of it over the course of four lectures.
For now, I would like you to simply think of a, b, and c as real numbers.
-/

/-
 Lean では演算は左結合である. すなわち
 a*b*c*d = ((a*b)*c)+d
 となる.
-/

/-
Lean での定理, 定義, 例などの読み方
- Lean での定理等は以下のような形をしている. ここで詳細のところは
  - 定理 : 仮定の項を主張の項の変換する「関数」を記述することになる.
  - 定義 : 仮定の項か定義された項がどう定まるか? という「関数」を記述することになる.
theorem 名前 仮定の項 : 主張の項 := 詳細
def 名前 仮定の項 : 定義された項の型 := 詳細
-/

variable (a b c : ℝ)

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]




example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

/-
 成績評価はこのような sorry を含む example を出すので, プログラムを書いて Moodle に投稿してもらい,
 エラーが出ない場合, 正解とみなして加点する.
-/

/- 関数の説明 -/

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
#check zero_add a


example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]



example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

/- rewrite で示す -/
example : (a - b)^2 = a^2 - 2*a*b + b^2 := by sorry

/- calc を使う -/
example : (a - b)^2 = a^2 - 2*a*b + b^2 := by sorry

/- 課題 -/
example  : a^2 - b^2 = (a -b)*(a + b) := by ring
--  calc
--    _ = a*a + a*b - a*b - b*b := by ring
--    _ = a*(a + b) - a*b - b*b := by ring
--    _ = a*(a + b) + (-b)*(a) + (-b)*b := by ring
--    _ = a*(a + b) + (-b)*(a + b) := by ring
--    _ = (a + (-b))*(a + b) := by ring
--

/- 課題 -/

example : (a + b + c)*(a^2 + b^2 + c^2 - a - b -c) = a^3 + b^3 + c^3 - 3*a*b*c := by
  sorry

variable (x y : ℝ)

example (h : 2*x + 1 = 3) : x = 1 := by
  calc
    _  = (1/2)*(2*x + 1) - 1/2 := by ring
    _  = (1/2)*3 - 1/2 := by rw [h]
    _ = 1 := by norm_num

example (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 := by
  sorry

example (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : y = 6 := by
  sorry

end
