# 0228 — `golden_remainder_size_lt`

## Lean の型

```lean
theorem golden_remainder_size_lt (x : GoldenInt) {y : GoldenInt} (hy : y ≠ 0) :
    goldenEuclideanSize (goldenRemainder x y) < goldenEuclideanSize y := by
  let A := (goldenQuotientCoords x y).1
  let B := (goldenQuotientCoords x y).2
  have hA : |A - round A| ≤ (1 : ℚ) / 2 := abs_sub_round A
  have hB : |B - round B| ≤ (1 : ℚ) / 2 := abs_sub_round B
  have hcell : |goldenRatNorm (A - round A, B - round B)| < 1 := by
    simpa [goldenRatNorm] using goldenRat_norm_abs_lt_one hA hB
  have hnpos : 0 < |(goldenNorm y : ℚ)| := abs_pos.mpr (by
    exact_mod_cast goldenNorm_ne_zero_of_ne_zero hy)
  have hid := goldenRemainder_norm_rat_identity x y hy
  have hrat : |(goldenNorm (goldenRemainder x y) : ℚ)| <
      |(goldenNorm y : ℚ)| := by
    rw [hid, abs_mul]
    have := mul_lt_mul_of_pos_left hcell hnpos
    simpa [A, B, goldenQuotient] using this
  have hInt : |goldenNorm (goldenRemainder x y)| < |goldenNorm y| := by
    exact_mod_cast hrat
  change (goldenNorm (goldenRemainder x y)).natAbs <
    (goldenNorm y).natAbs
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hInt
  exact_mod_cast hInt
```

これは `theorem` であり、非零の除数 `y` に対して、0220 `goldenQuotient` と 0221 `goldenRemainder` が作る最近接格子型の剰余が、0224 `goldenEuclideanSize` に関して除数より真に小さいことを証明する。

## 数学的主張

主張は

$$
 y\neq0
 \Longrightarrow
 \operatorname{size}(r)<\operatorname{size}(y),
$$

ここで

$$
 r=x-qy,
 \qquad
 \operatorname{size}(z)=|N(z)|_{\mathbb N}
$$

である。

`q = goldenQuotient x y` は、有理商

$$
\frac{x}{y}
=
\frac{x\overline y}{N(y)}
$$

の黄金基底座標を各々最近接整数へ丸めて得る。丸め前の座標を

$$
A=(goldenQuotientCoords\ x\ y)_1,
\qquad
B=(goldenQuotientCoords\ x\ y)_2
$$

とすると、丸め誤差は

$$
|A-\operatorname{round}(A)|\le\frac12,
\qquad
|B-\operatorname{round}(B)|\le\frac12
$$

を満たす。

0227 `goldenRemainder_norm_rat_identity` は剰余ノルムを

$$
N(r)
=
N(y)\,
Q\bigl(A-m,B-n\bigr)
$$

と分解する。ここで

$$
Q(u,v)=u^2+uv-v^2,
\qquad
m=\operatorname{round}(A),
\qquad
n=\operatorname{round}(B).
$$

0214 `goldenRat_norm_abs_lt_one` により fundamental cell 内では

$$
|Q(A-m,B-n)|<1
$$

なので、`y ≠ 0` から $|N(y)|>0$ を使えば

$$
|N(r)|
=
|N(y)|\,|Q(A-m,B-n)|
<
|N(y)|
$$

を得る。最後に整数絶対値を `Int.natAbs` へ移せば、

$$
goldenEuclideanSize(r)
<
goldenEuclideanSize(y)
$$

となる。

## 証明全体での役割

これは `GoldenEuclidean.lean` の Euclidean-domain 構築における **strict decrease theorem 本体** である。

前段では次の部品が順に用意された。

- 0209 `GoldenRat` — 有理 quotient 座標。
- 0210 `goldenRatNorm` — 有理座標上の黄金ノルム二次形式。
- 0211–0212 — 最近接整数丸めで誤差を各座標 `1/2` 以下へ入れる。
- 0213 — fundamental cell 上の鋭い bound `5/16`。
- 0214 — それを Euclidean contraction に必要な `< 1` へ変換。
- 0215 — 非零除数なら `N(y) ≠ 0`。
- 0216–0219 — 有理商 `x/y` の座標構築。
- 0220 — quotient を整数格子へ丸める。
- 0221 — remainder `r = x - qy`。
- 0224 — Euclidean size `natAbs (goldenNorm x)`。
- 0227 — `N(r)=N(y)Q(error)` という完全分解。

0228 はこれらを一つに束ね、最終的な減少条件

$$
size(r)<size(y)
$$

を与える。

直後の `exists_golden_quotient_remainder` は本 theorem を使って Euclidean division の witness を package し、その後の `goldenEuclideanDomain` instance は

```lean
remainder_lt := golden_remainder_size_lt
```

として本 theorem をそのまま `EuclideanDomain` の field に登録する。

したがって 0228 は、`GoldenInt` が単なる整域から Euclidean domain へ昇格するための中心 certificate である。

## 直接依存する定義・補題

主な直接依存は次の通りである。

- 0214 `goldenRat_norm_abs_lt_one`
- 0215 `goldenNorm_ne_zero_of_ne_zero`
- 0219 `goldenQuotientCoords`
- 0220 `goldenQuotient`
- 0221 `goldenRemainder`
- 0224 `goldenEuclideanSize`
- 0227 `goldenRemainder_norm_rat_identity`
- `goldenRatNorm`
- Mathlib `round`
- Mathlib `abs_sub_round`
- Mathlib `abs_pos`
- Mathlib `abs_mul`
- `mul_lt_mul_of_pos_left`
- `exact_mod_cast`
- `Int.abs_eq_natAbs`

概念的な依存は

$$
y\neq0
\Longrightarrow |N(y)|>0,
$$

$$
|error_i|\le\frac12
\Longrightarrow |Q(error)|<1,
$$

$$
N(r)=N(y)Q(error)
\Longrightarrow |N(r)|<|N(y)|
\Longrightarrow size(r)<size(y).
$$

と整理できる。

## 証明の流れ

### 1. rational quotient coordinates に短名を付ける

```lean
let A := (goldenQuotientCoords x y).1
let B := (goldenQuotientCoords x y).2
```

以後の式を `goldenQuotientCoords` の長い projection から切り離し、連続 quotient 座標を $(A,B)$ として扱う。

### 2. 最近接整数丸めの誤差を確保する

```lean
have hA : |A - round A| ≤ (1 : ℚ) / 2 := abs_sub_round A
have hB : |B - round B| ≤ (1 : ℚ) / 2 := abs_sub_round B
```

Mathlib の `abs_sub_round` により、二座標とも誤差は `1/2` 以下に入る。

### 3. fundamental cell の golden norm が 1 未満であることを得る

```lean
have hcell : |goldenRatNorm (A - round A, B - round B)| < 1 := by
  simpa [goldenRatNorm] using goldenRat_norm_abs_lt_one hA hB
```

0214 は二次形式を直接書いた theorem なので、`goldenRatNorm` を展開する `simpa` で consumer-facing な形へ合わせている。

### 4. 除数ノルムの絶対値が正であることを得る

```lean
have hnpos : 0 < |(goldenNorm y : ℚ)| := abs_pos.mpr (by
  exact_mod_cast goldenNorm_ne_zero_of_ne_zero hy)
```

0215 の整数上の nonzero theorem を `ℚ` へ cast し、`abs_pos.mpr` に渡して strict positivity へ変換する。

この positivity が、`|Q(error)|<1` の両辺に `|N(y)|` を掛けても strict inequality を保つために必要である。

### 5. 0227 の remainder norm identity を呼ぶ

```lean
have hid := goldenRemainder_norm_rat_identity x y hy
```

これにより

$$
N(r)=N(y)Q(error)
$$

が利用可能になる。

### 6. 有理数上で strict norm contraction を証明する

```lean
have hrat : |(goldenNorm (goldenRemainder x y) : ℚ)| <
    |(goldenNorm y : ℚ)| := by
  rw [hid, abs_mul]
  have := mul_lt_mul_of_pos_left hcell hnpos
  simpa [A, B, goldenQuotient] using this
```

`hid` と `abs_mul` を使うと左辺は

$$
|N(y)|\,|Q(error)|
$$

になる。

`mul_lt_mul_of_pos_left hcell hnpos` は

$$
|Q(error)|<1
$$

へ正の係数 $|N(y)|$ を掛け、

$$
|N(y)|\,|Q(error)|<|N(y)|
$$

を得る。

`simpa [A, B, goldenQuotient]` は、`round A`, `round B` と `goldenQuotient` の座標が同じであることを定義展開で合わせる。

### 7. `ℚ` 上の不等式を `ℤ` 上へ戻す

```lean
have hInt : |goldenNorm (goldenRemainder x y)| < |goldenNorm y| := by
  exact_mod_cast hrat
```

整数ノルムの絶対値 inequality へ戻す。

### 8. 整数絶対値から natural Euclidean size へ移す

```lean
change (goldenNorm (goldenRemainder x y)).natAbs <
  (goldenNorm y).natAbs
rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at hInt
exact_mod_cast hInt
```

0224 の `goldenEuclideanSize` を展開した目標を `Int.natAbs` の inequality にし、`Int.abs_eq_natAbs` を使って `hInt` を natural-number measure へ移送する。

これで Euclidean decrease condition が完成する。

## Lean 固有の処理

この theorem は数学そのものより、`ℤ`・`ℚ`・`ℕ` の三層を安全に行き来する Lean 処理が重要である。

- `exact_mod_cast` は `goldenNorm y ≠ 0 : ℤ` を `ℚ` 上の nonzero/inequality へ移す。
- `abs_pos.mpr` は nonzero を absolute-value positivity へ変換する。
- `simpa [A, B, goldenQuotient]` は local `let` と quotient の座標定義を解消する。
- `Int.abs_eq_natAbs` は整数絶対値と自然数絶対値の橋になる。
- 最後の `exact_mod_cast` は整数 absolute-value inequality と natural `natAbs` inequality の型差を処理する。

また 0227 が `private theorem` であるため、0228 はその内部 algebraic identity を外部 API に露出させず、公開側には「remainder size が減る」という Euclidean-domain に直接意味のある theorem だけを出している。

## 冗長・重複箇所

proof 中では型変換が何度も現れる。

特に

```lean
exact_mod_cast goldenNorm_ne_zero_of_ne_zero hy
```

と

```lean
exact_mod_cast hrat
```

および最後の `Int.abs_eq_natAbs` + `exact_mod_cast` は、`goldenEuclideanSize` が `ℕ`、`goldenNorm` が `ℤ`、0227 が `ℚ` 上の identity であることに由来する representation overhead である。

数学的には一行の

$$
|N(r)|=|N(y)|\,|Q(error)|<|N(y)|
$$

を、三つの数体系をまたいで証明している。

また `hA`, `hB` は 0212 `exists_goldenRat_near_int` と同種の nearest-rounding 情報だが、0220 が concrete witness として `round` を固定しているため、ここでは existential theorem 0212 を再利用せず `abs_sub_round` を直接使っている。

これは軽い重複だが、witness が既に canonical に決まっているため現行方式の方が短い。

## 最適化候補

1. **`goldenRatNorm` 版 contraction theorem を直接用意する**
   - 0214 が `goldenRatNorm (u,v)` を statement に直接持てば、0228 の `simpa [goldenRatNorm]` を消せる。

2. **rounded quotient error を専用定義として bundle する**
   - `(A-round A, B-round B)` を `goldenQuotientError x y` のような定義にすれば、0227/0228 間の長い座標式を短くできる。

3. **absolute norm を `ℚ` まで一貫して扱う補助 theorem を作る**
   - `natAbs` への変換を最後の一箇所に集約できる可能性がある。

4. **`goldenEuclideanSize` の比較と整数 abs 比較の iff lemma を用意する**
   - `goldenEuclideanSize a < goldenEuclideanSize b ↔ |N(a)| < |N(b)|` の適切な形を用意すれば末尾の cast 操作を隠蔽できる。

5. **現行構造を維持する**
   - 0227 を internal exact identity、0228 を public strict-decrease theorem とする分離は設計上かなり良い。最適化するなら主に cast boilerplate に限定するのが自然である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem が直接触れる Mathlib 表面には少なくとも次がある。

- `round`
- `abs_sub_round`
- `abs_pos`
- `abs_mul`
- `mul_lt_mul_of_pos_left`
- `exact_mod_cast`
- `Int.abs_eq_natAbs`
- 有理数・整数・自然数間 coercion

また依存 theorem 0214 は `linarith` / `norm_num`、0227 は `field_simp` / `push_cast` / `ring` を使うため、`GoldenEuclidean.lean` 全体ではさらに広い tactic/import surface が必要である。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

非常に適している。Euclidean-domain 構築の proof engineering 比較として価値が高い。

比較候補は次の通り。

- A: 現行の `ℚ` 上 identity → strict inequality → `ℤ` → `ℕ` への cast chain。
- B: absolute norm comparison helper を先に構築して cast boilerplate を隠蔽する方式。
- C: `GoldenRat` を quadratic algebra として構造化し、norm multiplicativityを generic API で使う方式。
- D: quotient error と contraction certificate を bundled structure として返す方式。
- E: Euclidean functionを直接 `ℤ` の絶対値関係で設計し、最後に well-founded natural measureへ変換する方式。

比較軸は、proof 行数、cast 操作数、Mathlib tactic 依存、数学的透明性、EuclideanDomain instance への接続の短さ、一般 quadratic order への再利用性である。

特に A と B の比較は、現行の明示性を保ちながら Lean 固有の coercion noise をどこまで削減できるかを見る良い課題になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

正本 source では、0227 `goldenRemainder_norm_rat_identity` の直後に本 theorem があり、その後

```lean
theorem exists_golden_quotient_remainder ...
```

および

```lean
noncomputable instance goldenEuclideanDomain : EuclideanDomain GoldenInt where
  ...
  remainder_lt := golden_remainder_size_lt
  ...
```

へ続くことを確認した。

既存の日英 PDF に対応する具体的ページ・節番号は今回特定できていないため、ページ番号は推測しない。

## 次に読むべき宣言

依存順の次は **0229 `exists_golden_quotient_remainder`** である。

```lean
theorem exists_golden_quotient_remainder
    (x y : GoldenInt) (hy : y ≠ 0) :
    ∃ q r : GoldenInt,
      x = q * y + r ∧
      (r = 0 ∨ goldenEuclideanSize r < goldenEuclideanSize y) := by
  refine ⟨goldenQuotient x y, goldenRemainder x y, ?_, ?_⟩
  · simp [goldenRemainder, golden_mul_eq]
  · exact Or.inr (golden_remainder_size_lt x hy)
```

0228 が Euclidean decrease condition を完成させたので、0229 は quotient と remainder の witness を一つの existential package として公開する。

その次はいよいよ `goldenEuclideanDomain : EuclideanDomain GoldenInt` instance であり、0228 はその `remainder_lt` field に直接使われる。