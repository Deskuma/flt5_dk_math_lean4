# 0230 — `goldenEuclideanDomain`

## Lean の型

```lean
/-- Euclidean division for the absolute norm, with well-founded measure
`natAbs (goldenNorm x)`. -/
noncomputable instance goldenEuclideanDomain : EuclideanDomain GoldenInt where
  quotient := goldenQuotient
  quotient_zero := goldenQuotient_zero
  remainder := goldenRemainder
  quotient_mul_add_remainder_eq := golden_quotient_mul_add_remainder
  r := fun a b => goldenEuclideanSize a < goldenEuclideanSize b
  r_wellFounded := (measure goldenEuclideanSize).wf
  remainder_lt := golden_remainder_size_lt
  mul_left_not_lt := by
    intro a b hb
    apply not_lt_of_ge
    rw [← golden_mul_eq, goldenEuclideanSize_mul]
    have hbSize : 1 ≤ goldenEuclideanSize b :=
      goldenEuclideanSize_pos_of_ne_zero hb
    exact Nat.le_mul_of_pos_right _ hbSize
```

これは theorem ではなく `noncomputable instance` であり、ここまで構成してきた黄金整数環 `GoldenInt` に Mathlib 標準の `EuclideanDomain` 構造を登録する。

## 数学的主張・宣言の意味

この instance の数学的内容は、黄金整数環

$$
\mathbb Z[\varphi],\qquad \varphi^2=\varphi+1
$$

が絶対ノルム

$$
\operatorname{size}(x)=|N(x)|
$$

に関して Euclidean domain である、ということに相当する。

すなわち任意の $x,y\in\mathbb Z[\varphi]$ に対し、$y\neq0$ なら quotient $q$ と remainder $r$ を選べて、

$$
x=yq+r
$$

かつ

$$
|N(r)|<|N(y)|
$$

となる。

この development では quotient を $x/y$ の黄金基底上の有理座標を各成分で最近接整数へ丸めて構成し、その rounding error が入る fundamental cell 上で黄金ノルム二次形式

$$
Q(u,v)=u^2+uv-v^2
$$

が

$$
|Q(u,v)|\le\frac5{16}<1
$$

となることから strict decrease を得ている。

## 証明全体での役割

0230 は `GoldenEuclidean.lean` 全体の integration point である。

0209–0229 では、以下の部品を順に構築してきた。

- 有理座標 `GoldenRat`
- 有理ノルム `goldenRatNorm`
- 最近接整数丸め
- fundamental cell 上の $5/16$ bound
- 非零元のノルム非零性
- 有理化分子 `x * conjugate(y)`
- rational quotient coordinates
- 最近接格子 quotient `goldenQuotient`
- remainder `goldenRemainder`
- quotient/remainder identity
- Euclidean size `natAbs (goldenNorm x)`
- size の正性と乗法性
- remainder norm identity
- strict remainder decrease
- quotient/remainder witness package

本 instance はそれらを Mathlib の `EuclideanDomain` interface に一度に接続する。

この登録以降は、`GoldenInt` に対して gcd、Euclidean algorithm、coprimality、divisibility などの一般 API を利用できるようになる。standalone source の module header でも、後続の `GoldenCoprimeFactor` がこの Euclidean-domain 構造から得られる gcd theory を使って fifth power の coprime factor splitting を行うと説明されている。

したがって本宣言は、明示座標で築いてきた黄金整数算術が Mathlib の抽象代数階層へ完全に接続される大きな節目である。

## 直接依存する定義・補題

instance field に直接現れる依存は次の通りである。

- 0220 `goldenQuotient`
- 0222 `goldenQuotient_zero`
- 0221 `goldenRemainder`
- 0223 `golden_quotient_mul_add_remainder`
- 0224 `goldenEuclideanSize`
- 0228 `golden_remainder_size_lt`
- 0159 `golden_mul_eq`
- 0226 `goldenEuclideanSize_mul`
- 0225 `goldenEuclideanSize_pos_of_ne_zero`
- Mathlib `measure`
- Mathlib `Nat.le_mul_of_pos_right`

また `EuclideanDomain GoldenInt` の前提として、既に `GoldenInt` は可換環かつ整域として構築済みである。

概念的には、

$$
\text{explicit quotient/remainder}
+
\text{well-founded size}
+
\text{strict remainder decrease}
\Longrightarrow
\texttt{EuclideanDomain GoldenInt}
$$

という構成である。

## 構築の流れ

### 1. quotient と zero branch

```lean
quotient := goldenQuotient
quotient_zero := goldenQuotient_zero
```

0220 の最近接格子 quotient を標準 Euclidean quotient として登録し、0222 で divisor が `0` の場合の全域仕様を与える。

### 2. remainder と再構成則

```lean
remainder := goldenRemainder
quotient_mul_add_remainder_eq := golden_quotient_mul_add_remainder
```

0221 の

$$
r=x-qy
$$

を remainder として登録し、0223 の

$$
yq+r=x
$$

を `EuclideanDomain` が要求する reconstruction law として渡す。

### 3. Euclidean relation

```lean
r := fun a b => goldenEuclideanSize a < goldenEuclideanSize b
r_wellFounded := (measure goldenEuclideanSize).wf
```

relation は自然数値 size の `<` とする。

$$
a\;r\;b
\iff
|N(a)|<|N(b)|.
$$

`measure goldenEuclideanSize` により、この relation の well-foundedness は自然数 `<` の well-foundedness から自動的に得られる。

### 4. remainder strict decrease

```lean
remainder_lt := golden_remainder_size_lt
```

0228 で証明した

$$
|N(r)|<|N(y)|
$$

を、そのまま Euclidean remainder condition に登録する。

### 5. 左乗法による relation の非減少

最後の field は、非零 `b` を左側へ掛けても size が小さくなりすぎないことを示す。

```lean
mul_left_not_lt := by
  intro a b hb
  apply not_lt_of_ge
  rw [← golden_mul_eq, goldenEuclideanSize_mul]
  have hbSize : 1 ≤ goldenEuclideanSize b :=
    goldenEuclideanSize_pos_of_ne_zero hb
  exact Nat.le_mul_of_pos_right _ hbSize
```

0226 により

$$
\operatorname{size}(ab)
=
\operatorname{size}(a)\operatorname{size}(b)
$$

であり、0225 から $b\neq0$ なら

$$
1\le\operatorname{size}(b)
$$

なので、

$$
\operatorname{size}(a)
\le
\operatorname{size}(a)\operatorname{size}(b)
$$

を得る。

## Lean 固有の処理

`noncomputable instance` である点が重要である。

数学的 quotient は具体的に `round` を使って定義されているが、`EuclideanDomain` structure 自体やその周辺 API が classical / noncomputable な要素を含むため、この instance は `noncomputable` として登録されている。これは数学的存在性の不足ではなく、Lean の計算可能性管理上の指定である。

```lean
r_wellFounded := (measure goldenEuclideanSize).wf
```

は、独自に well-founded recursion を証明する代わりに、自然数への measure map から標準 theorem を利用している。

また

```lean
rw [← golden_mul_eq, goldenEuclideanSize_mul]
```

では、標準乗法 `a * b` を raw API `goldenMul a b` へ一旦戻してから、0226 の size 乗法性 theorem を適用している。0196–0197 でも見られた raw / standard multiplication の API 境界がここにも現れている。

## 冗長・重複箇所

本 instance 自体の重複は少ない。むしろ 0209–0229 の補助 theorem を集約する役割を担う。

ただし以下の API-level 重複は見える。

1. `goldenMul` と標準 `*` の二重 API
   - `mul_left_not_lt` で `golden_mul_eq` により往復している。

2. 0229 `exists_golden_quotient_remainder`
   - 数学的には Euclidean division の存在を既に package しているが、`EuclideanDomain` instance は quotient/remainder function と個別 law を要求するため、0229 自体を直接 field として使うわけではない。

3. `goldenEuclideanSize` の明示 wrapper
   - 実体は `Int.natAbs (goldenNorm x)` であるが、名前を付けることで relation と downstream theorem の可読性が大きく向上している。

このため、論理的には薄い wrapper が存在しても API 設計上は有益なものが多い。

## 最適化候補

1. **標準乗法版の size theorem を追加する**

```lean
goldenEuclideanSize (x * y) =
  goldenEuclideanSize x * goldenEuclideanSize y
```

を公開すれば `mul_left_not_lt` で `← golden_mul_eq` が不要になる。

2. **Euclidean division certificate を structure 化する**

quotient、remainder、reconstruction、strict decrease を一つの内部 certificate にまとめれば、0229 と instance 構築の重複を減らせる可能性がある。

3. **一般 quadratic-order abstraction**

今回の最近接格子丸め + norm contraction の構成を一般の二次形式へ抽象化できれば、黄金整数固有コードを減らせる可能性がある。ただし $5/16$ bound は黄金ノルム固有なので、抽象化しすぎると proof が読みにくくなる。

4. **既存 Mathlib quadratic integer infrastructure との比較**

`AdjoinRoot`、quadratic algebra、既存 Euclidean-domain instance が利用可能なら、それらとの実装量・透明性・simp behavior を比較する価値がある。

現行設計は長いが、quotient selection から strict decrease までをすべて明示しているため、証明監査性は非常に高い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 instance 自身が直接使う Mathlib 表面は主に次の通りである。

- `EuclideanDomain`
- `measure`
- well-foundedness API
- `Nat.le_mul_of_pos_right`
- order lemmas `not_lt_of_ge`

ただし `GoldenEuclidean.lean` module 全体ではさらに、

- rational rounding
- `abs_sub_round`
- `nlinarith`
- `linarith`
- `field_simp`
- `exact_mod_cast`
- integer `natAbs`
- ring normalization

などを使用するため、module 全体の最小 import はかなり広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

非常に適している。0230 は実装方式の比較点として特に価値が高い。

比較候補は次の通り。

- A: 現行の明示座標 + 最近接格子 rounding + $5/16$ bound
- B: Mathlib の既存 quadratic integer / Euclidean-domain infrastructure を再利用
- C: `AdjoinRoot (X^2-X-1)` から抽象的に構築
- D: norm-nearest lattice point を直接最適化する quotient 選択
- E: quotient/remainder certificate を内部 structure 化して instance を薄くする実装

比較軸は、

- theorem 数
- proof 行数
- `rfl` / `simp` の強さ
- quotient の具体性
- strict decrease の数学的透明性
- Mathlib 依存深度
- downstream gcd / coprimality proof の簡潔さ
- 一般化可能性

である。

特に A と B の比較は、「明示座標の監査可能性」と「既存抽象 algebra hierarchy の再利用性」の trade-off を測るよい Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

source の module header では、黄金整数の rational quotient を両座標で丸め、fundamental cell 上の

$$
|u^2+uv-v^2|\le\frac5{16}<1
$$

から remainder の絶対ノルムを divisor より小さくし、最終的に `GoldenInt` を `EuclideanDomain` にすることが明記されている。

対象ブランチには既存の日英 PDF があるが、本 instance に対応する具体的ページ・節番号は今回直接特定できていないため推測しない。

## 次に読むべき宣言

`goldenEuclideanDomain` で `GoldenEuclidean.lean` は終了する。

依存順の次は次 module `SignedGoldenRamifierStripped.lean` の先頭にある **0231 `SignedGoldenRamifierStrippedPacket`** である。

```lean
structure SignedGoldenRamifierStrippedPacket (u v w : ℕ) : Type where
  exceptional : SignedSquareGoldenExceptionalPacket u v w
  alpha : GoldenInt
  beta : GoldenInt
  k : ℤ
  alpha_eq : alpha = ⟨exceptional.M, exceptional.N⟩
  linear_eq : 2 * exceptional.M + exceptional.N = 5 * k
  alpha_eq_tau_mul : alpha = goldenMul goldenTau beta
  beta_eq : beta = ⟨exceptional.M - k, 2 * k - exceptional.M⟩
  beta_norm : goldenNorm beta = (exceptional.powerSplit.b : ℤ) ^ 5
  beta_snd : beta.snd = -(5 : ℤ) ^ 7 * (exceptional.powerSplit.a : ℤ) ^ 10
  five_not_dvd_b : ¬ 5 ∣ exceptional.powerSplit.b
  five_not_dvd_beta_norm : ¬ (5 : ℤ) ∣ goldenNorm beta
  tau_not_dvd_beta : ¬ ∃ gamma : GoldenInt, beta = goldenMul goldenTau gamma
```

0230 までで黄金整数環そのものの Euclidean-domain infrastructure が完成し、0231 からは exceptional packet から唯一見えている ramified factor `tau` を除去した後の `beta` を package し、FLT5 の exceptional branch の本体へ戻る。