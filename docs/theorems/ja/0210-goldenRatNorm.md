# 0210 — `goldenRatNorm`

## Lean の型

```lean
/-- The golden norm polynomial on rational coordinates. -/
def goldenRatNorm (x : GoldenRat) : ℚ :=
  x.1 ^ 2 + x.1 * x.2 - x.2 ^ 2
```

これは theorem ではなく `def` であり、0209 `GoldenRat = ℚ × ℚ` 上に黄金整数と同じ二次ノルム多項式を有理数値で定義する。

## 数学的主張・宣言の意味

`x : GoldenRat` を座標 `(u,v)`、すなわち

$$
u+v\varphi,\qquad u,v\in\mathbb Q
$$

と読むと、`goldenRatNorm x` は

$$
Q(u,v)=u^2+uv-v^2
$$

である。これは整数座標に対する 0164 `goldenNorm`

$$
N(a+b\varphi)=a^2+ab-b^2
$$

と同じ多項式を、係数域を $\mathbb Z$ から $\mathbb Q$ へ拡張したものと見なせる。

ただし、この値は常に非負ではないので、解析的な意味での「長さ」や通常のノルムそのものではない。後続の Euclidean remainder 評価では絶対値

$$
|Q(u,v)|
$$

を用いて収縮率を測る。

## 証明全体での役割

`GoldenEuclidean.lean` の目的は `GoldenInt` に norm-Euclidean division を構成することである。source の module コメントでは、有理商を黄金基底の二座標で表し、各座標を最近接整数へ丸めることで誤差 `(u,v)` を

$$
|u|\le\frac12,\qquad |v|\le\frac12
$$

の fundamental cell に押し込む。その cell 上で

$$
|u^2+uv-v^2|\le\frac{5}{16}<1
$$

を得て、分母側のノルムを掛け戻すことで remainder の絶対ノルムが divisor より真に小さいことを示す。

`goldenRatNorm` は、この丸め誤差の二次量を一つの名前で表す中心定義である。実際に後続の `goldenRemainder_norm_rat_identity` では remainder の有理化ノルムを

$$
N(y)\,Q(\text{quotient error})
$$

という積へ分解し、さらに Euclidean-size の strict decrease proof では `goldenRatNorm` の絶対値が `1` 未満であることを直接使用する。

したがって 0210 は単なる整数ノルムのコピーではなく、整数環上の divisibility 議論から Euclidean algorithm の「局所収縮係数」へ移るための橋である。

## 直接依存する定義・補題

直接依存するのは主に次の要素である。

- 0209 `GoldenRat := ℚ × ℚ`
- `Prod.fst` / `Prod.snd` に対応する `.1` / `.2`
- 有理数 `ℚ` の加法・乗法・減法・自然数冪

`def` なので proof theorem への直接依存はない。

概念的には

$$
\texttt{GoldenRat}
\longrightarrow
Q(u,v)=u^2+uv-v^2
\longrightarrow
\texttt{goldenRatNorm}
$$

である。

整数版 `goldenNorm` と数学的な多項式は同じだが、現行 source では両者を別々の定義として置いている。

## 構築の流れ

定義はそのまま座標二次式を返す。

```lean
def goldenRatNorm (x : GoldenRat) : ℚ :=
  x.1 ^ 2 + x.1 * x.2 - x.2 ^ 2
```

1. 第一座標 `x.1` の平方を取る。
2. 交差項 `x.1 * x.2` を加える。
3. 第二座標 `x.2` の平方を引く。

黄金基底 $1,\varphi$ が満たす $\varphi^2=\varphi+1$ に対応する二次形式を、そのまま $\mathbb Q^2$ 上へ延長している。

## Lean 固有の処理

0209 `GoldenRat` は `abbrev` なので、Lean から見れば `x : GoldenRat` は実質的に `x : ℚ × ℚ` と同じであり、`.1` と `.2` を追加の coercion や projection theorem なしに利用できる。

`x.1 ^ 2` の指数 `2` は自然数冪であり、期待型から基底が `ℚ` と推論される。全演算も同様に `ℚ` 上の ring operations として elaboration される。

この透明性は後続で `simp [goldenRatNorm]` や `dsimp only [goldenNorm, goldenRatNorm]` により二次式を直接展開し、`ring` / ordered arithmetic へ渡す設計と相性がよい。

## 冗長・重複箇所

最も明確な重複は 0164 `goldenNorm` との多項式部分である。

```lean
goldenNorm x = x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

と

```lean
goldenRatNorm x = x.1 ^ 2 + x.1 * x.2 - x.2 ^ 2
```

は係数型だけが異なる。

一般化すれば同じ二次多項式を任意の適切な可換環上で一度定義し、整数版・有理版を特殊化することも可能である。一方、現行方式は各 proof で unfold した式が極めて単純になり、coercion や抽象構造を増やさない利点がある。

## 最適化候補

1. **共通二次多項式を一般化する**
   - 例えば `goldenNormPoly` を適切な ring 型上で定義し、`goldenNorm` と `goldenRatNorm` を特殊化する。

2. **整数ノルムとの cast bridge を公開する**
   - `GoldenInt` の座標を `ℚ` へ cast したとき、`goldenRatNorm` が `(goldenNorm x : ℚ)` と一致する theorem を置けば、後続の cast-heavy proof の見通しが改善する可能性がある。

3. **Mathlib の quadratic-form abstraction を使う**
   - 構造的には自然だが、今回の二変数 explicit calculation に対して abstraction cost が高い可能性がある。

4. **現行の明示式を維持する**
   - Euclidean contraction proof では直接 `ring` や不等式 tactic に渡しやすく、監査性も高い。

現時点では 4 の利点が大きいが、整数版との重複が今後さらに増えるなら 1 または 2 の価値が上がる。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。0210 単独が必要とする表面は非常に小さく、概ね

- `ℚ`
- `Prod`
- 基本 ring operations と自然数冪

だけである。

ただし `GoldenEuclidean.lean` 全体では `round`、絶対値、不等式、整数・有理数 cast、Euclidean-domain 構築などを利用するため、module 全体の最小 import はかなり広くなる。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行の `GoldenRat := ℚ × ℚ` + 直接二次式
- B: generic `goldenNormPoly` を整数版・有理版で共有
- C: Mathlib `QuadraticForm` 等へ bundle
- D: `GoldenInt` の norm を cast する bridge を中心に有理版を構成

比較軸は、proof 行数、coercion burden、`simp` / `ring` の効き方、Euclidean contraction proof の読みやすさ、一般化可能性、定義展開の透明性である。

特に A と B は、「明示座標の重複」と「抽象化による coercion 増加」の trade-off を測る良い Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

source では 0209 `GoldenRat` の直後に本定義があり、その直後に「任意の有理数には距離 `1/2` 以下の整数が存在する」0211 `exists_int_near_rat` が続く。また後段では `goldenRemainder_norm_rat_identity` と Euclidean-size の strict decrease proof が `goldenRatNorm` を実際に使用している。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本定義に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0211 `exists_int_near_rat`** である。

```lean
/-- Every rational has an integer within one half. -/
theorem exists_int_near_rat (x : ℚ) :
    ∃ n : ℤ, |x - n| ≤ (1 : ℚ) / 2 := by
  exact ⟨round x, abs_sub_round x⟩
```

0210 が丸め誤差を測る二次形式を用意したのに対し、0211 は各有理座標を整数へ丸めた誤差が `1/2` 以下に収まることを保証する。ここから二座標同時丸め、fundamental cell 上の norm bound、Euclidean remainder の strict contraction へ進む。
