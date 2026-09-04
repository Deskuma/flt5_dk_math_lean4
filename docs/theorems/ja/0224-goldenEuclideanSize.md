# 0224 — `goldenEuclideanSize`

## Lean の型

```lean
/-- Euclidean size is the natural absolute value of the golden norm. -/
def goldenEuclideanSize (x : GoldenInt) : ℕ :=
  Int.natAbs (goldenNorm x)
```

これは `theorem` ではなく `def` であり、黄金整数 `x` の Euclidean division を駆動する自然数値の size を、整数ノルム `goldenNorm x` の絶対値として定義する。

## 数学的主張・宣言の意味

黄金整数

$$
x=a+b\varphi
$$

のノルムは

$$
N(x)=a^2+ab-b^2\in\mathbb Z
$$

である。`goldenEuclideanSize` はこの符号付き整数ノルムから符号を捨て、

$$
\operatorname{size}(x)=|N(x)|\in\mathbb N
$$

を Euclidean measure として採用する。

Lean では `goldenNorm x : ℤ` に対して `Int.natAbs` を使うため、結果型は `ℕ` になる。これは Euclidean-domain の well-founded measure として扱うのに都合がよく、後続では remainder に対してこの自然数値が真に減少することを証明する。

## 証明全体での役割

0220–0223 までで quotient / remainder の構成と再構成 law

$$
yq+r=x
$$

が揃った。しかし Euclidean division を完成させるには、さらに remainder が divisor より「小さい」ことを well-founded な量で示す必要がある。

0224 はその比較量を定義する節目である。

正本 source では直後に、

```lean
theorem goldenEuclideanSize_pos_of_ne_zero {x : GoldenInt} (hx : x ≠ 0) :
    0 < goldenEuclideanSize x := by
  rw [goldenEuclideanSize, Int.natAbs_pos]
  exact goldenNorm_ne_zero_of_ne_zero hx
```

さらに

```lean
theorem goldenEuclideanSize_mul (x y : GoldenInt) :
    goldenEuclideanSize (goldenMul x y) =
      goldenEuclideanSize x * goldenEuclideanSize y := by
  change (goldenNorm (goldenMul x y)).natAbs =
    (goldenNorm x).natAbs * (goldenNorm y).natAbs
  rw [goldenNorm_mul, Int.natAbs_mul]
```

が続く。

そして `golden_remainder_size_lt` により

$$
\operatorname{size}(r)<\operatorname{size}(y)
$$

を証明し、最終 `goldenEuclideanDomain` instance では

```lean
r := fun a b => goldenEuclideanSize a < goldenEuclideanSize b
r_wellFounded := (measure goldenEuclideanSize).wf
remainder_lt := golden_remainder_size_lt
```

として本定義を Euclidean relation の中心へ直接登録する。

したがって 0224 は、ここまでの黄金ノルム算術を Mathlib の Euclidean-domain hierarchy へ変換する **measure interface** である。

## 直接依存する定義・補題

直接依存する定義は少ない。

- `GoldenInt`
- 0164 `goldenNorm`
- `Int.natAbs`

`def` なので proof script はなく、定義そのものは theorem に依存しない。

ただし数学的な正当性と後続利用は、特に次の上流結果に支えられる。

- 0174 `goldenNorm_mul`
- 0215 `goldenNorm_ne_zero_of_ne_zero`

前者から size の乗法性、後者から非零元の size 正値性が導かれる。

概念的には

$$
\texttt{goldenNorm}:GoldenInt\to\mathbb Z
\quad\Longrightarrow\quad
\texttt{Int.natAbs}\circ\texttt{goldenNorm}:GoldenInt\to\mathbb N
$$

という単純な合成である。

## 構築の流れ

定義は一段だけである。

```lean
def goldenEuclideanSize (x : GoldenInt) : ℕ :=
  Int.natAbs (goldenNorm x)
```

1. `x : GoldenInt` を受け取る。
2. `goldenNorm x : ℤ` を計算する。
3. `Int.natAbs` によって符号を落とし、`ℕ` の measure に変換する。

数学的にはノルムの絶対値そのものだが、Lean 上では `Int.natAbs` を使うことで、well-foundedness を自然数の `<` に委譲できる。

## Lean 固有の処理

### 1. `Int.natAbs` は結果を `ℕ` にする

`goldenNorm x` は符号を持つ整数値であり、たとえば `goldenNorm goldenPhi = -1` である。Euclidean size としては符号ではなく大きさだけが必要なので、`Int.natAbs` がちょうど適合する。

### 2. well-foundedness を自前で証明しなくてよい

最終 instance では

```lean
(measure goldenEuclideanSize).wf
```

を使うため、`GoldenInt` 上の well-founded relation を直接構築する必要がない。自然数値 measure を一つ用意すれば、Mathlib の一般 `measure` machinery が残りを担う。

### 3. signed norm と Euclidean size を分離している

`goldenNorm` は乗法性・共役・unit 判定などで符号情報を保持する必要がある。一方 Euclidean descent では絶対値のみ必要である。本定義を別名にすることで、数論的 invariant と termination measure の役割が明確に分離される。

## 冗長・重複箇所

`goldenEuclideanSize x` は数学的には単に `Int.natAbs (goldenNorm x)` なので、論理的には薄い wrapper である。downstream に毎回右辺を書けば専用定義を削除できる。

しかし dedicated name を置く利点は大きい。

- Euclidean-domain 構築で使う measure が theorem 名から明瞭になる。
- `goldenNorm` の符号付き数論的意味と、termination 用の自然数 measure を分離できる。
- 後続 theorem `goldenEuclideanSize_pos_of_ne_zero` / `goldenEuclideanSize_mul` / `golden_remainder_size_lt` の API が読みやすくなる。
- 最終 `EuclideanDomain` instance の `r` と `measure` に直接渡せる。

したがって wrapper としては薄いが、API 設計上は有用な名前付けである。

## 最適化候補

1. **現行定義を維持する**
   - 最も単純で、Euclidean construction の意図が明確。

2. **`abbrev` 化する**
   - より透明な alias とすることは可能だが、現行 `def` でも展開は容易であり利点は限定的。

3. **一般 norm-Euclidean helper を抽象化する**
   - 整数値 multiplicative norm `N : R → ℤ` と remainder contraction がある環に対して `Int.natAbs ∘ N` を size にする一般構築へ抽象化できる可能性がある。

4. **`goldenNormAbs` と Euclidean size を統一する**
   - もし downstream で整数絶対ノルムを数論用途にも多用するなら共通 API を作る余地がある。ただし `ℕ` と `ℤ` のどちらを正本にするかは慎重に選ぶ必要がある。

5. **measure theorem 群を namespace / structure に束ねる**
   - 正値性、乗法性、remainder decrease を一つの Euclidean certificate として整理すると最終 instance の監査性が上がる可能性がある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本定義単独で必要な Mathlib surface は極めて小さい。

- `Int.natAbs`
- `ℕ`, `ℤ` の基本型

ただし同じ `GoldenEuclidean.lean` module 全体では、

- `round` / `abs_sub_round`
- `field_simp`
- `linarith` / `nlinarith`
- `measure`
- `EuclideanDomain`

などを利用するため、module 全体の最小 import は大幅に広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 `Int.natAbs (goldenNorm x)` を専用 `def` とする。
- B: 専用名を置かず downstream で直接 `Int.natAbs (goldenNorm x)` を使う。
- C: 整数絶対値 `|goldenNorm x| : ℤ` を measure にしてから自然数へ変換する。
- D: 一般 norm-Euclidean certificate から size を自動生成する。
- E: quotient/remainder/size/decrease を一つの structure に bundle する。

比較軸は theorem surface の簡潔さ、well-foundedness 接続の容易さ、coercion の少なさ、数論的意味の可読性、一般化可能性、最終 `EuclideanDomain` instance の短さである。

特に A と D の比較は、明示座標実装の監査性を保ちつつどこまで一般化できるかを見るよい Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

正本 source では 0223 `golden_quotient_mul_add_remainder` の直後に本定義が置かれ、その後に `goldenEuclideanSize_pos_of_ne_zero`、`goldenEuclideanSize_mul`、remainder contraction、最終 `goldenEuclideanDomain` が続くことを確認した。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、本定義に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0225 `goldenEuclideanSize_pos_of_ne_zero`** である。

```lean
theorem goldenEuclideanSize_pos_of_ne_zero {x : GoldenInt} (hx : x ≠ 0) :
    0 < goldenEuclideanSize x := by
  rw [goldenEuclideanSize, Int.natAbs_pos]
  exact goldenNorm_ne_zero_of_ne_zero hx
```

0224 で Euclidean size を `|N(x)|` と定義したので、0225 は非零元ならこの measure が正であることを証明する。これは後続の積に対する size の単調性と、最終 `EuclideanDomain` instance の `mul_left_not_lt` を支える基礎 certificate になる。
