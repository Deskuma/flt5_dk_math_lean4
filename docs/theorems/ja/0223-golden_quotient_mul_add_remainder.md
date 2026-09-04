# 0223 — `golden_quotient_mul_add_remainder`

## Lean の型

```lean
theorem golden_quotient_mul_add_remainder (x y : GoldenInt) :
    y * goldenQuotient x y + goldenRemainder x y = x := by
  simp [goldenRemainder, golden_mul_eq]
  ring
```

これは `theorem` であり、0220 `goldenQuotient` と 0221 `goldenRemainder` が標準的な Euclidean division identity を満たすことを示す。

## 数学的主張・宣言の意味

0221 では remainder を

$$
r=x-qy
$$

と定義した。ここで

$$
q=goldenQuotient(x,y),\qquad r=goldenRemainder(x,y)
$$

である。本 theorem はその定義を組み替え、

$$
yq+r=x
$$

を証明する。

通常の可換環では $qy=yq$ なので、

$$
yq+(x-qy)=x
$$

は純粋な環恒等式である。したがって本 theorem の数学的内容は新しい数論ではなく、ここまで構成した quotient / remainder pair が Euclidean-domain API の要求する向きで正しく再構成されることを保証する interface theorem である。

## 証明全体での役割

`GoldenEuclidean.lean` の役割は `GoldenInt` に具体的な Euclidean division を与えることにある。

この区間の流れは次の通りである。

1. 0219 `goldenQuotientCoords` — 有理 quotient coordinates を構成する。
2. 0220 `goldenQuotient` — 最近接整数へ丸めて黄金整数 quotient を選ぶ。
3. 0221 `goldenRemainder` — $r=x-qy$ を定義する。
4. 0222 `goldenQuotient_zero` — divisor `0` の quotient law を閉じる。
5. **0223 本 theorem — $yq+r=x$ を証明する。**
6. 0224 以降 — 絶対ノルムを Euclidean size として定義し、remainder が strict decrease することを証明する。
7. 最終 `goldenEuclideanDomain` instance — quotient、remainder、size とそれらの law を `EuclideanDomain GoldenInt` に登録する。

したがって 0223 は quotient / remainder の **正しさ** を担い、後続 theorem 群は remainder の **小ささ** を担う。この二つが揃って Euclidean division になる。

## 直接依存する定義・補題

直接依存は次の通りである。

- `GoldenInt`
- 0220 `goldenQuotient`
- 0221 `goldenRemainder`
- 0159 `golden_mul_eq`
- `CommRing GoldenInt` が提供する標準乗法・加法・減法
- `ring` tactic

proof は 0219 の rational coordinates、0213–0214 の contraction estimate、0215 の norm nonzero theorem を使用しない。これは重要であり、division identity 自体は quotient の選び方や divisor の非零性に依存せず、`r := x-qy` という定義だけで成立する。

概念的には

$$
\texttt{goldenRemainder}(x,y)=x-qy
\Longrightarrow
yq+\texttt{goldenRemainder}(x,y)=x.
$$

## 証明の流れ

現行 proof は二段階である。

```lean
by
  simp [goldenRemainder, golden_mul_eq]
  ring
```

### 1. remainder と raw multiplication を正規化する

`goldenRemainder` を展開すると、目標は概念的に

```lean
y * goldenQuotient x y +
  (x - goldenMul (goldenQuotient x y) y) = x
```

となる。

`golden_mul_eq` により raw operation

```lean
goldenMul (goldenQuotient x y) y
```

を標準記法

```lean
goldenQuotient x y * y
```

へ接続する。

### 2. `ring` で可換環恒等式を閉じる

残る目標は

$$
yq+(x-qy)=x
$$

の形であり、`GoldenInt` が既に `CommRing` なので `ring` が乗法可換性と加減法を正規化して閉じる。

## Lean 固有の処理

### 1. theorem statement は `y * q`、remainder 定義は `q * y`

0221 は

```lean
goldenRemainder x y :=
  x - goldenMul (goldenQuotient x y) y
```

と `q*y` の順で定義されている。一方 0223 の statement は `y*q+r=x` である。

この順序差は `GoldenInt` が可換環であるため数学的には問題にならず、`ring` が吸収する。

### 2. `golden_mul_eq` が raw / standard API 境界を埋める

`goldenRemainder` は raw `goldenMul` を使う一方、theorem statement は標準 `*` を使う。0159 `golden_mul_eq` が両者を definitionally compatible な surface として接続する。

### 3. divisor `0` の場合も theorem はそのまま成立する

0223 には `y ≠ 0` 仮定がない。`y=0` の場合でも 0222 により quotient は `0` だが、それを使わずとも remainder 定義から恒等式は成立する。

これは Euclidean-domain の quotient/remainder identity が total operation として全 `x,y` に対して要求される設計と整合する。

## 冗長・重複箇所

本 theorem は `goldenRemainder` の定義からほぼ自明であり、論理的には独立した深い内容を持たない。しかし最終 `EuclideanDomain` instance にそのまま渡せる named theorem として価値がある。

また proof 中の `golden_mul_eq` は raw `goldenMul` と標準 `*` の二重 API があるため必要になっている。もし `goldenRemainder` を最初から

```lean
x - goldenQuotient x y * y
```

と定義すれば、この bridge は不要になる可能性がある。

一方、現在の Euclidean layer が explicit golden-coordinate API を追跡する方針なら、raw operation を維持することにも監査上の利点がある。

## 最適化候補

1. **`goldenRemainder` を標準 `*` で定義する**
   - `golden_mul_eq` rewrite を減らせる可能性がある。

2. **theorem statement を `q*y+r=x` に合わせる**
   - remainder 定義との向きを一致させれば `ring` より軽い `simp` / `abel` 系で閉じられる可能性がある。ただし `EuclideanDomain` の field が `b*q+r=a` の順を要求するなら現行 statement の方が interface に直接対応する。

3. **`simpa [goldenRemainder, golden_mul_eq]` を試す**
   - simp が可換性まで処理できるかは build 未検証。現行 `ring` は確実で読みやすい。

4. **quotient/remainder pair を bundle する**
   - quotient、remainder、再構成 identity、strict-size certificate を一つの structure にまとめれば、最終 instance への接続が明示的になる。

5. **一般 quadratic-order Euclidean division へ抽象化する**
   - `r=x-qy` から reconstruction law を得る部分は golden order 固有ではないため、一般 helper として再利用可能である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem が直接必要とする Mathlib surface は小さい。

- simplifier `simp`
- `ring` tactic
- 可換環の加法・乗法・減法

`round`、`field_simp`、`nlinarith`、有理数の最近接整数 theorem は本 theorem 自体では使わない。

ただし同じ `GoldenEuclidean.lean` module 全体では rounding、rational arithmetic、nonlinear inequality、Euclidean-domain hierarchy を使用するため、module の正確な最小 import は本 theorem 単独より広い。

今回は Lean build を行わないため、最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 `simp [goldenRemainder, golden_mul_eq]; ring`
- B: `goldenRemainder` を標準 `*` で定義して simplification のみで閉じる実装
- C: explicit `calc` で `y*q + (x-q*y) = x` を変形する proof
- D: quotient/remainder bundle の reconstruction law を再利用する proof
- E: 一般 commutative-ring helper theorem を適用する proof

比較軸は proof 長、raw/standard API 境界の露出度、`ring` 依存、実装変更への頑健性、`EuclideanDomain` への接続の自然さ、一般化可能性である。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

正本 source では 0222 `goldenQuotient_zero` の直後に本 theorem があり、さらにその直後に 0224 `goldenEuclideanSize` が定義されることを確認した。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、本 theorem に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0224 `goldenEuclideanSize`** である。

```lean
/-- Euclidean size is the natural absolute value of the golden norm. -/
def goldenEuclideanSize (x : GoldenInt) : ℕ :=
  Int.natAbs (goldenNorm x)
```

0223 までで quotient/remainder の再構成 law が揃った。0224 からは Euclidean induction を駆動する size を

$$
|N(x)|\in\mathbb N
$$

として定義し、非零なら正、積に対して乗法的、remainder では strict decrease することを順に証明する段階へ進む。