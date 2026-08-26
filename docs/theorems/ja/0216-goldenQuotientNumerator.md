# 0216 — `goldenQuotientNumerator`

## Lean の型

```lean
/-- Numerator coordinates of `x * conjugate(y)`. -/
def goldenQuotientNumerator (x y : GoldenInt) : GoldenInt :=
  goldenMul x (goldenConj y)
```

これは `theorem` ではなく `def` であり、黄金整数 `x,y` に対して、有理商 `x / y` を構成するときの分子 `x * conjugate(y)` を `GoldenInt` として名前付けする。

## 数学的主張・宣言の意味

黄金整数を

$$
x=a+b\varphi,\qquad y=c+d\varphi
$$

とする。二次拡大では、通常

$$
\frac{x}{y}=\frac{x\overline y}{y\overline y}
=\frac{x\overline y}{N(y)}
$$

と共役を掛けて分母を整数ノルムへ落とす。本定義はこの式の分子

$$
x\overline y
$$

をそのまま `GoldenInt` として取り出したものである。

0163 `goldenConj` により

$$
\overline y=(c+d)-d\varphi
$$

なので、`goldenMul` を展開すると後続 0217・0218 で

$$
(x\overline y).\mathrm{fst}=a(c+d)-bd,
$$

$$
(x\overline y).\mathrm{snd}=bc-ad
$$

が得られる。したがって `goldenQuotientNumerator` は、二次体での共役有理化を整数座標のまま実装する中間層である。

## 証明全体での役割

`GoldenEuclidean.lean` は、黄金整数環を `EuclideanDomain` にするため、非零 `y` に対して最近接格子点を使った quotient と remainder を構成する。

0209–0214 では有理座標と丸め誤差 cell の strict norm contraction を準備し、0215 では

$$
y\neq0\Longrightarrow N(y)\neq0
$$

を証明して分母の安全性を確保した。本 0216 からは実際の quotient

$$
\frac{x\overline y}{N(y)}
$$

を座標化する段階に入る。

正本 source では、本定義の直後に

- 0217 `goldenQuotientNumerator_fst`
- 0218 `goldenQuotientNumerator_snd`
- `goldenQuotientCoords`
- `goldenQuotient`
- `goldenRemainder`

が続く。特に `goldenQuotientCoords` は本定義の二座標を `goldenNorm y` で割り、`goldenQuotient` はそれぞれを `round` して整数座標へ戻す。

さらに下流の `goldenRemainder_norm_rat_identity` では、0217・0218 の座標公式を用いて元の座標を quotient 座標から復元し、remainder norm の縮小公式を証明する。よって本定義は Euclidean quotient の algebraic numerator を一箇所に固定する役割を持つ。

## 直接依存する定義・補題

直接依存は次の二つである。

- 0124 `goldenMul`
- 0163 `goldenConj`

型として `GoldenInt` に依存する。

定義なので theorem-level の proof 依存はない。概念的には

$$
(x,y)
\longmapsto
\overline y
\longmapsto
x\overline y
$$

という一段の構成である。

0215 `goldenNorm_ne_zero_of_ne_zero` は本定義そのものの型には不要だが、直後にこの分子を `N(y)` で割るための論理的前提として位置している。

## 構築の流れ

構築は非常に短い。

```lean
def goldenQuotientNumerator (x y : GoldenInt) : GoldenInt :=
  goldenMul x (goldenConj y)
```

1. divisor `y` の共役 `goldenConj y` を取る。
2. dividend `x` と raw multiplication `goldenMul` で掛ける。
3. 得られた黄金整数を quotient numerator として返す。

分母処理や有理数への coercion はここでは一切行わない。それらは後続 `goldenQuotientCoords` に分離されている。

## Lean 固有の処理

本定義は raw API を意図的に使用している。

```lean
goldenMul x (goldenConj y)
```

は、既に標準記法

```lean
x * goldenConj y
```

と定義的に一致するが、`goldenQuotientNumerator` 自身は `goldenMul` を明示する。これにより後続の座標 theorem で `goldenMul` と `goldenConj` を直接 `simp` 展開しやすい。

また戻り値を `GoldenRat` ではなく `GoldenInt` としているため、共役を掛けた段階までは整数格子構造を保持する。`ℚ` への移行は denominator division が必要になる次の層へ遅延されている。

この層分離は Lean 上でも有用で、0217・0218 は整数演算だけで `ring` により閉じ、その後 `goldenQuotientCoords` で初めて rational division が現れる。

## 冗長・重複箇所

数学的には本定義は単なる `x * conjugate(y)` の alias なので、情報量だけを見れば薄い wrapper である。後続で毎回

```lean
goldenMul x (goldenConj y)
```

と書くこともできる。

しかし専用名を置くことで、次の三段階が明瞭になる。

- algebraic numerator: `goldenQuotientNumerator`
- rational quotient coordinates: `goldenQuotientCoords`
- nearest integral quotient: `goldenQuotient`

Euclidean division の実装を監査する上では、この分離は有益である。

一方、標準 `*` notation が既に利用可能なので、raw `goldenMul` を使い続けるかどうかは API-level の重複候補である。

## 最適化候補

1. **現行の中間定義を維持する**
   - quotient construction の段階が明確で、後続座標 lemma の共通左辺を短くできる。

2. **標準乗法記法へ統一する**
   - `def goldenQuotientNumerator x y := x * goldenConj y` とすれば一般 ring API との接続が見やすくなる。

3. **共役を `RingEquiv` として bundle する**
   - `goldenConj` の代数的性質を generic API へ寄せ、quotient numerator の意味をより抽象化できる。

4. **0217・0218 を定義内部へ inline する**
   - `goldenQuotientCoords` を最初から明示座標式で定義すれば中間 object を減らせるが、再利用性と監査性は下がる。

5. **quadratic-order quotient numerator を一般化する**
   - 一般の二次環で `x * conj y` を quotient numerator とする構成へ抽象化できる。

現行方式はコード量より証明構造の可視性を優先しており、Euclidean-domain 構築の監査用途には適している。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本定義単独では、高度な tactic や theorem は必要なく、実質的には

- `GoldenInt`
- `goldenMul`
- `goldenConj`

だけで足りる。

ただし同じ `GoldenEuclidean.lean` module では `round`、`abs_sub_round`、`nlinarith`、`field_simp`、`ring`、Euclidean-domain API などを広く利用するため、module 全体の最小 import はかなり広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行の named intermediate `goldenQuotientNumerator`
- B: `goldenQuotientCoords` に `x * conj y` を直接 inline
- C: 標準 `*` notation のみで構成
- D: 共役を `RingEquiv` として bundle した抽象実装
- E: 一般 quadratic order の quotient numerator へ抽象化

比較軸は、downstream theorem の長さ、座標展開の容易さ、raw/standard API 境界、再利用性、数学的読みやすさ、Euclidean proof の監査性である。

特に A と B の比較は、「一行の中間定義を置くことが長い形式証明全体の見通しをどれだけ改善するか」を測る小さな Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

source では 0215 `goldenNorm_ne_zero_of_ne_zero` の直後に本定義が置かれ、その次に分子の第一・第二座標 theorem、さらに `goldenQuotientCoords` が続く。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、本定義に対応する具体的ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0217 `goldenQuotientNumerator_fst`** である。

```lean
theorem goldenQuotientNumerator_fst (x y : GoldenInt) :
    (goldenQuotientNumerator x y).fst =
      x.fst * (y.fst + y.snd) - x.snd * y.snd := by
  simp [goldenQuotientNumerator, goldenMul, goldenConj]
  ring
```

0216 が `x * conjugate(y)` を中間 object として固定したので、0217 はその第一座標を明示的な整数多項式へ展開する。続く第二座標公式と合わせて、`goldenQuotientCoords` の有理座標式を具体化する段階へ進む。
