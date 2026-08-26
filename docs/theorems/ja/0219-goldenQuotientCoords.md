# 0219 — `goldenQuotientCoords`

## Lean の型

```lean
/-- Rational coordinates of `x/y` in the golden basis. -/
def goldenQuotientCoords (x y : GoldenInt) : GoldenRat :=
  (((goldenQuotientNumerator x y).fst : ℚ) / goldenNorm y,
    ((goldenQuotientNumerator x y).snd : ℚ) / goldenNorm y)
```

これは `theorem` ではなく `def` であり、二つの黄金整数 `x`,`y` に対して、黄金基底 `1,φ` における有理商 `x/y` の二座標を `GoldenRat = ℚ × ℚ` として定義する。

## 数学的主張・宣言の意味

`x=a+bφ`、`y=c+dφ` と書く。黄金共役とノルムにより、非零 `y` について形式的には

$$
\frac{x}{y}=\frac{x\overline y}{N(y)}
$$

と有理化できる。

0216 `goldenQuotientNumerator` は分子

$$
x\overline y
$$

を `GoldenInt` として定義し、0217・0218 はその座標を

$$
(x\overline y).\mathrm{fst}=a(c+d)-bd,
$$

$$
(x\overline y).\mathrm{snd}=bc-ad
$$

と明示した。

したがって本定義は

$$
\operatorname{goldenQuotientCoords}(x,y)
=
\left(
\frac{a(c+d)-bd}{N(y)},
\frac{bc-ad}{N(y)}
\right)
$$

を Lean 上で表している。

ここで

$$
N(y)=c^2+cd-d^2
$$

である。

重要なのは、本 `def` 自体は `y ≠ 0` を仮定しないことじゃ。Lean の `ℚ` における除算は全域的に定義されているため、`goldenNorm y = 0` の場合でも項そのものは構成できる。数学的に通常の商として利用する段階では、0215 `goldenNorm_ne_zero_of_ne_zero` が非零分母を保証する。

## 証明全体での役割

`GoldenEuclidean.lean` の目的は `GoldenInt` に norm-Euclidean division を構成することにある。そのためには、任意の `x` を非零 `y` で割った有理商を黄金基底で表し、その二座標を最近接整数へ丸める必要がある。

流れは次の通り。

1. 0215 で `y ≠ 0 → N(y) ≠ 0` を確保する。
2. 0216 で `x * conjugate(y)` を整数分子として構成する。
3. 0217・0218 でその二座標を明示する。
4. **0219 本定義** で各座標を `N(y)` で割り、`ℚ × ℚ` の rational quotient に移す。
5. 0220 `goldenQuotient` で各座標を `round` し、最近接黄金整数 quotient を得る。
6. 0221 `goldenRemainder` で `x - qy` を residual として定義する。
7. 後続で丸め誤差が `[-1/2,1/2]^2` に入ることと 0213–0214 の norm contraction を組み合わせ、remainder の Euclidean size が divisor より真に小さいことを示す。

したがって 0219 は、整数座標の代数から最近接格子丸めの幾何へ移る **型境界** である。

## 直接依存する定義・補題

直接依存する定義は次の通り。

- `GoldenInt`
- 0209 `GoldenRat`
- 0216 `goldenQuotientNumerator`
- 0164 `goldenNorm`
- 整数から有理数への coercion
- `ℚ` 上の除算

本宣言は `def` なので proof script はなく、0215 `goldenNorm_ne_zero_of_ne_zero` を直接は使用しない。

しかし数学的に `x/y` として解釈する際には

$$
y\neq0\Longrightarrow N(y)\neq0
$$

が必要であり、その保証を0215が与える。

概念的な依存は

$$
x\overline y
\xrightarrow{\text{0217,0218}}
(A,B)\in\mathbb Z^2
\xrightarrow{/N(y)}
\left(\frac{A}{N(y)},\frac{B}{N(y)}\right)\in\mathbb Q^2
$$

である。

## 構築の流れ

定義は二座標を直接組にするだけである。

```lean
def goldenQuotientCoords (x y : GoldenInt) : GoldenRat :=
  (((goldenQuotientNumerator x y).fst : ℚ) / goldenNorm y,
    ((goldenQuotientNumerator x y).snd : ℚ) / goldenNorm y)
```

第一座標では、

```lean
(goldenQuotientNumerator x y).fst : ℤ
```

を `ℚ` へ cast し、`goldenNorm y : ℤ` も除算の文脈で `ℚ` へ coercion して割る。

第二座標も全く同様である。

この段階では quotient を整数へ丸めず、正確な有理座標を保持する。最近接整数への離散化は次の `goldenQuotient` に分離されている。

## Lean 固有の処理

### 1. `GoldenRat` は `abbrev`

0209 で

```lean
abbrev GoldenRat := ℚ × ℚ
```

と定義されているため、本定義の pair literal は通常の `Prod ℚ ℚ` と definitionally 同一である。後続では `.1`, `.2` をそのまま利用できる。

### 2. 明示的な numerator cast

```lean
((goldenQuotientNumerator x y).fst : ℚ)
```

では `ℤ → ℚ` の coercion を明示している。分母 `goldenNorm y` は `/` の期待型から `ℚ` へ coercion される。

### 3. zero division が型レベルでは禁止されない

`ℚ` の `/` は total operation なので、Lean は `goldenNorm y ≠ 0` をこの定義時点で要求しない。この設計により `goldenQuotientCoords x 0` も well-typed であり、後続の `goldenQuotient_zero` を全域関数として述べられる。

一方、`field_simp` 等で通常の有理化恒等式を使うときには denominator nonzero proof が必要になり、そこで0215が効く。

## 冗長・重複箇所

0217・0218 が numerator の座標公式を公開した直後に、本定義は再び `.fst` / `.snd` を直接参照している。したがって数学的には、0217・0218 の明示公式を定義本体へ inline する設計も可能である。

しかし現行設計では

- numerator の整数代数
- norm による有理化
- 最近接整数への丸め

を三段階に分離しており、監査性が高い。

また第一・第二座標は同じ分母を共有するので、`GoldenRat` を pair ではなく「common denominator を持つ rationalized golden coordinate」の専用 structure として表す案もある。ただし現段階では `ℚ × ℚ` の方が軽量で、Mathlib の既存 rational arithmetic を直接使える。

## 最適化候補

1. **標準乗法・共役 API へ寄せる**
   - `goldenQuotientNumerator` を raw `goldenMul` ではなく標準 `*` ベースへ寄せ、下流の raw API exposure を減らす。

2. **非零分母版を別 theorem / function として提供する**
   - `y ≠ 0` を引数に取り、有理化恒等式を利用しやすい wrapper を用意する。
   - ただし Euclidean function 自体を total に保つ現行設計には利点がある。

3. **0217・0218 の explicit formula を使った alternate definition を比較する**
   - numerator object を経由する現行版と、座標式を直接記述する版の proof burden を比較できる。

4. **一般 quadratic order へ抽象化する**
   - 共役・ノルム・有理化商は二次環一般に現れるため、`θ²=pθ+q` の一般 quotient-coordinate API を作り golden case を特殊化する余地がある。

5. **`GoldenRat` を専用 structure にする**
   - field 名に `oneCoord`, `phiCoord` のような意味を持たせられるが、軽量さとの trade-off がある。

局所的には本定義は極めて短く、最適化の主眼は API 境界の設計にある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本定義単独で直接必要なのは主に、

- `ℚ`
- `Prod`
- `ℤ → ℚ` coercion
- field division
- project-local な `GoldenInt`, `GoldenRat`, `goldenQuotientNumerator`, `goldenNorm`

である。

`tactic` は本 `def` 自身では使用しない。

ただし `GoldenEuclidean.lean` 全体では `round`, `abs_sub_round`, `nlinarith`, `field_simp`, `ring`, `Int.natAbs`, Euclidean-domain infrastructure まで利用するため、module 単位の最小 import は本宣言単独よりかなり広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行の numerator-object 経由 definition
- B: 0217・0218 の explicit coordinate formula を直接 inline
- C: `GoldenRat` を専用 structure に変更
- D: `y ≠ 0` を引数に持つ partial-style quotient API
- E: 一般 quadratic-order quotient coordinates の特殊化

比較軸は、

- definitional transparency
- downstream `field_simp` の容易さ
- zero-divisor / zero-denominator handling
- proof term の長さ
- API の監査性
- 一般化可能性

である。

特に A と D の比較は、「Euclidean division の演算を total function として定義する設計」と「数学的前提 `y ≠ 0` を型・引数に露出する設計」の違いを測るよい challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

正本 source では 0217・0218 の直後に本定義が置かれ、その直後に

```lean
def goldenQuotient (x y : GoldenInt) : GoldenInt :=
  ⟨round (goldenQuotientCoords x y).1,
    round (goldenQuotientCoords x y).2⟩
```

が続く。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本定義に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0220 `goldenQuotient`** である。

```lean
/-- The nearest integral golden quotient. -/
def goldenQuotient (x y : GoldenInt) : GoldenInt :=
  ⟨round (goldenQuotientCoords x y).1,
    round (goldenQuotientCoords x y).2⟩
```

0219 が正確な rational quotient coordinates を構成したので、0220 ではその二座標を独立に最近接整数へ丸め、実際の `GoldenInt` quotient を得る。ここで連続的な有理商から離散的な黄金整数格子へ戻り、その次の `goldenRemainder` と norm contraction へ進む。
