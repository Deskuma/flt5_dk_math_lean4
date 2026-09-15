# 0409 `positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic`

## 宣言種別

`theorem`

## Lean の型

```lean
theorem positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    PositiveFermat5Refuter :=
  positiveFermat5Refuter_of_counterexamplePackRefuter
    (counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic)
```

この theorem は、黄金整数側の unit class 分類

```lean
hClasses : GoldenUnitClassesModFifth
```

と zero sector の算術排除

```lean
hArithmetic : GoldenZeroSectorArithmeticExclusion
```

を受け取り、正の自然数における FLT5 の反例をすべて排除する

```lean
PositiveFermat5Refuter
```

を返す。

0407 `PositiveFermat5Refuter` を展開すれば、結論は

```lean
∀ x y z : ℕ,
  0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

である。

## 数学的主張

数学的には、次の二つの局所的な入力が揃えば、正整数上の指数 5 の Fermat 方程式に解が存在しないことを示せる、という closure theorem である。

1. 黄金整数の fifth-power 分解に現れる unit class が必要な有限個の class に分類されること。
2. そのうち残る zero sector が算術的に不可能であること。

これらから primitive counterexample がすべて排除され、さらに primitive reduction を通じて任意の正整数解が排除される。

論理経路は

$$
\mathrm{GoldenUnitClassesModFifth}
+
\mathrm{GoldenZeroSectorArithmeticExclusion}
\longrightarrow
\mathrm{CounterexamplePackRefuter}
\longrightarrow
\mathrm{PositiveFermat5Refuter}
$$

である。

最終的には任意の $x,y,z\in\mathbb N$ について

$$
0<x,\qquad 0<y,\qquad 0<z
$$

ならば

$$
x^5+y^5\ne z^5
$$

を得る。

ただし、この theorem 自身が unit class の分類や zero sector の無限降下を再証明するわけではない。それらは既存 theorem の背後に封じ込められており、0409 は証明済みの二つの層を full positive target へ接続する。

## 証明全体での役割

0409 は `SignedGoldenClosure` の終端に位置する高水準 receiver theorem である。

直前までの流れは大きく次の三段に分かれている。

1. 黄金整数・unit fifth-power 側で、unit class と zero sector の排除から primitive packet を否定できるようにする。
2. 0405 `counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic` で、その結果を `CounterexamplePackRefuter` にまとめる。
3. 0408 `positiveFermat5Refuter_of_counterexamplePackRefuter` で、primitive refuter を任意の正整数解の refuter へ持ち上げる。

0409 は 2 と 3 を一つの theorem application として合成する。

したがって証明全体では

$$
\text{golden arithmetic boundary}
\Longrightarrow
\text{primitive FLT5 closure}
\Longrightarrow
\text{positive FLT5 closure}
$$

という dependency boundary を公開する役割を持つ。

ここで重要なのは、0409 の結論がすでに `PositiveFermat5Refuter` であるため、後続の `Main.lean` は黄金整数内部の詳細を知らずに、この receiver を FLT5 の公開 target に接続できる点である。

## 直接依存する定義・補題

### `GoldenUnitClassesModFifth`

`hClasses` の型。

黄金整数の unit を fifth-power class modulo の有限分類へ落とすための receiver proposition である。

0409 はその内部構造を直接展開せず、0405 にそのまま渡す。

### `GoldenZeroSectorArithmeticExclusion`

`hArithmetic` の型。

zero sector に到達した場合の算術的条件が矛盾することを表す公開 receiver proposition である。

0409 自身はその条件を分解せず、0405 に渡す。

### `counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic`

0405 の theorem。

```lean
theorem counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter
```

二つの黄金整数側入力から、すべての primitive `CounterexamplePack` を否定する refuter を構築する。

0409 の内側の application

```lean
counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

がこの段階に対応する。

### `positiveFermat5Refuter_of_counterexamplePackRefuter`

0408 の theorem。

```lean
theorem positiveFermat5Refuter_of_counterexamplePackRefuter
    (hPrimitive : CounterexamplePackRefuter) :
    PositiveFermat5Refuter
```

primitive packet の refuter を、任意の正整数 FLT5 解の refuter へ持ち上げる。

0409 の外側の application がこの段階である。

### `PositiveFermat5Refuter`

0407 の `abbrev`。

```lean
abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

0409 の結論型である。

## 証明の流れ

0409 の proof term は一つの入れ子になった関数適用だけで完成している。

### 1. unit classification と zero-sector arithmetic から primitive refuter を作る

```lean
counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

この式の型は

```lean
CounterexamplePackRefuter
```

である。

ここまでで、任意の primitive `CounterexamplePack` を `False` に送れる。

### 2. primitive refuter を positive refuter へ持ち上げる

得られた値を 0408 に渡す。

```lean
positiveFermat5Refuter_of_counterexamplePackRefuter
  (counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    hClasses hArithmetic)
```

0408 は正整数解が存在すると仮定したとき、その解を 0406 の gcd normalization により primitive packet へ変換し、primitive refuter と矛盾させる。

そのため、この式全体の型は

```lean
PositiveFermat5Refuter
```

となり、0409 の目標と一致する。

## Lean 固有の処理

### tactic を使わない term-style proof

0409 は

```lean
:=
  positiveFermat5Refuter_of_counterexamplePackRefuter
    (...)
```

という pure term proof である。

`by`、`intro`、`exact`、`rw` などは一切必要ない。Lean の型検査器は、内側の theorem application の結果型が外側の theorem の入力型と一致し、最終結果型が目標と一致することだけを検証する。

### 型による dependency routing

内側の結果は

```lean
CounterexamplePackRefuter
```

外側が要求する引数も

```lean
CounterexamplePackRefuter
```

であるため、証明は数学的にも Lean 上も通常の関数合成として読める。

概念的には

```lean
A → B → C
C → D
----------------
A → B → D
```

という型の接続である。

### `abbrev` の透過性

最終型 `PositiveFermat5Refuter` と中間型 `CounterexamplePackRefuter` は `abbrev` で定義されている。

しかし 0409 ではそれらを `unfold` する必要はない。Lean は reducible abbreviation として必要時に展開し、型一致を確認できる。

### implicit argument の明示不要

0409 には `x y z` のような具体的自然数は現れない。

それらは `PositiveFermat5Refuter` と `CounterexamplePackRefuter` の内部 binder に封じ込められており、この theorem は proposition-level interface 同士だけを接続している。

これにより proof term は非常に短く保たれている。

## 冗長・重複箇所

0409 の本体には計算上の重複はほぼない。

形式的には、0405 と 0408 を利用せず、それぞれの内部証明を展開して一つの巨大な theorem にすることもできる。しかしそれは

- primitive closure
- positive normalization
- golden arithmetic boundary

の分離を壊すため、明確な悪化になる。

一方で 0409 は「既存 theorem 二つの単純合成」に見えるため、コード行数だけを基準にすれば wrapper の重複に見える。

それでも、この名前付き theorem は

```lean
GoldenUnitClassesModFifth
GoldenZeroSectorArithmeticExclusion
```

という二つの外部境界だけを提示し、`PositiveFermat5Refuter` を直接返す API になっている。後続 `Main.lean` から primitive 層の詳細を隠せるので、設計上の価値がある。

## 最適化候補

### 1. 現行 term proof を維持する

実装はすでにほぼ最短である。

```lean
positiveFermat5Refuter_of_counterexamplePackRefuter
  (counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic)
```

以上に本質的に短くしても可読性や依存関係は改善しない。

したがって **現行形を維持するのが最も自然** である。

### 2. 中間 `have` を置く説明用形式

教育目的なら

```lean
by
  have hPrimitive : CounterexamplePackRefuter :=
    counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
  exact positiveFermat5Refuter_of_counterexamplePackRefuter hPrimitive
```

とすれば dependency の二段階が見えやすい。

ただし production code では現在の term-style の方が簡潔であり、この変更は最適化ではなく説明性との交換である。

### 3. generic composition helper は不要

抽象的には単なる関数合成なので generic helper を導入できるが、Lean 自体の関数適用で十分である。

新しい abstraction を置くと FLT5 固有の dependency 名が隠れ、むしろ追跡しにくくなる。

## 必要な Mathlib import

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

0409 の proof body が直接使うものは、Mathlib の個別数論 theorem や tactic ではなく、先行して定義・証明された FLT5 の proposition と theorem application だけである。

直接必要なのは概念的には

- `GoldenUnitClassesModFifth`
- `GoldenZeroSectorArithmeticExclusion`
- `CounterexamplePackRefuter`
- `PositiveFermat5Refuter`
- `counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic`
- `positiveFermat5Refuter_of_counterexamplePackRefuter`

を提供する module context である。

### import 最適化候補

0409 単独の proof term は Mathlib の演算 API を直接呼ばないため、`import Mathlib` はこの theorem だけを見ると大幅に広い。

分割された source module では、上記先行宣言を公開する内部 module を import すれば十分である可能性が高い。

ただし、この作業では Lean build を行っていないため、厳密な最小 import module 集合は確認していない。従って具体的な最小 import 名を断定することは避ける。

## Comparator challenge 化の可否

**可能。ただし難度は低い。**

0409 は大型算術 challenge ではなく、型に従って既存 theorem を正しく合成できるかを測る challenge に向いている。

例えば context として

```lean
axiom counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter

axiom positiveFermat5Refuter_of_counterexamplePackRefuter
    (hPrimitive : CounterexamplePackRefuter) :
    PositiveFermat5Refuter
```

を与え、0409 の proof hole を埋めさせる。

評価対象は

- theorem の入出力型の読解
- 中間型 `CounterexamplePackRefuter` の認識
- nested application による theorem composition
- `abbrev` を展開せず interface として扱う能力

である。

依存 theorem 名をそのまま与えると challenge は非常に容易である。候補 theorem 群を多めに与えて dependency selection まで要求すれば、Comparator 用として多少意味のある課題になる。

## 次に読むべき宣言

次は `SignedGoldenZeroSectorFinal.lean` の先頭にある

```lean
theorem goldenZeroSectorFactorExclusion : GoldenZeroSectorFactorExclusion := by
  intro packet
  exact goldenZeroSectorCandidate_false packet.inversion.source
```

である。

0409 で `SignedGoldenClosure` の conditional closure interface が完成した後、source order は zero-sector receiver を無条件に閉じる段階へ移る。

`goldenZeroSectorFactorExclusion` は factor packet が保持している inversion source から `GoldenZeroSectorCandidate` を取り出し、0399 `goldenZeroSectorCandidate_false` に渡すことで、すべての certified factor branch を排除する。

したがって次は、これまで receiver として仮定していた zero-sector arithmetic exclusion を、実際の無限降下結果から供給する finalization 層を読むことになる。