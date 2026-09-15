# 0405 `counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic`

## 宣言種別

`theorem`

## Lean の型

```lean
/-- Unit classification and zero-sector arithmetic suffice for all primitive packets. -/
theorem counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter :=
  counterexamplePackRefuter_of_unitFifthPowerExclusion
    (signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector hClasses
      (signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic))
```

## 数学的主張・宣言の意味

この theorem は、golden-order 側で必要となる二つの入力

1. unit の第五冪剰余類分類 `GoldenUnitClassesModFifth`
2. zero sector の算術的排除 `GoldenZeroSectorArithmeticExclusion`

があれば、すべての primitive FLT5 counterexample packet を否定できることを示す。

型としては

$$
\mathrm{GoldenUnitClassesModFifth}
\to
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{CounterexamplePackRefuter}
$$

である。

0400 で `GoldenZeroSectorArithmeticExclusion` は raw arithmetic receiver として定義され、0401 で

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\mathrm{SignedGoldenZeroSectorExclusion}
$$

へ変換された。

一方、先行する unit-class closure theorem は

$$
\mathrm{GoldenUnitClassesModFifth}
+
\mathrm{SignedGoldenZeroSectorExclusion}
\Longrightarrow
\mathrm{SignedGoldenUnitFifthPowerExclusion}
$$

を与える。

さらに 0404 が

$$
\mathrm{SignedGoldenUnitFifthPowerExclusion}
\Longrightarrow
\mathrm{CounterexamplePackRefuter}
$$

を与えるため、0405 はこれらをそのまま合成した theorem である。

全体の論理回路は

$$
\begin{aligned}
&\mathrm{GoldenUnitClassesModFifth}
\quad+
\mathrm{GoldenZeroSectorArithmeticExclusion}\\
&\qquad\Downarrow\\
&\mathrm{GoldenUnitClassesModFifth}
\quad+
\mathrm{SignedGoldenZeroSectorExclusion}\\
&\qquad\Downarrow\\
&\mathrm{SignedGoldenUnitFifthPowerExclusion}\\
&\qquad\Downarrow\\
&\mathrm{CounterexamplePackRefuter}.
\end{aligned}
$$

つまり、zero sector の無限降下で得た算術的矛盾と、非零 unit classes の有限分類を一つに束ね、primitive FLT5 closure まで到達させる接着定理である。

## 証明全体での役割

0405 は `SignedGoldenClosure` 層の重要な composition point である。

ここまでの証明では、責務が意図的に分離されている。

- unit classes の分類は `GoldenUnitClassesModFifth`
- zero sector の困難な無限降下は `GoldenZeroSectorArithmeticExclusion`
- raw arithmetic から signed zero-sector receiver への変換は 0401
- unit classes と zero sector を統合した unit-times-fifth-power 排除は `signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector`
- primitive packet 全体への routing closure は 0404

0405 はこれらを一つの public theorem にまとめる。

そのため、この theorem 自身は新しい数論的事実を証明しない。新しい congruence、valuation、golden integer の計算、descent measure の評価も行わない。役割は既存の receiver theorem を正しい順序で合成することである。

この設計により、下流では unit classification と zero-sector arithmetic だけを入力すればよく、その内部で `SignedGoldenZeroSectorExclusion` や `SignedGoldenUnitFifthPowerExclusion` を手作業で組み立てる必要がなくなる。

## 直接依存する定義・補題

### `GoldenUnitClassesModFifth`

第1引数 `hClasses` の型。

これは golden unit を第五冪を法とする有限個の unit class に分類するための receiver contract である。

0405 自身は分類の内部には立ち入らず、既証明 theorem

```lean
signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector
```

へそのまま渡す。

### `GoldenZeroSectorArithmeticExclusion`

第2引数 `hArithmetic` の型。0400 で導入された `abbrev` である。

これは zero sector を排除するために必要な raw integer arithmetic 条件を一つの `Prop` にまとめたものだった。

0405 では直接 primitive packet に使わず、まず 0401 を通して signed zero-sector receiver へ変換する。

### `signedGoldenZeroSectorExclusion_of_arithmetic`

0401 の theorem。

```lean
signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic
```

により

```lean
SignedGoldenZeroSectorExclusion
```

が得られる。

数学的には

$$
\mathrm{raw\ zero\ arithmetic}
\Longrightarrow
\mathrm{signed\ zero\ sector\ exclusion}
$$

という adapter である。

### `signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector`

unit class classification と zero-sector exclusion を統合する先行 theorem。

型は概念的に

```lean
GoldenUnitClassesModFifth →
SignedGoldenZeroSectorExclusion →
SignedGoldenUnitFifthPowerExclusion
```

である。

0405 の内側の application

```lean
signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector hClasses
  (signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic)
```

が `SignedGoldenUnitFifthPowerExclusion` を生成する。

ここで非零 unit classes は有限分類側で排除され、zero class は zero-sector theorem 側で排除される。

### `counterexamplePackRefuter_of_unitFifthPowerExclusion`

0404 の theorem。

```lean
SignedGoldenUnitFifthPowerExclusion → CounterexamplePackRefuter
```

という closure adapter であり、0402 の orientation theorem と `CounterexamplePack.swap` を内部で利用して primitive packet の左右どちらの gap も一つの Branch B refuter に送る。

0405 はこの theorem を最外層として使用する。

### `CounterexamplePackRefuter`

0403 で定義された `abbrev`。

```lean
abbrev CounterexamplePackRefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

従って 0405 の結論は、任意の primitive FLT5 packet が矛盾を導くという命題である。

## 証明・構築の流れ

proof term は tactic block を使わず、三段の関数合成として書かれている。

### 1. zero-sector arithmetic を signed receiver へ変換する

```lean
signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic
```

これで

```lean
SignedGoldenZeroSectorExclusion
```

を得る。

### 2. unit classes と zero sector を統合する

```lean
signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector hClasses
  (signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic)
```

これにより

```lean
SignedGoldenUnitFifthPowerExclusion
```

が得られる。

この段階で、unit-times-fifth-power 表現の全 unit class が排除済みとなる。

### 3. primitive packet refuter へ閉じる

```lean
counterexamplePackRefuter_of_unitFifthPowerExclusion
  (...)
```

0404 に前段の exclusion を渡すことで

```lean
CounterexamplePackRefuter
```

を得る。

従って証明は本質的に

$$
A\to B,
\qquad
(C,B)\to D,
\qquad
D\to E
$$

という既存写像を

$$
(C,A)\to E
$$

へ合成している。

## Lean 固有の処理

### tactic-free term proof

宣言末尾は

```lean
:=
  counterexamplePackRefuter_of_unitFifthPowerExclusion
    (...)
```

となっており、`by` block を使わない。

Lean の Curry 化された関数適用だけで型が完全に決まるため、`intro`、`exact`、`simpa` などは不要である。

### nested function application

Lean は内側から

```lean
signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic
```

を elaboration し、その結果型を使って

```lean
signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector
```

の第2引数を決定する。

最後に生成された `SignedGoldenUnitFifthPowerExclusion` が 0404 の入力型に一致する。

型が receiver boundary ごとに明確に分離されているため、明示的な型注釈は不要である。

### `abbrev` conclusion の透過性

最終結論 `CounterexamplePackRefuter` は `abbrev` だが、この proof ではその展開を明示的に行わない。

0404 の返り値がすでに同じ名前付き命題型なので、そのまま型一致する。

### implicit arguments をほぼ露出しない設計

primitive packet の `{x y z}`、golden packet の各 index、unit class index などは前段 theorem の内部へ隠れている。

0405 では公開 receiver 型だけを組み合わせるため、dependent indices の明示的な指定や rewrite は一切不要である。

これは closure API の分離がうまく機能している例である。

## 冗長・重複箇所

0405 の proof term 自体に冗長性はほぼない。

一見すると

```lean
signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic
```

を一度 `have` で名前付けし、さらに unit exclusion を `have` で名前付けする書き方も可能である。

例えば

```lean
by
  have hZero := signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic
  have hExclude :=
    signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector hClasses hZero
  exact counterexamplePackRefuter_of_unitFifthPowerExclusion hExclude
```

と書ける。

しかし現在の nested term は三段しかなく、型名も明瞭なので、短さと可読性のバランスは良い。

closure 層には 0401、0404、0405 のような薄い adapter theorem が続くが、これは単なる重複ではない。それぞれが

- raw arithmetic boundary
- unit-times-fifth-power boundary
- primitive packet boundary

を明示しており、将来別の zero-sector proof や別の unit classification を差し替えられる。

## 最適化候補

### 現状維持が最有力

0405 は既存 API の型をそのまま合成しており、証明項としてほぼ最小である。

ここを一行化しても本質的な短縮はなく、逆に theorem 名の関係が読みにくくなる可能性がある。

### composition helper の一般化

同様の receiver chain が他 exponent でも大量に現れる場合、抽象的な composition combinator を用意することはできる。

しかし Lean の通常の関数適用そのものが既に composition の役割を果たしているため、0405 のためだけに generic helper を導入する価値は低い。

### 中間 theorem の整理

将来 API を簡略化するなら、

```lean
GoldenUnitClassesModFifth →
GoldenZeroSectorArithmeticExclusion →
SignedGoldenUnitFifthPowerExclusion
```

を直接返す adapter を別名で置く案はある。

ただし現在の 0401 を明示的に経由する構造は、「raw arithmetic」と「signed zero-sector theorem」の境界を監査しやすくする利点がある。

従って最適化はコード短縮よりも、この receiver architecture を保持する方が重要である。

## 必要な Mathlib import

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

0405 の proof 本体は tactic を使用せず、既存 DkMath theorem の関数適用だけで構成される。そのため、0405 自身が直接要求する Mathlib 機能は非常に少ない。

実際の依存の大部分は次の宣言を定義する先行 DkMath modules に由来する。

- `GoldenUnitClassesModFifth`
- `GoldenZeroSectorArithmeticExclusion`
- `SignedGoldenZeroSectorExclusion`
- `SignedGoldenUnitFifthPowerExclusion`
- `CounterexamplePackRefuter`
- それらを結ぶ先行 closure theorem

standalone manifest ではこの宣言は `DkMath/FLT/Five/SignedGoldenClosure.lean` に属する。

### import 最適化候補

この theorem 単独を理由に `import Mathlib` 全体を要求する必要はない。

モジュール版では、上記 receiver 型と adapter theorem を公開する DkMath modules を import すれば十分である可能性が高い。

ただし今回 Lean build は行っていないため、正確な最小 Mathlib import 集合は未確認である。`Mathlib` を細分化するなら、依存モジュール側を含めて `lake build` で検証する必要がある。

## Comparator challenge 化の可否

単独の proof synthesis challenge としては **容易** である。

理由は、必要な theorem をすべて context に与えれば、解はほぼ型に強制されるからである。

challenge 化するなら、次の API だけを公開する。

```lean
hClasses : GoldenUnitClassesModFifth
hArithmetic : GoldenZeroSectorArithmeticExclusion

signedGoldenZeroSectorExclusion_of_arithmetic :
  GoldenZeroSectorArithmeticExclusion → SignedGoldenZeroSectorExclusion

signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector :
  GoldenUnitClassesModFifth →
  SignedGoldenZeroSectorExclusion →
  SignedGoldenUnitFifthPowerExclusion

counterexamplePackRefuter_of_unitFifthPowerExclusion :
  SignedGoldenUnitFifthPowerExclusion → CounterexamplePackRefuter
```

そして target を

```lean
CounterexamplePackRefuter
```

とすればよい。

これは数論 challenge というより、API composition と theorem selection の challenge になる。

より意味のある Comparator challenge にするなら、0401 や unit-class integration theorem を隠し、raw packet lemmas から `SignedGoldenUnitFifthPowerExclusion` を再構築させる方が難度は高い。

## 次に読むべき宣言

正本で直後に続くのは

```lean
/-- Arbitrary positive solutions can be reduced to a primitive counterexample packet. -/
theorem exists_counterexamplePack_of_positive_fermat5
    {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hEq : Fermat5Equation x y z) :
    ∃ x₀ y₀ z₀ : ℕ, CounterexamplePack x₀ y₀ z₀ := by
  ...
```

である。

0405 までで

$$
\mathrm{primitive\ CounterexamplePack}\to\bot
$$

を閉じた。

次は任意の正の FLT5 解

$$
x^5+y^5=z^5,
\qquad x,y,z>0
$$

から primitive packet を取り出す reduction へ進む。

従って証明の層はここで

$$
\text{primitive closure}
\longrightarrow
\text{general positive-solution normalization}
$$

へ移る。0405 は golden-order 側の closure chain と、最終的な正整数 FLT5 theorem を結ぶ直前の節目である。
