# 0408 `positiveFermat5Refuter_of_counterexamplePackRefuter`

## 宣言種別

`theorem`

## Lean の型

```lean
theorem positiveFermat5Refuter_of_counterexamplePackRefuter
    (hPrimitive : CounterexamplePackRefuter) : PositiveFermat5Refuter := by
  intro x y z hx hy hz hEq
  rcases exists_counterexamplePack_of_positive_fermat5 hx hy hz hEq with
    ⟨x', y', z', p⟩
  exact hPrimitive p
```

型だけを展開すると、入力は primitive counterexample をすべて否定する証明

```lean
hPrimitive : CounterexamplePackRefuter
```

であり、出力は正の自然数上の FLT5 解をすべて否定する証明

```lean
PositiveFermat5Refuter
```

である。

0403 と 0407 の `abbrev` を展開すれば、概念的には

```lean
(∀ {x y z : ℕ}, CounterexamplePack x y z → False) →
  (∀ x y z : ℕ,
    0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z)
```

という theorem である。

## 数学的主張

この theorem の数学的内容は、**primitive な FLT5 候補をすべて排除できれば、任意の正整数 FLT5 解も排除できる**、という primitive reduction の closure である。

仮に正整数 $x,y,z$ が

$$
x^5+y^5=z^5
$$

を満たすとする。

0406 `exists_counterexamplePack_of_positive_fermat5` により、そこからある正整数 $x',y',z'$ が存在して

$$
\gcd(x',y')=1,
\qquad
{x'}^5+{y'}^5={z'}^5
$$

を満たす primitive packet

$$
\mathrm{CounterexamplePack}(x',y',z')
$$

を得られる。

しかし `hPrimitive : CounterexamplePackRefuter` は任意のそのような packet から `False` を返す。従って元の正整数解の存在仮定も矛盾する。

論理経路は

$$
\text{positive FLT5 solution}
\longrightarrow
\text{primitive normalization}
\longrightarrow
\mathrm{CounterexamplePack}
\longrightarrow
\bot
$$

である。

## 証明全体での役割

0406 までで、証明は二つの層に分離されていた。

1. `CounterexamplePackRefuter` 側では、primitive packet に対する黄金整数・unit class・zero sector・無限降下などの局所的な数論を閉じる。
2. `exists_counterexamplePack_of_positive_fermat5` 側では、任意の正整数解を gcd で正規化し primitive packet に落とす。

0408 はこの二層を接続する closure theorem である。

特に重要なのは、この theorem 自身が黄金整数、五進評価、unit classification、descent の詳細を一切知らない点である。primitive 層の内部証明は

```lean
CounterexamplePackRefuter
```

という interface の背後に完全に隠れている。

したがって 0408 は、証明全体のアーキテクチャ上

$$
\text{primitive core}
\Longrightarrow
\text{full positive FLT5 target}
$$

を実現する **normalization-to-refutation bridge** である。

## 直接依存する定義・補題

### `CounterexamplePackRefuter`

0403 の `abbrev`。

```lean
abbrev CounterexamplePackRefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

0408 の仮定 `hPrimitive` の型であり、最後の

```lean
exact hPrimitive p
```

で直接使用する。

### `PositiveFermat5Refuter`

0407 の `abbrev`。

```lean
abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

0408 の結論型である。

### `exists_counterexamplePack_of_positive_fermat5`

0406 の theorem。

```lean
theorem exists_counterexamplePack_of_positive_fermat5
    {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hEq : Fermat5Equation x y z) :
    ∃ x' y' z' : ℕ, CounterexamplePack x' y' z'
```

正の FLT5 解を primitive packet へ変換する normalization theorem であり、0408 の実質的な唯一の数学的変換である。

### `CounterexamplePack`

0408 自身は field を参照しないが、0406 が返し `hPrimitive` が消費する中間データ型である。

そのため 0408 は `CounterexamplePack` の内部構造にも依存せず、型を介した接続だけを行う。

## 証明の流れ

### 1. `PositiveFermat5Refuter` の引数を導入する

```lean
intro x y z hx hy hz hEq
```

`PositiveFermat5Refuter` は `abbrev` なので、Lean は必要に応じて

```lean
∀ x y z : ℕ,
  0 < x → 0 < y → 0 < z →
  Fermat5Equation x y z → False
```

へ透過的に展開する。

ここで

- `x y z : ℕ`
- `hx : 0 < x`
- `hy : 0 < y`
- `hz : 0 < z`
- `hEq : Fermat5Equation x y z`

を得る。

### 2. 正整数解を primitive packet へ正規化する

```lean
rcases exists_counterexamplePack_of_positive_fermat5 hx hy hz hEq with
  ⟨x', y', z', p⟩
```

0406 により

```lean
∃ x' y' z' : ℕ, CounterexamplePack x' y' z'
```

が得られるので、existential witness を取り出す。

結果として

```lean
x' y' z' : ℕ
p : CounterexamplePack x' y' z'
```

を得る。

### 3. primitive refuter に packet を渡す

```lean
exact hPrimitive p
```

`hPrimitive` は

```lean
∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

なので、`p` の dependent indices `x' y' z'` は Lean が推論し、結果として `False` が得られる。

これで最初に仮定した `hEq` が否定される。

## Lean 固有の処理

### `abbrev` の自動展開

結論は名前付き proposition

```lean
PositiveFermat5Refuter
```

だが、証明冒頭で

```lean
unfold PositiveFermat5Refuter
```

を書く必要はない。

`abbrev` が reducible なので `intro` が右辺の関数型を認識する。

同様に `hPrimitive` も `CounterexamplePackRefuter` の `abbrev` 展開を通じて関数として適用できる。

### `¬ P` の展開

Lean では

```lean
¬ P
```

は

```lean
P → False
```

なので、最後の `hEq` まで `intro` で導入できる。

### `rcases` による依存 existential elimination

0406 の結論は三つの witness と packet を持つ。

```lean
∃ x' y' z' : ℕ, CounterexamplePack x' y' z'
```

`rcases ... with ⟨x', y', z', p⟩` はこれを一度に分解する。

`p` の型が witness 三つに依存しているため、これは単なる四要素 tuple の分解ではなく、依存 existential の elimination である。

### implicit indices の推論

`CounterexamplePackRefuter` の binder は

```lean
∀ {x y z : ℕ}, ...
```

と implicit である。

したがって

```lean
hPrimitive p
```

だけで、Lean は `p : CounterexamplePack x' y' z'` から `x' y' z'` を推論する。

## 冗長・重複箇所

証明はすでに非常に短く、数論的な重複はない。

ただし

```lean
⟨x', y', z', p⟩
```

のうち `x'`, `y'`, `z'` は後続のソースコードでは名前として直接使われない。

従って Lean 上は例えば

```lean
rcases exists_counterexamplePack_of_positive_fermat5 hx hy hz hEq with
  ⟨_, _, _, p⟩
exact hPrimitive p
```

のように witness 名を捨てる書き方も可能である。

しかし現状の名前付き witness は「正整数解から新しい primitive triple を得た」ことを読み手に明示するため、説明性は高い。

また 0408 は後続の

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
```

から単に composition component として利用される。薄い bridge theorem が複数並ぶこと自体は、証明の dependency boundary を名前付きで公開する設計上の意図があるため、単純なコード重複とは見なしにくい。

## 最適化候補

### 1. witness 名を省略する

最小コードを優先するなら

```lean
theorem positiveFermat5Refuter_of_counterexamplePackRefuter
    (hPrimitive : CounterexamplePackRefuter) : PositiveFermat5Refuter := by
  intro x y z hx hy hz hEq
  obtain ⟨_, _, _, p⟩ :=
    exists_counterexamplePack_of_positive_fermat5 hx hy hz hEq
  exact hPrimitive p
```

とできる。

ただし現行版との差は表面的であり、証明性能や依存関係に本質的な改善はない。

### 2. 一般的な normalization/refuter lifting lemma

抽象的には

$$
(A\to\exists b,B(b))
\to
(\forall b,B(b)\to\bot)
\to
(A\to\bot)
$$

という一般論である。

この形の bridge が多数あるなら generic helper を導入できるが、現状の theorem は 4 行で意味も明瞭である。過度な抽象化は FLT5 固有の normalization 経路を逆に読みにくくする可能性が高い。

従って **現行実装を維持する方が自然** と考えられる。

### 3. term-style composition への短縮

existential elimination が必要なので、0405 のような単純な関数合成だけでは書けない。

`by` block を保持した現行形は、normalization の存在 witness を明示するうえで適切である。

## 必要な Mathlib import

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

0408 自身が直接使う Lean/Mathlib 機能は主に

- `intro`
- `rcases`
- existential elimination
- `exact`
- 先行宣言 `CounterexamplePackRefuter`
- 先行宣言 `PositiveFermat5Refuter`
- 先行 theorem `exists_counterexamplePack_of_positive_fermat5`

である。

この theorem 自身は ring、gcd、divisibility、valuation、golden integer などの Mathlib API を直接呼ばない。

### import 最適化候補

分割元 `SignedGoldenClosure.lean` の依存全体まで含めた最小 import は、実際に Lean build を行わなければ確定できない。

今回の作業条件では Lean build を行わないため、具体的な最小 import module 名は未確認である。

確実に言えるのは、

- standalone 正本は `import Mathlib`
- 0408 の proof body 自体は高度な Mathlib 数論 theorem に直接依存しない
- `rcases` と先行 FLT5 宣言が利用可能な module context なら proof は非常に軽い

という範囲である。

## Comparator challenge 化の可否

**可能であり、小型 challenge として適している。**

0407 の `abbrev` 単独よりは、0408 の方が challenge として意味がある。

例えば以下を context として与える。

```lean
abbrev CounterexamplePackRefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → False

abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z

axiom exists_counterexamplePack_of_positive_fermat5
    {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hEq : Fermat5Equation x y z) :
    ∃ x' y' z' : ℕ, CounterexamplePack x' y' z'
```

そして 0408 の proof hole を埋めさせる。

評価対象は

- reducible `abbrev` の扱い
- `¬ P` の関数型としての理解
- dependent existential の unpack
- implicit parameter inference
- primitive refuter の適用

となる。

数学的難度は低いが、Lean の proposition plumbing を評価する challenge としては良い。

逆に「FLT5 の数論そのもの」を比較する challenge としては弱い。数論の難所はすでに 0406 より前の primitive layer に押し込まれているからである。

## 次に読むべき宣言

次は 0409

```lean
theorem positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    PositiveFermat5Refuter :=
  positiveFermat5Refuter_of_counterexamplePackRefuter
    (counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic)
```

である。

0408 が

$$
\mathrm{CounterexamplePackRefuter}
\longrightarrow
\mathrm{PositiveFermat5Refuter}
$$

を与えたのに対し、0409 はさらに上流の

$$
\mathrm{GoldenUnitClassesModFifth}
$$

と

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
$$

から primitive refuter を組み立てて 0408 へ渡す。

従って dependency chain は

$$
\text{unit classes + zero-sector arithmetic}
\longrightarrow
\mathrm{CounterexamplePackRefuter}
\longrightarrow
\mathrm{PositiveFermat5Refuter}
$$

へ進む。