# 0423 `counterexamplePackRefuter_of_zeroArithmetic`

## 宣言種別

`theorem`

## Lean の型

```lean
/-- The zero-sector arithmetic proposition refutes every primitive packet. -/
theorem counterexamplePackRefuter_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter :=
  counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

## 数学的主張・宣言の意味

0423 は、zero sector の算術的排除命題が成立すれば、任意の primitive FLT5 counterexample packet を反駁できることを述べる theorem である。

結論の `CounterexamplePackRefuter` は `abbrev : Prop` として

```lean
abbrev CounterexamplePackRefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

と定義されている。

したがって数学的には

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\forall x,y,z\in\mathbb N,
\ \mathrm{CounterexamplePack}(x,y,z)\to\bot
$$

という主張である。

`CounterexamplePack x y z` は正の自然数による指数 5 の解候補を primitive 条件つきで束ねた packet であり、0423 はその primitive 層を完全に閉じる conditional receiver である。

重要なのは、0423 が unit classification を仮定として要求しない点である。より一般の receiver

```lean
counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
```

は

```lean
GoldenUnitClassesModFifth →
GoldenZeroSectorArithmeticExclusion →
CounterexamplePackRefuter
```

という二仮定の形だが、0423 ではすでに証明済みの

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

を投入することで、残る仮定を zero-sector arithmetic のみに縮約している。

## 証明全体での役割

0423 は Main 層に置かれた primitive-counterexample 用の公開 receiver である。

FLT5 の closure は大きく

$$
\text{unit classification}
\;\Longrightarrow\;
\text{finite unit sectors}
\;\Longrightarrow\;
\text{nonzero sectors の排除}
\;\Longrightarrow\;
\text{zero sector の排除}
\;\Longrightarrow\;
\text{primitive packet の反駁}
\;\Longrightarrow\;
\text{任意の正の解の反駁}
$$

と流れる。

0423 はこのうち

$$
\text{zero-sector arithmetic exclusion}
\Longrightarrow
\text{primitive packet refuter}
$$

という境界を Main 層で明示する。

最終 theorem `flt5Target` は positive solution 全体を対象とするが、その直前の内部構造では `CounterexamplePackRefuter` が primitive 層の closure endpoint である。したがって 0423 は、gcd normalization より前の数論コアを独立して再利用・監査できるようにする facade theorem と解釈できる。

## 直接依存する定義・補題

### `GoldenZeroSectorArithmeticExclusion`

zero sector の最終算術 contract である。

```lean
abbrev GoldenZeroSectorArithmeticExclusion : Prop :=
  ∀ (r s : ℤ) (a b : ℕ),
    0 < a →
    0 < b →
    Nat.Coprime a b →
    ¬ 5 ∣ b →
    (goldenNorm ⟨r, s⟩ = (b : ℤ) ∨
      goldenNorm ⟨r, s⟩ = -(b : ℤ)) →
    s * goldenFifthSndFactor r s =
      -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10 →
    Nat.Coprime r.natAbs s.natAbs →
    (∃ c d : ℕ,
      s.natAbs = 5 ^ 6 * c ^ 10 ∧
      (goldenFifthSndFactor r s).natAbs = d ^ 10) →
    False
```

0423 はこれを唯一の外部仮定として受け取る。

### `CounterexamplePackRefuter`

primitive packet 全体を反駁する proposition である。

```lean
abbrev CounterexamplePackRefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

0423 の conclusion はこの proposition そのものである。

### `counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic`

0423 が直接呼び出す receiver theorem である。

```lean
theorem counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter :=
  counterexamplePackRefuter_of_unitFifthPowerExclusion
    (signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector hClasses
      (signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic))
```

この theorem が、unit-classification と zero-sector arithmetic を、primitive packet refuter へ接続する実際の composition を担う。

### `goldenUnitClassesModFifth`

unit classification の無条件 provider である。

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

0423 はこれを第一引数へ投入し、unit-classification 仮定を discharge する。

## 証明または構築の流れ

0423 自身の proof は一つの関数適用である。

```lean
counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

流れは次の通りである。

### 1. 二仮定 receiver を取得する

既存 theorem は

```lean
GoldenUnitClassesModFifth →
GoldenZeroSectorArithmeticExclusion →
CounterexamplePackRefuter
```

という型を持つ。

### 2. unit classification を無条件 theorem で埋める

`goldenUnitClassesModFifth` はすでに proof object として存在するため、第一引数にそのまま渡せる。

これにより receiver は

```lean
GoldenZeroSectorArithmeticExclusion → CounterexamplePackRefuter
```

へ部分適用される。

### 3. zero-sector arithmetic 仮定を渡す

残った引数 `hArithmetic` を渡すと conclusion は

```lean
CounterexamplePackRefuter
```

となる。

0423 自身には case split、rewrite、ring、omega、gcd 計算などは存在しない。そうした数論処理はすべて下位 theorem へ押し込まれている。

## Lean 固有の処理

### Curry–Howard 対応による theorem composition

`GoldenUnitClassesModFifth`、`GoldenZeroSectorArithmeticExclusion`、`CounterexamplePackRefuter` はいずれも `Prop` であり、それぞれの theorem は proof object である。

0423 は

```lean
A → B → C
```

型の theorem に

```lean
a : A
b : B
```

を適用して `C` を得る、純粋な関数適用になっている。

### `abbrev` の透明性

`CounterexamplePackRefuter` は `abbrev` なので、必要なら Lean は

```lean
∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

へ定義展開できる。

しかし 0423 では receiver の返り値型がそのまま一致するため、`unfold` や `simpa` は不要である。

### 部分適用

式

```lean
counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth
```

の段階で、Lean は残りの引数として `GoldenZeroSectorArithmeticExclusion` を待つ関数を得る。0423 はそこへ `hArithmetic` を適用している。

## 冗長・重複箇所

0423 は数学的には新しい数論内容を追加しない。

同じ conclusion は利用箇所で直接

```lean
counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

と書けば得られるため、proof term の情報量だけを見れば facade wrapper である。

ただしこの重複には設計上の意味がある。

- primitive packet 層の public receiver を短い名前で提供できる。
- unit classification がすでに無条件化済みであることを API 上で示せる。
- zero-sector arithmetic だけを仮定として残す境界が明瞭になる。
- full positive target と primitive target を分離して監査できる。

したがって、0419 や 0422 と同様に意図的な interface duplication と評価できる。

## 最適化候補

### 1. wrapper の削除

最小コード量を優先するなら 0423 は削除可能である。呼び出し側で receiver と provider を直接合成すればよい。

ただし API の意味が弱くなるため、現行の facade 設計では残す価値がある。

### 2. proof syntax

現行の term-style proof はほぼ最短である。

```lean
by
  exact counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

としても意味は同じだが、コード量は増える。

### 3. facade naming の統一

Main 層には

```text
flt5Target_of_zeroArithmetic
counterexamplePackRefuter_of_zeroArithmetic
positiveFermat5Refuter_of_zeroArithmetic
```

という似た receiver 群が並ぶ。これは重複でもあるが、各 abstraction layer の endpoint として規則的である。

将来整理するなら、conditional/unconditional receiver の命名規則を機械的に統一すると依存関係の可視性がさらに上がる。

## 必要な Mathlib import

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

0423 本体自身は theorem application しか行わないため、特別な Mathlib tactic を直接使用しない。

直接必要なのは少なくとも次の FLT5 declarations である。

- `GoldenZeroSectorArithmeticExclusion`
- `CounterexamplePackRefuter`
- `GoldenUnitClassesModFifth`
- `goldenUnitClassesModFifth`
- `counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic`

その推移依存として `CounterexamplePack`、signed golden sector machinery、zero-sector exclusion、unit classification などが必要になる。

### import 最適化候補

0423 単体のコードから見れば `Mathlib` 全体を直接 import する必要性は低く、分割 source では `SignedGoldenClosure` と unit classification provider を含む module 群の import closure で足りる可能性が高い。

ただし今回は Lean build を実行していないため、最小 Mathlib module 集合および最小 FLT5 import closure は実測していない。具体的な最小 import 名は未確認事項として断定しない。

## Comparator challenge 化の可否

 **適している。難度は低いが、provider/receiver 接続と部分適用を試す challenge として明瞭である。**

例えば環境に

```lean
counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic :
  GoldenUnitClassesModFifth →
  GoldenZeroSectorArithmeticExclusion →
  CounterexamplePackRefuter

goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

を与え、

```lean
theorem challenge
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter := by
  ?_
```

を解かせれば、solver は

```lean
exact counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

を発見すればよい。

より難しくするなら `goldenUnitClassesModFifth` を隠し、`GoldenUnitClassesModFifth` を下位 theorem から再構成させる、または `counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic` 自体を隠して

```text
signedGoldenZeroSectorExclusion_of_arithmetic
→ signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector
→ counterexamplePackRefuter_of_unitFifthPowerExclusion
```

の三段 composition を復元させると、dependency selection challenge として価値が上がる。

## 次に読むべき宣言

次は 0424 `positiveFermat5Refuter_of_zeroArithmetic` である。

```lean
/-- The zero-sector arithmetic proposition refutes every positive solution. -/
theorem positiveFermat5Refuter_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    PositiveFermat5Refuter :=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

0423 が primitive packet 層を閉じるのに対し、0424 は gcd normalization を含む full positive-solution 層の receiver を公開する。

したがって依存構造としては

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\mathrm{CounterexamplePackRefuter}
\Longrightarrow
\mathrm{PositiveFermat5Refuter}
$$

という abstraction-level の上昇を追うことになる。