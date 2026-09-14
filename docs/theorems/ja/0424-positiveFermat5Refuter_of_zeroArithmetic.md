# 0424 `positiveFermat5Refuter_of_zeroArithmetic`

## 宣言種別

`theorem`

## Lean の型

```lean
/-- The zero-sector arithmetic proposition refutes every positive solution. -/
theorem positiveFermat5Refuter_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    PositiveFermat5Refuter :=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

## 数学的主張・宣言の意味

0424 は、zero sector の算術的排除命題

```lean
GoldenZeroSectorArithmeticExclusion
```

が与えられれば、任意の正の自然数による FLT5 解候補を反駁できることを述べる theorem である。

結論の `PositiveFermat5Refuter` は

```lean
abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

と定義されている。したがって 0424 の数学的内容は

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\forall x,y,z\in\mathbb N,
\quad x>0\to y>0\to z>0\to
x^5+y^5\ne z^5
$$

である。

ただし 0424 自身が zero-sector の Diophantine 解析や primitive reduction を新たに実行するわけではない。より一般の receiver

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
```

に、すでに証明済みの unit classification

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

を投入し、unit-classification 仮定を discharge するだけである。

その意味で 0424 は

$$
\mathrm{GoldenUnitClassesModFifth}
\to
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{PositiveFermat5Refuter}
$$

という二仮定の closure theorem を

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{PositiveFermat5Refuter}
$$

へ特殊化した公開 receiver である。

## 証明全体での役割

0424 は FLT5 proof architecture の内部 closure API を Main 層で公開する最後の facade theorem である。

証明全体は概念的には

$$
\text{positive solution}
\Longrightarrow
\text{primitive packet}
\Longrightarrow
\text{signed gap orientation}
\Longrightarrow
\text{golden unit} \times \text{fifth power}
\Longrightarrow
\text{five unit sectors}
\Longrightarrow
\text{sector exclusions}
\Longrightarrow
\text{zero-sector arithmetic}
\Longrightarrow
\bot
$$

という流れを持つ。

`SignedGoldenClosure.lean` では、まず primitive packet を反駁する

```lean
CounterexamplePackRefuter
```

を作り、それを gcd normalization によって任意の正の解へ引き上げて

```lean
PositiveFermat5Refuter
```

を得る。

0424 は、その positive-solution closure の入口で要求される仮定を zero-sector arithmetic 一つだけにまで縮約する。

Main 層にはすでに 0419

```lean
flt5Target_of_zeroArithmetic
```

が存在し、こちらも `GoldenZeroSectorArithmeticExclusion` から `FLT5Target` を与える。したがって数学的 proposition の形だけを見ると 0419 と 0424 はほぼ同じ境界を公開している。

違いは API 上の役割である。

- `FLT5Target` は最終的な公開 statement を表す。
- `PositiveFermat5Refuter` は closure 層の内部 architecture を表す。
- 0419 は public target 側の receiver。
- 0424 は internal refuter 側の receiver。

この二重化により、最終 theorem を利用する側と、proof architecture を監査・再利用する側の双方に安定した入口が用意されている。

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
    (goldenNorm ⟨r, s⟩ = (b : ℤ) ∨ goldenNorm ⟨r, s⟩ = -(b : ℤ)) →
    s * goldenFifthSndFactor r s = -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10 →
    Nat.Coprime r.natAbs s.natAbs →
    (∃ c d : ℕ,
      s.natAbs = 5 ^ 6 * c ^ 10 ∧
      (goldenFifthSndFactor r s).natAbs = d ^ 10) →
    False
```

0424 が外部から受け取る唯一の仮定である。

### `PositiveFermat5Refuter`

正の自然数による FLT5 解候補をすべて反駁する proposition である。

```lean
abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

0424 の conclusion はこの proposition そのものである。

### `positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic`

0424 が直接呼び出す一般 receiver である。

```lean
theorem positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    PositiveFermat5Refuter :=
  positiveFermat5Refuter_of_counterexamplePackRefuter
    (counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic)
```

ここで実際の composition は

$$
\text{unit classes} + \text{zero arithmetic}
\Longrightarrow
\text{primitive refuter}
\Longrightarrow
\text{positive refuter}
$$

として組み立てられている。

### `goldenUnitClassesModFifth`

unit classification の無条件 provider である。

```lean
theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth := by
  intro epsilon hepsilon
  exact goldenUnitFifthClass_of_unit epsilon hepsilon
```

0424 はこの proof object を第一引数に渡すことで `GoldenUnitClassesModFifth` の仮定を消去する。

## 証明または構築の流れ

0424 自身の proof term は

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

だけである。

### 1. 一般 receiver を取得する

既存 theorem の型は

```lean
GoldenUnitClassesModFifth →
GoldenZeroSectorArithmeticExclusion →
PositiveFermat5Refuter
```

である。

### 2. unit-classification 仮定を埋める

無条件 theorem

```lean
goldenUnitClassesModFifth
```

を第一引数へ渡す。

これにより Lean 上では関数が部分適用され、残る型は概念的に

```lean
GoldenZeroSectorArithmeticExclusion → PositiveFermat5Refuter
```

となる。

### 3. zero-sector arithmetic 仮定を渡す

第二引数として `hArithmetic` を渡すと

```lean
PositiveFermat5Refuter
```

の proof object が得られる。

0424 自身には `intro`、`rw`、`ring`、`omega`、case split、gcd 計算、descent は存在しない。それらはすべて依存先の theorem 群で完了している。

## Lean 固有の処理

### Curry–Howard 対応による proof object の適用

0424 は theorem を通常の関数と同じように適用している。

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

は、型

```lean
A → B → C
```

を持つ proof term に `A` の proof と `B` の proof を順に渡して `C` の proof を得る構造そのものである。

### `abbrev` の透明性

`PositiveFermat5Refuter` は `abbrev : Prop` であるため、必要なら Lean はその定義を展開して

```lean
∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

として扱える。

同様に Main の `FLT5Target` も同じ proposition shape を持つ `abbrev` である。この definitional transparency が、closure 層と public target 層の薄い wrapper 構造を可能にしている。

### tactic を必要としない term-style proof

0424 は `:=` の右辺に完成した proof term を直接置く形式であり、証明状態を開かない。これは依存構造が十分に整理されていることを示す。

## 冗長・重複箇所

0424 は数学的には新しい事実を証明していない。

特に 0419

```lean
flt5Target_of_zeroArithmetic
```

と 0424 は、ともに `GoldenZeroSectorArithmeticExclusion` を受け取り、正の自然数における FLT5 の否定を返す。さらに `FLT5Target` と `PositiveFermat5Refuter` の定義本体も同じ proposition shape である。

したがって、コード量だけを最小化するなら 0424 を削除し、一般 receiver を直接利用することも可能である。

しかし、この重複は意図的な facade と見るのが自然である。0424 を残すことで、利用者は unit-classification の実装詳細を知らずに

```lean
GoldenZeroSectorArithmeticExclusion → PositiveFermat5Refuter
```

という closure 境界だけを利用できる。

## 最適化候補

### 1. 0419 と 0424 の alias 関係を明文化する

`FLT5Target` と `PositiveFermat5Refuter` が同型ではなく実質的に同一の proposition shape を持つため、将来 API を整理するなら一方を他方の alias として定義する方法がある。

例えば概念的には

```lean
abbrev FLT5Target := PositiveFermat5Refuter
```

のようにすれば、両者の関係がさらに明確になる可能性がある。ただし public API 名の安定性や module dependency の向きを考慮する必要があるため、これは設計候補であり、現状コードに必要な変更ではない。

### 2. facade theorem を残すか直接 export するか

0424 は一行 wrapper なので、最小コードを優先するなら削除可能である。一方、proof architecture を文書化する名前付き境界としては価値が高い。現在の Main 層の目的を考えると、保持する方が監査性は高い。

### 3. term-style proof はすでに最小に近い

証明本体については

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

より実質的に短くする余地はほとんどない。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

0424 自身は Mathlib の tactic や個別 theorem を直接呼ばず、プロジェクト内で構築済みの

- `GoldenZeroSectorArithmeticExclusion`
- `PositiveFermat5Refuter`
- `positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic`
- `goldenUnitClassesModFifth`

だけに依存する。

したがって modular source の観点では、0424 単体の直接依存は closure theorem と unit classification provider を公開するプロジェクト内 module に限定できるはずである。

ただし、このリポジトリの standalone artifact では module 群が単一ファイルへ生成結合され `import Mathlib` に集約されている。今回 Lean build は行っていないため、`Mathlib` をどの最小個別 import に分解できるかは確認していない。最小 import closure を断定することはできない。

## Comparator challenge 化の可否

0424 単体は Comparator challenge としては **容易すぎる**。

入力として

```lean
hGeneral : GoldenUnitClassesModFifth →
  GoldenZeroSectorArithmeticExclusion →
  PositiveFermat5Refuter
hClasses : GoldenUnitClassesModFifth
hArithmetic : GoldenZeroSectorArithmeticExclusion
```

を与えれば、解答は単純な関数適用

```lean
exact hGeneral hClasses hArithmetic
```

で終わる。

したがって theorem 単体では Lean の推論能力をほとんど測れない。

一方、challenge として有意味にするなら、依存先をまとめて隠し、

1. `CounterexamplePackRefuter` を unit classification と zero-sector arithmetic から構成する。
2. positive solution を primitive packet へ正規化する。
3. primitive refuter を positive refuter へ持ち上げる。

という 0424 の背後の composition を再構築させる形式が適している。その場合は proof architecture の理解を測る中程度以上の challenge になる。

## 次に読むべき宣言

**なし。**

`positiveFermat5Refuter_of_zeroArithmetic` は、正本 `Flt5DkMath/FLT5StandAlone.lean` に生成結合された `DkMath/FLT/Five/Main.lean` 部分の最後の宣言であり、その直後に

```lean
end DkMath.FLT.Five

/-! ===== END GENERATED SOURCE: DkMath/FLT/Five/Main.lean ===== -/
```

が続く。

したがって 0424 は、この theorem museum が依存順に追ってきた FLT5 standalone source の **最終宣言** である。

数学的な無条件 endpoint 自体は 0420 `flt5Target` と 0421 `fermatFive_no_positive_solution` ですでに完成している。0422〜0424 は Main 層が内部 proof architecture の主要 endpoint も名前付き facade として公開する後段であり、0424 はその最後を閉じる。
