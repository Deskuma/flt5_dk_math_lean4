# 0418 `flt5Target_of_unitClasses_of_zeroArithmetic`

## 宣言種別

`theorem`

## Lean の型

```lean
/-- Conditional receiver exposing both unit classification and zero-sector arithmetic. -/
theorem flt5Target_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

## 数学的主張・宣言の意味

この theorem は、黄金整数環側で必要となる二つの最終入力

1. `GoldenUnitClassesModFifth` — 黄金単元を第五冪剰余類で分類できること
2. `GoldenZeroSectorArithmeticExclusion` — unit class の zero sector に残る Diophantine 候補を算術的に排除できること

を仮定すれば、指数 5 の Fermat 方程式に正の自然数解が存在しないという公開 target `FLT5Target` が従うことを述べる。

型を数式的に読むと

$$
\mathrm{GoldenUnitClassesModFifth}
\to
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{FLT5Target}
$$

であり、0417 `FLT5Target` を展開すれば結論は

$$
\forall x,y,z\in\mathbb N_{>0},
\qquad
x^5+y^5\ne z^5
$$

である。

この theorem 自身は新しい数論計算を行わない。既に closure 層で証明されている

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
```

を Main 層の公開 target にそのまま接続する receiver theorem である。

## 証明全体での役割

0417 では最終仕様

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

が定義された。0418 はその型を初めて返す theorem であり、Main 層における最初の conditional endpoint である。

直前までの closure 層では 0409

```lean
theorem positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    PositiveFermat5Refuter :=
  positiveFermat5Refuter_of_counterexamplePackRefuter
    (counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic)
```

が既に得られている。

`PositiveFermat5Refuter` と `FLT5Target` はともに

```lean
∀ x y z : ℕ,
  0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

という同じ proposition shape を持つ `abbrev` なので、0418 は closure theorem の proof object を型変換なしでそのまま返せる。

従って証明アーキテクチャ上は

$$
\text{unit classification}
+
\text{zero-sector arithmetic}
\Longrightarrow
\text{primitive closure}
\Longrightarrow
\text{positive Fermat refuter}
\Longrightarrow
\text{public FLT5 target}
$$

という長い経路の最後の module-boundary adapter に相当する。

また後続では仮定が順に消される。

```lean
theorem flt5Target_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  flt5Target_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

で `GoldenUnitClassesModFifth` が既証明 theorem `goldenUnitClassesModFifth` によって埋められ、さらに

```lean
theorem flt5Target : FLT5Target :=
  flt5Target_of_zeroArithmetic goldenZeroSectorArithmeticExclusion
```

で zero-sector arithmetic も既証明値に置換される。

0418 はこの最終三段合成の最初の段である。

## 直接依存する定義・補題

### `GoldenUnitClassesModFifth`

正本では

```lean
abbrev GoldenUnitClassesModFifth : Prop :=
  ∀ epsilon : GoldenInt,
    GoldenUnit epsilon →
    ∃ i : Fin 5, ∃ delta : GoldenInt,
      epsilon = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

と定義されている。

これは任意の黄金単元 `epsilon` が、第五冪を除けば

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

の五つの unit class のいずれかに入るという contract である。

0418 自身は分類証明の内部を見ず、完成済み contract `hClasses` だけを受け取る。

### `GoldenZeroSectorArithmeticExclusion`

zero-sector に残る整数パラメータ候補を排除する算術 contract である。正本では `abbrev ... : Prop := ∀ (r s : ℤ) (a b : ℕ), ...` として公開され、primitive / tenth-power split から出現する Diophantine configuration を否定する。

0418 はこの contract の内部証明にも立ち入らず、`hArithmetic` として closure theorem へ渡すだけである。

### `positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic`

0418 の本体が直接呼び出す唯一の DkMath theorem である。

```lean
theorem positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    PositiveFermat5Refuter := ...
```

この theorem が primitive normalization、signed golden factorization、unit-class elimination、zero-sector closure を既に吸収しているため、Main 層ではその結果を再利用するだけでよい。

### `FLT5Target`

0417 で定義された公開 target。

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

0418 の結論型である。

## 証明の流れ

証明は term-style の一行で完結する。

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

流れを展開すると次の通りである。

### 1. unit classification を受け取る

```lean
hClasses : GoldenUnitClassesModFifth
```

黄金単元の第五冪剰余類分類を closure theorem に渡す。

### 2. zero-sector exclusion を受け取る

```lean
hArithmetic : GoldenZeroSectorArithmeticExclusion
```

unit-class analysis 後に残る zero sector の算術排除 contract を渡す。

### 3. closure theorem を適用する

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

結果型は `PositiveFermat5Refuter` である。

### 4. `FLT5Target` として受理される

`PositiveFermat5Refuter` と `FLT5Target` の定義本体が一致するため、Lean の definitional equality によってその proof object がそのまま `FLT5Target` の inhabitant として受理される。

明示的な `exact`、`simpa`、`change`、`unfold` は不要である。

## Lean 固有の処理

### `abbrev` 間の definitional equality

この theorem の最重要 Lean 的特徴は、結論型の名前と実際に返している theorem の結果型の名前が異なるのに、変換コードが一切ない点である。

概念的には

```lean
PositiveFermat5Refuter
```

を返しているが、要求されているのは

```lean
FLT5Target
```

である。

双方が透明な `abbrev` で、展開後の proposition が同じため Lean が型検査時に自動で一致させる。

もし一方が opaque な定義で proposition body も直接は同一視できない設計なら、`change` や equivalence theorem が必要になる可能性がある。

### theorem application の Curry 化

二つの仮定は

```lean
(hClasses : ...)
(hArithmetic : ...)
```

として curried argument になっている。

従って本体は

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

という通常の関数適用そのものである。

### tactic block を使わない term proof

```lean
:=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

という proof term 形式であり、`by` block を必要としない。

この形式は「新しい推論をしているのではなく、既存 theorem の型を公開 API に運んでいるだけ」という設計意図をよく表している。

## 冗長・重複箇所

0418 は論理的には 0409 とほぼ同じ theorem である。

0409 は

```lean
... : PositiveFermat5Refuter
```

を返し、0418 は

```lean
... : FLT5Target
```

を返す。

両 target の proposition body は同一なので、数学的内容の追加はない。

ただしこれは単純な無駄ではなく、module architecture 上の意図的な wrapper である。

- 0409: closure 層の内部 API
- 0418: Main 層の公開 endpoint

つまり同じ proof object に対し、内部用名称と公開用名称を分離している。

また 0418 と 0419 `flt5Target_of_zeroArithmetic` も非常に薄い wrapper が連続する。0418 は unit-class と zero-sector の両方を外部入力として残し、0419 は unit-class だけを既証明値で固定する。これは依存境界を段階的に可視化するための意図的重複である。

## 最適化候補

### 1. 0418 を省略して直接 0419 を構築する

コード量だけを減らすなら 0419 から直接

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

を返せるため、0418 は削除可能である。

しかしそうすると「unit classification と zero-sector arithmetic があれば Main target が閉じる」という重要な dependency cut が名前付き theorem として失われる。

形式化の監査性や Comparator challenge 化を考えると、現状の receiver theorem を残す価値は高い。

### 2. `FLT5Target` を `PositiveFermat5Refuter` の alias にする

0417 でも述べたように

```lean
abbrev FLT5Target : Prop := PositiveFermat5Refuter
```

とすれば両者の同型性がさらに明示的になる。

ただし Main 層だけを読む際の自己記述性は下がる。

### 3. generic receiver combinator への抽象化

同一 proposition shape の内部 alias を公開 alias へ運ぶだけの wrapper は一般化可能だが、この一箇所のために generic theorem を導入すると抽象化コストの方が大きい。

現状の一行 theorem の方が可読性は高い。

## 必要な Mathlib import

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

0418 自身が直接使用する Lean 機能はほぼ core の関数適用と型検査だけである。数論 tactic、ring tactic、valuation API などはこの theorem 本体では使われない。

実質的な依存は DkMath 側の次の宣言を提供する module 群である。

- `FLT5Target`
- `GoldenUnitClassesModFifth`
- `GoldenZeroSectorArithmeticExclusion`
- `positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic`

standalone manifest ではこれらが `GoldenUnitClassification.lean`、`SignedGoldenClosure.lean`、`SignedGoldenZeroSectorFinal.lean`、`Main.lean` へ至る ordered module chain に含まれている。

### import 最適化候補

0418 単独のために `import Mathlib` 全体が必要とは考えにくい。分割ソースの `Main.lean` では、上記 DkMath declarations を供給する module imports だけで十分な可能性が高い。

ただし、この repository では standalone artifact は確認できたものの、今回の条件では Lean build を実施しておらず、分割ソース側の最小 Mathlib import closure も実測していない。

従って具体的な最小 import 名については未確認であり、推測で断定しない。

## Comparator challenge 化の可否

**適している。難度は低〜中程度。**

0418 は一行 theorem だが、challenge としては次の architecture を理解できるかを測れる。

- `GoldenUnitClassesModFifth`
- `GoldenZeroSectorArithmeticExclusion`
- closure theorem `positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic`
- `PositiveFermat5Refuter` と `FLT5Target` の definitional equality

単純な穴埋めなら

```lean
theorem challenge
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target := by
  ?_
```

として、既存 closure theorem を発見して適用できるかを見る形になる。

難度を上げるなら 0409 を直接利用不可にし、`counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic` と `positiveFermat5Refuter_of_counterexamplePackRefuter` から同じ target を再構築させるとよい。この場合は closure architecture の二段構成を理解する必要がある。

さらに 0419〜最終 `flt5Target` までを一つの challenge にまとめれば、conditional assumptions を既証明 provider で順番に discharge する最終 composition 全体を試験できる。

## 次に読むべき宣言

次は 0419

```lean
theorem flt5Target_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  flt5Target_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

である。

0418 では

$$
\mathrm{GoldenUnitClassesModFifth}
+
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\mathrm{FLT5Target}
$$

だった。

0419 では既証明の

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

を代入して unit-class assumption を消し、

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\mathrm{FLT5Target}
$$

まで進む。

その次に無条件の `goldenZeroSectorArithmeticExclusion` を代入すれば `flt5Target : FLT5Target` が完成するため、0419 は最終 endpoint 直前の receiver である。
