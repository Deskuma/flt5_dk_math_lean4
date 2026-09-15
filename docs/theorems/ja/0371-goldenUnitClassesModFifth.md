# 0371 `goldenUnitClassesModFifth`

## 宣言種別

`theorem`

## Lean コード

```lean
/-- Every golden unit has a representative among five classes modulo fifth powers. -/
theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth := by
  intro epsilon hepsilon
  exact goldenUnitFifthClass_of_unit epsilon hepsilon
```

## Lean の型

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

ここで `GoldenUnitClassesModFifth` は下流向けに用意された命題の略記で、定義は

```lean
abbrev GoldenUnitClassesModFifth : Prop :=
  ∀ epsilon : GoldenInt,
    GoldenUnit epsilon →
    ∃ i : Fin 5, ∃ delta : GoldenInt,
      epsilon = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

である。

したがって theorem の型を展開すると、任意の黄金整数 `epsilon` に対して、それが unit ならば

```lean
∃ i : Fin 5, ∃ delta : GoldenInt,
  epsilon = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

を与える全称定理になる。

数学的には、任意の黄金 unit $\varepsilon$ が

$$
\varepsilon=\varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\}
$$

と表されることを述べる。

## 数学的主張または宣言の意味

この theorem 自体は、0370 `goldenUnitFifthClass_of_unit` が既に証明した分類結果を新しく強化してはいない。

0370 は個々の `x` に対し

```lean
GoldenUnit x → GoldenUnitFifthClass x
```

を与える。一方、今回の `goldenUnitClassesModFifth` はその結果を

```lean
∀ epsilon, GoldenUnit epsilon → ...
```

という下流モジュールが要求する公開 contract にまとめ直す bridge theorem である。

`Fin 5` を使うため、代表指数は厳密に

$$
0,1,2,3,4
$$

の五つに制限される。符号は fifth power 側へ吸収できるため、独立な負符号 class は不要である。

$$
(-\delta)^5=-\delta^5.
$$

従って黄金 unit の無限集合を、fifth powers を法として五つの sector に有限化した結果を、後段へ供給する宣言と解釈できる。

## 証明全体での役割

`GoldenUnitClassification.lean` の最終公開出口に相当する。

直前の 0370 までで、座標 measure、measure-one の四つの基底 unit、strict descent、`φ` と `φ⁻¹` による sector 遷移を使って、任意の黄金 unit の five-sector 分類が構成的に証明された。

今回の theorem は、その内部的な分類述語

```lean
GoldenUnitFifthClass epsilon
```

を、証明後半のモジュールが直接受け取る

```lean
GoldenUnitClassesModFifth
```

という contract に変換する。

実際、この contract は後段の

```lean
signedGoldenFiniteUnitSectorCore_of_unitClasses
```

で仮定として受け取られ、stripped packet から現れる任意の unit factor `epsilon` を五つの sector のいずれかへ落とすために使われる。

さらに

```lean
signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector
counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
flt5Target_of_unitClasses_of_zeroArithmetic
```

などの receiver theorem 群へ流れ込み、unit 分類を FLT5 の最終 refutation chain に接続する。

したがって 0370 が数学的な分類の核心なら、0371 はその結果を証明アーキテクチャ全体へ接続する API 境界である。

## 直接依存する定義・補題

### `GoldenUnitClassesModFifth`

今回の結論そのものを表す `abbrev`。

```lean
abbrev GoldenUnitClassesModFifth : Prop :=
  ∀ epsilon : GoldenInt,
    GoldenUnit epsilon →
    ∃ i : Fin 5, ∃ delta : GoldenInt,
      epsilon = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

この contract は「すべての unit が five-sector 表示を持つ」という global statement である。

### `GoldenUnitFifthClass`

0370 の結論に用いられた個別版の述語。

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

`GoldenUnitClassesModFifth` の各 `epsilon` に対する conclusion と実質的に同じ witness shape を持つ。

### `goldenUnitFifthClass_of_unit`

唯一の実質的直接依存 theorem。

```lean
theorem goldenUnitFifthClass_of_unit
    (x : GoldenInt) (hx : GoldenUnit x) :
    GoldenUnitFifthClass x
```

0370 までの descent 全体を背負っており、今回の theorem はこれを任意の `epsilon` に適用するだけである。

## 証明または構築の流れ

証明は二段階だけである。

### 1. contract の引数を導入する

```lean
intro epsilon hepsilon
```

`GoldenUnitClassesModFifth` を展開したときの

```lean
∀ epsilon : GoldenInt,
  GoldenUnit epsilon → ...
```

から、任意の unit `epsilon` とその証明 `hepsilon` を取り出す。

数学的には「任意の黄金 unit $\varepsilon$ を一つ固定する」に対応する。

### 2. 0370 をそのまま適用する

```lean
exact goldenUnitFifthClass_of_unit epsilon hepsilon
```

0370 の結論 `GoldenUnitFifthClass epsilon` を展開すれば、現在の goal と同じ

```lean
∃ i : Fin 5, ∃ delta : GoldenInt,
  epsilon = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

になるため、そのまま閉じる。

この一行に至るまでの数学的負荷はほぼすべて 0370 側にある。

## Lean 固有の処理

### `abbrev` の透過性

この theorem が極端に短く書ける大きな理由は、`GoldenUnitClassesModFifth` が `abbrev` として定義されていることにある。

Lean は必要に応じてその略記を展開し、

```lean
intro epsilon hepsilon
```

を受理する。さらに `GoldenUnitFifthClass epsilon` の witness shape と conclusion が定義展開で一致するため、明示的な `change` や `simpa [GoldenUnitClassesModFifth, GoldenUnitFifthClass]` を書かずに `exact` で閉じられる。

### `intro`

命題の全称量化と含意を順に導入しているだけであり、特別な algebraic tactic は使っていない。

### `exact`

proof term としては本質的に

```lean
fun epsilon hepsilon =>
  goldenUnitFifthClass_of_unit epsilon hepsilon
```

である。

この theorem は自動化ではなく、既証明 theorem の型整合性だけで成立している。

## 冗長・重複箇所

コードそのものに実質的な冗長性はほぼない。

```lean
by
  intro epsilon hepsilon
  exact goldenUnitFifthClass_of_unit epsilon hepsilon
```

は十分に最小に近い。

ただし設計上は、`GoldenUnitFifthClass` と `GoldenUnitClassesModFifth` が同じ existential witness shape を別名で持っているため、型レベルでは一定の重複がある。

この重複は意図的と考えられる。前者は「ある一つの unit `x` の class」を表す局所述語、後者は「すべての unit が分類可能」という下流への global contract であり、役割を分離することで依存境界が明瞭になる。

## 最適化候補

### 1. theorem を term style に縮約する

現在の証明はすでに短いが、さらに

```lean
theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth :=
  goldenUnitFifthClass_of_unit
```

のような形が elaboration 上通る可能性がある。

ただし `GoldenUnitFifthClass` と `GoldenUnitClassesModFifth` の定義展開を Lean がこの位置で期待通り同一視できるかは、実ビルドを行っていないため未確認である。

現在の `intro` + `exact` は型の意図が明示的で、展示コードとしても読みやすい。

### 2. contract を `∀ x, GoldenUnit x → GoldenUnitFifthClass x` と定義する

例えば

```lean
abbrev GoldenUnitClassesModFifth : Prop :=
  ∀ epsilon : GoldenInt,
    GoldenUnit epsilon → GoldenUnitFifthClass epsilon
```

とすれば witness shape の重複を避けられる。

ただし現在の定義は downstream contract の数式内容を単独で読める利点がある。どちらが良いかは API 設計上の選択であり、現状を誤りとは評価できない。

### 3. public API としての名称整理

`goldenUnitFifthClass_of_unit` と `goldenUnitClassesModFifth` は意味が非常に近い。前者を implementation theorem、後者を receiver-facing theorem として明確に位置づける docstring を維持すると、利用側からの探索性が高まる。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

今回の theorem 本体だけを見ると、必要なのは主として

- `GoldenInt`
- `GoldenUnit`
- `GoldenUnitFifthClass`
- `GoldenUnitClassesModFifth`
- `goldenUnitFifthClass_of_unit`

という同一開発内の宣言であり、theorem 本体は Mathlib の高度な tactic を直接使用しない。

`Fin 5` や自然数、基本論理は下位定義側で必要になるが、この wrapper theorem 自身は `intro` と `exact` だけである。

したがって standalone 全体の `import Mathlib` はこの一宣言に対しては過大である可能性が高い。ただし正確な最小 import は周辺定義と生成 standalone の依存関係を含めて Lean ビルドで検証する必要がある。本作業ではビルドを行っていないため、最小 import は未確認である。

## Comparator challenge 化の可否

**可能。ただし単独では極めて易しい micro challenge 向け。**

challenge としては、次の前提を与える。

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop := ...
abbrev GoldenUnitClassesModFifth : Prop := ...

theorem goldenUnitFifthClass_of_unit
    (x : GoldenInt) (hx : GoldenUnit x) :
    GoldenUnitFifthClass x := ...
```

そして target を

```lean
theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth := by
  ...
```

とすればよい。

評価対象は数学的探索ではなく、`abbrev` の展開、全称量化の導入、既存 theorem の再利用、definitionally equal な goal の認識になる。

より有意義な Comparator challenge にするなら、0370 と 0371 を組にして「strong induction による unit 分類を証明し、それを public contract へ接続せよ」とする方が適している。

## 技術的意味

この theorem の重要性はコード長では測れない。

0370 までの大きな descent proof を、後段が要求する一つの名前付き仮定

```lean
GoldenUnitClassesModFifth
```

へ圧縮することで、以後の証明は unit 群の内部分類方法を知る必要がなくなる。

すなわちここは、

$$
\text{unit descent implementation}
\longrightarrow
\text{five-sector public contract}
$$

という abstraction boundary である。

この境界のおかげで、下流の zero-sector arithmetic や packet refutation は、unit 分類が「どう証明されたか」ではなく「五つに分類できる」という事実だけに依存できる。

形式化設計としては、実装詳細と receiver theorem 群を分離する重要な接続点である。

## 次に読むべき宣言

次は、依存順では `GoldenUnitClassification.lean` を終えて、後続の `SignedGoldenZeroSectorDescent.lean` に進み、最初の未解説宣言を確認すべきである。

リポジトリ正本上で次の宣言を改めて確認してから連番を割り当てる必要がある。今回確認した範囲では `goldenUnitClassesModFifth` 自体が `GoldenUnitClassification.lean` の末尾であるため、次回は後続モジュールの冒頭から選定するのが正しい。
