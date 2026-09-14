# 0422 `signedGoldenFiniteUnitSectorCore`

## 宣言種別

`theorem`

## Lean の型

```lean
/-- Every stripped golden packet is unconditionally reduced to the five sectors. -/
theorem signedGoldenFiniteUnitSectorCore : SignedGoldenFiniteUnitSectorCore :=
  signedGoldenFiniteUnitSectorCore_of_unitClasses goldenUnitClassesModFifth
```

## 数学的主張・宣言の意味

0422 は、ramifier を除去した signed golden packet が、無条件に五つの unit sector のいずれかへ還元されることを公開する theorem である。

直接の結論 `SignedGoldenFiniteUnitSectorCore` は `abbrev : Prop` として

```lean
abbrev SignedGoldenFiniteUnitSectorCore : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w),
    ∃ i : Fin 5, ∃ gamma : GoldenInt,
      p.beta = goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)
```

と定義されている。

したがって数学的には、任意の stripped packet `p` に付随する golden integer `p.beta` が

$$
\beta = \phi^i\gamma^5,
\qquad i\in\{0,1,2,3,4\}
$$

の形に必ず書ける、という主張である。

ここで五つの sector は幾何学的な角度区分ではなく、golden order の unit を fifth powers で割った剰余類の代表

$$
1,\ \phi,\ \phi^2,\ \phi^3,\ \phi^4
$$

に対応する代数的 sector である。符号は指数 5 が奇数であるため `gamma` 側へ吸収でき、別の符号 sector を必要としない。

0422 自身はこの分類を新たに証明するのではなく、すでに構築済みの unit-classification theorem を sector reduction receiver に供給することで、条件付き proposition を無条件化する。

## 証明全体での役割

0422 は FLT5 の最終結論 0420–0421 より後に置かれているが、数学的には証明内部の重要な中間構造を public facade として再公開する theorem である。

証明アーキテクチャでは、まず coprime factorization により stripped packet の `beta` を

$$
\beta = \varepsilon\gamma^5
$$

と書き、ここで `epsilon` は golden unit となる。次に unit classification により

$$
\varepsilon = \phi^i\delta^5
$$

と書けるので、

$$
\beta
= \phi^i\delta^5\gamma^5
= \phi^i(\delta\gamma)^5
$$

となり、五つの sector へ有限化される。

この有限化が後続の `SignedGoldenSectorArithmetic` で sector `i = 1,2,3,4` を排除し、`i = 0` の zero sector だけを strict descent へ送るための分岐点である。

0422 の役割は、その有限 sector reduction が研究上の仮定ではなく、すでに証明済みの `goldenUnitClassesModFifth` によって **無条件に成立する** ことを Main 層で明示することにある。

## 直接依存する定義・補題

### `SignedGoldenFiniteUnitSectorCore`

`SignedGoldenUnitClasses.lean` で定義された `abbrev : Prop` である。

```lean
abbrev SignedGoldenFiniteUnitSectorCore : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w),
    ∃ i : Fin 5, ∃ gamma : GoldenInt,
      p.beta = goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)
```

0422 の conclusion はこの proposition そのものである。

### `GoldenUnitClassesModFifth`

同じく `SignedGoldenUnitClasses.lean` で公開される unit-classification contract である。

```lean
abbrev GoldenUnitClassesModFifth : Prop :=
  ∀ epsilon : GoldenInt,
    GoldenUnit epsilon →
    ∃ i : Fin 5, ∃ delta : GoldenInt,
      epsilon = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

これは任意の golden unit を、五つの代表 `phi^i` と fifth power の積へ還元する contract である。

### `signedGoldenFiniteUnitSectorCore_of_unitClasses`

0422 が直接呼び出す receiver theorem である。

```lean
theorem signedGoldenFiniteUnitSectorCore_of_unitClasses
    (hClasses : GoldenUnitClassesModFifth) :
    SignedGoldenFiniteUnitSectorCore := by
  intro u v w p
  obtain ⟨epsilon, gamma, hepsilon, hbeta⟩ :=
    signedGoldenFifthPowerUpToUnitCore p
  obtain ⟨i, delta, hdelta⟩ := hClasses epsilon hepsilon
  refine ⟨i, goldenMul delta gamma, ?_⟩
  rw [hbeta, hdelta]
  simp only [golden_mul_eq, golden_pow_eq]
  rw [mul_pow]
  ring
```

この theorem が実際の factorization と unit-classification の合成を担当している。

### `goldenUnitClassesModFifth`

`GoldenUnitClassification.lean` で無条件に証明された provider theorem である。

```lean
theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth := by
  intro epsilon hepsilon
  exact goldenUnitFifthClass_of_unit epsilon hepsilon
```

0422 はこれを `signedGoldenFiniteUnitSectorCore_of_unitClasses` の唯一の仮定として供給する。

### 間接的な核 `signedGoldenFifthPowerUpToUnitCore`

0422 の本体から直接は見えないが、receiver の内部では

```lean
signedGoldenFifthPowerUpToUnitCore p
```

によって

```lean
∃ epsilon gamma,
  GoldenUnit epsilon ∧
  p.beta = goldenMul epsilon (goldenPow gamma 5)
```

型の factorization data が取り出される。この theorem は golden order の coprime factor theorem を FLT5 packet に接続したものなので、五 sector 化の代数的入口となる。

## 証明または構築の流れ

0422 自身の proof term は一行である。

```lean
signedGoldenFiniteUnitSectorCore_of_unitClasses goldenUnitClassesModFifth
```

流れは次のように分解できる。

### 1. 条件付き receiver を取得する

既存 theorem

```lean
signedGoldenFiniteUnitSectorCore_of_unitClasses :
  GoldenUnitClassesModFifth → SignedGoldenFiniteUnitSectorCore
```

は、unit classification が与えられれば stripped packet を五 sector へ還元できることを表す。

### 2. unit classification の無条件 provider を供給する

`GoldenUnitClassification.lean` で

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

がすでに証明されている。

これは coordinate measure による unit descent を用いて、すべての golden unit が fifth-power modulo で `phi^i`, `i : Fin 5` のいずれかに属することを証明した結果である。

### 3. receiver の最後の仮定を discharge する

両者を関数適用で合成すると

```lean
signedGoldenFiniteUnitSectorCore_of_unitClasses
  goldenUnitClassesModFifth
```

の型はそのまま

```lean
SignedGoldenFiniteUnitSectorCore
```

となる。

従って 0422 自身には tactic block、rewrite、case split、算術処理は不要である。

## Lean 固有の処理

### proposition を theorem argument として渡す

`GoldenUnitClassesModFifth` は `Prop` であり、

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

はその proof object である。

一方、receiver は

```lean
signedGoldenFiniteUnitSectorCore_of_unitClasses :
  GoldenUnitClassesModFifth → SignedGoldenFiniteUnitSectorCore
```

なので、0422 は Curry–Howard 対応そのままの関数適用で閉じる。

### `abbrev` の definitional transparency

`GoldenUnitClassesModFifth` と `SignedGoldenFiniteUnitSectorCore` はどちらも `abbrev : Prop` である。したがって Lean は必要に応じてそれぞれの quantified proposition へ透明に展開できる。

ただし 0422 の term-style proof では明示的な `unfold` は必要ない。型がそのまま一致しているためである。

### `Fin 5` による有限 sector の型レベル表現

sector index は自然数条件を別に持つのではなく

```lean
i : Fin 5
```

として表される。これにより `i.val < 5` が型に組み込まれ、後続の `fin_cases` による五分岐と整合する。

## 冗長・重複箇所

0422 の proof body は、数学的には既存 receiver と既存 provider の単純 composition であり、新しい number-theoretic content はない。

また `signedGoldenFiniteUnitSectorCore_of_unitClasses goldenUnitClassesModFifth` を利用者が直接書けば、0422 を経由せず同じ proof object を得られる。その意味では情報量としては重複している。

しかし Main 層の facade theorem としては意味がある。

- conditional interface と unconditional result を分離できる。
- `signedGoldenFiniteUnitSectorCore` という名前だけで無条件 provider を検索できる。
- unit classification がすでに discharge 済みであることを API 上で明示できる。
- proof architecture の監査時に、どの仮定がどこで閉じられたかを追いやすい。

したがってこの重複は、0418–0420 と同様に意図的な endpoint/facade duplication と評価できる。

## 最適化候補

### 1. facade theorem を削除する

最小コードだけを目指すなら 0422 は削除できる。

```lean
signedGoldenFiniteUnitSectorCore_of_unitClasses goldenUnitClassesModFifth
```

を必要箇所で直接使用すればよい。

ただし公開 API と依存関係の可読性が低下するので、現行設計では残す価値がある。

### 2. proof syntax は現行が最短

例えば

```lean
by
  exact signedGoldenFiniteUnitSectorCore_of_unitClasses
    goldenUnitClassesModFifth
```

とも書けるが、現行 term-style の方が短い。

`simpa` や `unfold` も不要であり、Lean コード上の局所最適化余地はほぼない。

### 3. architecture 上の統合

もし将来 Main 層の facade theorem を大量に整理するなら、provider naming policy を統一して

```text
<contract>_of_<assumption>
<contract>
```

という conditional/unconditional pair を機械的に追える形へ揃える余地はある。0422 はすでにほぼその形になっている。

## 必要な Mathlib import

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

ただし 0422 本体が直接行うことは theorem application だけであり、特殊な Mathlib tactic や API を新たに使用していない。

0422 を成立させるために直接必要なのは、少なくとも次の FLT5 declarations が環境中に存在することである。

- `SignedGoldenFiniteUnitSectorCore`
- `signedGoldenFiniteUnitSectorCore_of_unitClasses`
- `GoldenUnitClassesModFifth`
- `goldenUnitClassesModFifth`

それらの定義・証明の推移依存として `GoldenInt`, `GoldenUnit`, `goldenMul`, `goldenPow`, `Fin 5`, packet structures、Euclidean/gcd machinery 等が必要になる。

### import 最適化候補

0422 自身のためだけに `Mathlib` 全体を直接 import する必要性は低く、分割 source では `SignedGoldenUnitClasses` と `GoldenUnitClassification`、さらにそれらの推移 import があれば十分である可能性が高い。

ただし今回は Lean build を実行していないため、最小の Mathlib module 集合や最小 import closure は実測していない。具体的な最小 import 名は未確認事項として断定しない。

## Comparator challenge 化の可否

 **適している。単体では低難度だが、dependency selection challenge として明瞭である。**

最小 challenge は例えば

```lean
theorem challenge : SignedGoldenFiniteUnitSectorCore := by
  ?_
```

とし、環境に

```lean
signedGoldenFiniteUnitSectorCore_of_unitClasses :
  GoldenUnitClassesModFifth → SignedGoldenFiniteUnitSectorCore

goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

だけを主要候補として置く形である。

solver が provider と receiver の型を正しく接続できれば

```lean
exact signedGoldenFiniteUnitSectorCore_of_unitClasses
  goldenUnitClassesModFifth
```

で閉じる。

より価値の高い challenge にするなら `goldenUnitClassesModFifth` を隠し、`goldenUnitFifthClass_of_unit` から `GoldenUnitClassesModFifth` を再構成させる。その場合、solver は

1. contract の quantified shape を読む。
2. `epsilon` と `GoldenUnit epsilon` を導入する。
3. unit-classification theorem を適用する。
4. 得られた contract を sector receiver に供給する。

という二段 composition を行う必要があり、Comparator での theorem-selection と interface-understanding の評価に適する。

さらに難度を上げるなら `signedGoldenFiniteUnitSectorCore_of_unitClasses` 自体も隠し、`signedGoldenFifthPowerUpToUnitCore` と unit classification から sector witness `i, gamma` を構成させれば、`rw`, `mul_pow`, ring normalization を含む実質的 proof challenge になる。

## 次に読むべき宣言

次は 0423 `counterexamplePackRefuter_of_zeroArithmetic`、種別は `theorem` である。

```lean
/-- The zero-sector arithmetic proposition refutes every primitive packet. -/
theorem counterexamplePackRefuter_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter :=
  counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

0422 が finite unit-sector core の無条件 facade を公開した後、0423 は再び zero-sector arithmetic を仮定として受け取り、すでに証明済みの unit classification を内部で供給することで、すべての primitive `CounterexamplePack` を refute する receiver を Main 層へ公開する。

従って依存順の解説は 0423 へ続く。