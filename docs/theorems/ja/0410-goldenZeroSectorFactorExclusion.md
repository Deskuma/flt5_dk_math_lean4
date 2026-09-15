# 0410 `goldenZeroSectorFactorExclusion`

## 宣言種別

`theorem`

## Lean の型

```lean
theorem goldenZeroSectorFactorExclusion : GoldenZeroSectorFactorExclusion := by
  intro packet
  exact goldenZeroSectorCandidate_false packet.inversion.source
```

`GoldenZeroSectorFactorExclusion` は直前の factorization 層で定義された `abbrev` であり、展開すると

```lean
GoldenZeroSectorFactorPacket → False
```

である。

したがってこの theorem は、任意の認証済み zero-sector factor packet が矛盾を導くことを無条件に証明する。

## 数学的主張

`GoldenZeroSectorFactorPacket` は、zero sector の原始算術データから構成された inversion packet と、その inversion から得られる三つの exact factor branch のいずれかを保持する。

その factor branch は

- odd branch,
- even-left-low branch,
- even-right-low branch

のいずれかであり、各 branch には fifth-power factorization、coprimality、二進付値の割当、差の方程式などが記録されている。

しかし 0410 は、それら三分岐を改めて場合分けして矛盾させる theorem ではない。

各 factor packet は

```lean
packet.inversion.source
```

として元の `GoldenZeroSectorCandidate` を完全に保持している。そして、その candidate が存在し得ないことは先行する無限降下 theorem

```lean
goldenZeroSectorCandidate_false
```

ですでに証明済みである。

従って論理は単純に

$$
\mathrm{GoldenZeroSectorFactorPacket}
\longrightarrow
\mathrm{GoldenZeroSectorInversionPacket}
\longrightarrow
\mathrm{GoldenZeroSectorCandidate}
\longrightarrow
\bot
$$

となる。

つまり、factorization 層でどの branch が選ばれたとしても、その packet の provenance を元 candidate まで戻せば、既証明の strict infinite descent によって一括して排除できる。

## 証明全体での役割

この theorem は `SignedGoldenZeroSectorFinal.lean` の最初の finalization theorem である。

ここまでの zero-sector 証明は概略として次の順に進んでいる。

1. `GoldenZeroSectorCandidate` に primitive zero-sector の生の算術条件を集約する。
2. inversion により `A0`, `B0` の積・差・正値性などを持つ `GoldenZeroSectorInversionPacket` を作る。
3. 二進付値によって三つの factor branch に分解し、`GoldenZeroSectorFactorPacket` を作る。
4. 別の descent 層では candidate から `GoldenZeroSectorDescentPacket` を作り、strictly smaller な packet を反復生成する。
5. `Nat.strong_induction_on` により `goldenZeroSectorDescentPacket_false` を証明し、そこから `goldenZeroSectorCandidate_false` を得る。

0410 は 3 の factor packet と 5 の candidate-level impossibility を接続する。

この接続により、factorization 層で公開されていた receiver

```lean
GoldenZeroSectorFactorExclusion
```

が仮定ではなく実際の theorem として充足される。

後続ではこの factor-level exclusion を public な

```lean
GoldenZeroSectorArithmeticExclusion
```

へ変換し、最終的に `PositiveFermat5Refuter` と `FLT5Target` へ供給する。

従って 0410 は、新しい数論を証明する箇所というより、長い zero-sector descent の結果を factorization API に差し戻す **final closure bridge** である。

## 直接依存する定義・補題

### `GoldenZeroSectorFactorExclusion`

factorization 層で定義された receiver proposition。

```lean
abbrev GoldenZeroSectorFactorExclusion : Prop :=
  GoldenZeroSectorFactorPacket → False
```

0410 の結論型そのものである。

### `GoldenZeroSectorFactorPacket`

```lean
structure GoldenZeroSectorFactorPacket : Type where
  inversion : GoldenZeroSectorInversionPacket
  factors : GoldenZeroSectorFactorData inversion
```

factorization 後の完全 packet である。

0410 が直接利用するのは `factors` ではなく

```lean
packet.inversion
```

だけである。これは重要で、三つの factor branch の詳細をこの theorem では一切再解析しない。

### `GoldenZeroSectorInversionPacket.source`

`GoldenZeroSectorInversionPacket` が保持する元 candidate。

したがって

```lean
packet.inversion.source
```

の型は

```lean
GoldenZeroSectorCandidate
```

である。

factorization の途中で元の primitive arithmetic provenance が失われていないため、この projection だけで descent theorem の入力へ戻れる。

### `goldenZeroSectorCandidate_false`

先行する descent 層の theorem。

```lean
theorem goldenZeroSectorCandidate_false
    (p : GoldenZeroSectorCandidate) : False :=
  goldenZeroSectorDescentPacket_false
    (goldenZeroSectorDescentPacket_of_candidate p)
```

任意の `GoldenZeroSectorCandidate` を recursive descent invariant に入れ、strict descent によって否定する。

0410 の数学的内容の本体は、この既証明 theorem を factor packet の source に適用することに尽きる。

## 証明の流れ

証明は二段だけである。

### 1. factor exclusion の引数を導入する

```lean
intro packet
```

`GoldenZeroSectorFactorExclusion` が reducible abbreviation なので、Lean は目標を実質的に

```lean
GoldenZeroSectorFactorPacket → False
```

として扱う。

従って `intro packet` 後の context は

```lean
packet : GoldenZeroSectorFactorPacket
⊢ False
```

となる。

### 2. source candidate を既証明の無限降下へ渡す

```lean
exact goldenZeroSectorCandidate_false packet.inversion.source
```

projection の型は順に

```lean
packet.inversion
  : GoldenZeroSectorInversionPacket

packet.inversion.source
  : GoldenZeroSectorCandidate
```

である。

`goldenZeroSectorCandidate_false` はその candidate から `False` を返すため、目標が直ちに閉じる。

ここには新しい branch split、合同式、coprimality 計算、valuation 計算、あるいは descent construction は存在しない。それらはすべて先行 theorem に封じ込められている。

## Lean 固有の処理

### `abbrev` の透過展開

結論型は名前付きの

```lean
GoldenZeroSectorFactorExclusion
```

だが、証明冒頭で `unfold` は不要である。

Lean は `abbrev` を reducible として扱うため、`intro packet` に必要な function type

```lean
GoldenZeroSectorFactorPacket → False
```

へ自動的に展開できる。

### nested structure projection

```lean
packet.inversion.source
```

は二段の structure projection である。

Lean は

```lean
packet : GoldenZeroSectorFactorPacket
```

から `.inversion` の型を推論し、さらにその結果から `.source` の型を推論する。

この provenance chain が型として保持されているため、途中のデータを再構築する必要がない。

### `False` を返す theorem の直接適用

```lean
goldenZeroSectorCandidate_false packet.inversion.source
```

の結果型そのものが `False` であるため、`exact` だけで証明が完了する。

`False.elim` や `by_contra` は不要である。

### branch data を消費しないことも型安全

`GoldenZeroSectorFactorPacket` には

```lean
factors : GoldenZeroSectorFactorData inversion
```

が含まれるが、0410 はこれを参照しない。

Lean では structure の全 field を証明中に使用する義務はない。packet の existence 自体が source candidate の existence を含意し、その source が既に不可能だと分かっているため、`factors` の内容はこの closure theorem には不要である。

## 冗長・重複箇所

0410 の proof body 自体には実質的な重複はない。

一見すると、`GoldenZeroSectorFactorPacket` を構築するために大規模な factorization を行ったにもかかわらず、最終 exclusion では `packet.factors` を全く使わないため、factorization 層全体が冗長に見える可能性がある。

しかし repository 上の構造を見る限り、factorization 層には独立した数学的価値がある。

- exact two-adic branch data を公開する。
- odd branch の modulo-eleven channel を記録する。
- source-level arithmetic と branch-level arithmetic の間の監査可能な中間構造を提供する。
- `GoldenZeroSectorFactorArithmeticExclusion` という receiver boundary を形成する。

一方、現在の unconditional closure はより強い `goldenZeroSectorCandidate_false` をすでに得ているため、0410 では branch-specific contradiction を再利用する必要がない。

従って **factorization が冗長なのではなく、final theorem が意図的に最強の既証明結果を再利用して短くなっている** と読むのが自然である。

## 最適化候補

### 1. term-style へ短縮可能

現在の証明

```lean
by
  intro packet
  exact goldenZeroSectorCandidate_false packet.inversion.source
```

はすでに十分短いが、技術的には

```lean
fun packet => goldenZeroSectorCandidate_false packet.inversion.source
```

という term-style にできる。

ただし現行形の方が theorem が function-valued receiver を実装していることを読み取りやすく、最適化効果はほぼない。

### 2. branch ごとの contradiction を追加しない

`packet.factors` を `cases` して三 branch を個別に処理することも可能だが、既に source candidate 全体が impossible なので冗長である。

0410 に関しては現在の provenance-based proof が最も良い。

### 3. provenance projection の helper は不要

例えば

```lean
GoldenZeroSectorFactorPacket.source
```

のような shortcut accessor を追加すれば `packet.inversion.source` を短縮できるが、この二段 projection は十分明瞭であり、専用 helper の導入価値は小さい。

## 必要な Mathlib import

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

0410 の proof body 自身が直接使用する Mathlib theorem や tactic はほぼなく、必要なのは先行する FLT5 内部宣言である。

直接必要な logical interface は

- `GoldenZeroSectorFactorPacket`
- `GoldenZeroSectorFactorExclusion`
- `GoldenZeroSectorInversionPacket.source`
- `GoldenZeroSectorCandidate`
- `goldenZeroSectorCandidate_false`

である。

生成元の module 順では、factorization と descent の双方がすでに読み込まれた後の `SignedGoldenZeroSectorFinal.lean` にこの theorem が置かれている。

### import 最適化候補

0410 単体だけを見れば `import Mathlib` は大幅に広い。

分割 source では、概念的には

- factor packet と factor-exclusion receiver を提供する factorization module
- `goldenZeroSectorCandidate_false` を提供する descent module

があれば theorem body は記述できる。

ただし、この解説作業では Lean build を行っていないため、具体的な最小 import セットが実際にコンパイル可能かは確認していない。従って exact minimal import 名の断定はしない。

## Comparator challenge 化の可否

**可能。ただし単体では低難度。**

challenge としては、structure provenance と receiver abbreviation を正しく追えるかを測る題材になる。

例えば次だけを与える。

```lean
abbrev GoldenZeroSectorFactorExclusion : Prop :=
  GoldenZeroSectorFactorPacket → False

axiom goldenZeroSectorCandidate_false
    (p : GoldenZeroSectorCandidate) : False
```

さらに packet structure が

```lean
packet.inversion.source : GoldenZeroSectorCandidate
```

を持つことを context に含め、0410 の proof hole を埋めさせる。

評価できる点は

- `abbrev` の展開を理解できるか
- nested structure projection を追跡できるか
- branch data が不要であることを見抜けるか
- 既存の stronger theorem を最短経路で再利用できるか

である。

算術推論や無限降下そのものを Comparator に評価させたい場合は、この wrapper ではなく `goldenZeroSectorDescentPacket_false` や `GoldenZeroSectorDescentPacket.strictDescent` を challenge 化する方がはるかに有意義である。

## 次に読むべき宣言

次は 0411

```lean
theorem goldenZeroSectorArithmeticExclusion_of_factorExclusion
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion hFactor
```

である。

0410 が

$$
\mathrm{GoldenZeroSectorFactorExclusion}
$$

を無条件に供給したのに対し、0411 はその factor-level receiver を `SignedGoldenClosure` が公開している source-level receiver

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
$$

へ変換する。

つまり finalization の流れは

$$
\mathrm{GoldenZeroSectorCandidate}
\xrightarrow{\text{strict descent}}
\bot
$$

から 0410 で

$$
\mathrm{GoldenZeroSectorFactorExclusion}
$$

を得て、0411 で

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
$$

へ戻す構成である。

その次には、この変換へ 0410 を実際に代入して public zero-sector arithmetic exclusion を無条件化する theorem が続く。