# 0411 `goldenZeroSectorArithmeticExclusion_of_factorExclusion`

## 宣言種別

`theorem`

## Lean の型

```lean
theorem goldenZeroSectorArithmeticExclusion_of_factorExclusion
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion hFactor
```

この theorem は、factorization 層で得られた exclusion receiver

```lean
GoldenZeroSectorFactorExclusion
```

から、closure 層が公開している zero-sector の算術的 exclusion contract

```lean
GoldenZeroSectorArithmeticExclusion
```

を構成する。

証明本体は既存 theorem

```lean
goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion
```

への直接適用だけである。

## 数学的主張

`GoldenZeroSectorArithmeticExclusion` は、zero-sector に現れる整数座標 `r, s` と正整数データ `a, b` が、以下の primitive arithmetic 条件を同時に満たす状況を排除する proposition である。

中心となる条件は次の形である。

```lean
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
  ... →
  False
```

末尾には tenth-power split の存在条件が続く。正本では `GoldenZeroSectorFactorArithmeticExclusion` と `GoldenZeroSectorArithmeticExclusion` が同じ raw arithmetic contract を表すように設計されている。

したがって数学的には、

$$
\mathrm{GoldenZeroSectorFactorExclusion}
\Longrightarrow
\mathrm{GoldenZeroSectorArithmeticExclusion}
$$

という変換である。

factor packet がすべて不可能であるならば、factor packet を生成する元の zero-sector arithmetic data も存在できない。

## 証明全体での役割

0410 `goldenZeroSectorFactorExclusion` は、無限降下によって

```lean
GoldenZeroSectorFactorExclusion
```

を無条件に供給した。

0411 はその結果を、FLT5 closure 側が期待する公開 interface

```lean
GoldenZeroSectorArithmeticExclusion
```

へ戻す adapter である。

全体の流れは

$$
\mathrm{GoldenZeroSectorCandidate}
\longrightarrow
\text{strict infinite descent}
\longrightarrow
\mathrm{GoldenZeroSectorFactorExclusion}
\longrightarrow
\mathrm{GoldenZeroSectorArithmeticExclusion}
$$

となる。

ここで重要なのは、0411 自身が新しい無限降下や因数分解を行うのではないことである。

factorization module は raw arithmetic input から factor packet を構成する方法を既に持ち、その generic lifting theorem

```lean
goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion
```

が「factor packet を全排除できれば raw arithmetic input も全排除できる」ことを証明済みである。

0411 はその theorem を public closure contract に再公開している。

## 直接依存する定義・補題

### `GoldenZeroSectorFactorExclusion`

```lean
abbrev GoldenZeroSectorFactorExclusion : Prop :=
  GoldenZeroSectorFactorPacket → False
```

factorization 後の全 packet を否定する receiver である。

0411 では仮定 `hFactor` として受け取る。

### `GoldenZeroSectorFactorArithmeticExclusion`

factorization module 側で定義された raw arithmetic receiver。

`r, s, a, b` と、正値性、互いに素性、`5 ∤ b`、golden norm 条件、zero-sector product identity、座標の互いに素性、tenth-power split を受けて `False` を返す。

この contract は dependency graph を循環させずに factorization 層だけで使用できるよう、factorization 側に置かれている。

### `GoldenZeroSectorArithmeticExclusion`

closure 側で公開される zero-sector arithmetic receiver。

正本のコメント通り、`GoldenZeroSectorFactorArithmeticExclusion` と同じ arithmetic contract を表すように定義されている。

このため 0411 では追加の変換データを構築する必要がない。

### `goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion`

```lean
theorem goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorFactorArithmeticExclusion := by
  ...
```

0411 の実質的な証明本体である。

この先行 theorem は raw arithmetic data から `GoldenZeroSectorCandidate`、inversion packet、factor packet を構成し、最後に `hFactor` を適用して矛盾を得る。

従って 0411 は、この既存 generic lifting theorem を public 型へ接続する薄い wrapper である。

## 証明または構築の流れ

証明は term-style で一行である。

```lean
goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion hFactor
```

型の流れは

```lean
hFactor
  : GoldenZeroSectorFactorExclusion
```

から

```lean
goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion hFactor
  : GoldenZeroSectorFactorArithmeticExclusion
```

を得る。

そして正本では factorization 側の arithmetic contract と public な `GoldenZeroSectorArithmeticExclusion` が定義的に一致するため、その項をそのまま結論として返せる。

明示的な `change`、`simpa`、`exact`、`rw` は不要である。

## Lean 固有の処理

### 1. `abbrev` の definitional transparency

この theorem が一行で通る核心は、receiver proposition が `abbrev` として定義されている点にある。

Lean は必要に応じて reducible abbreviation を展開し、

```lean
GoldenZeroSectorFactorArithmeticExclusion
```

と

```lean
GoldenZeroSectorArithmeticExclusion
```

の underlying function type が一致することを確認できる。

従って explicit cast や equality proof は不要である。

### 2. tactic block を必要としない term proof

宣言は

```lean
:=
  goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion hFactor
```

という pure term で閉じている。

この形は「新しい証明をしている」のではなく「既存の theorem の結果型を public interface として再利用している」ことを非常に明瞭に表す。

### 3. dependency boundary の保持

同じ contract を二箇所で名前付けしているのは単なる重複ではない。

factorization module 側は closure module を import できないため、循環依存を避けるために local receiver を持つ。後段の closure module で 0411 が両者を接続する。

Lean の module dependency graph を acyclic に保つための設計である。

## 冗長・重複箇所

表面的には

```lean
GoldenZeroSectorFactorArithmeticExclusion
```

と

```lean
GoldenZeroSectorArithmeticExclusion
```

が同じ型を繰り返しているため、重複に見える。

しかし正本コメントでは、前者を factorization 側に再定義した理由が dependency direction を保つためと明示されている。

したがってこの重複は accidental duplication ではなく、module layering のための意図的な interface duplication と読むべきである。

0411 自身の proof body には冗長性はほぼない。

## 最適化候補

### 1. 現行一行 proof を維持する

すでに最小に近い。

例えば

```lean
by
  exact goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion hFactor
```

とも書けるが、現行 term-style の方が短く、意味も明瞭である。

### 2. receiver alias の共通化は慎重に行う

二つの arithmetic exclusion 型を一つの共通定義へ統合すれば文字列上の重複は減らせる。

しかし共通定義をどの module に置くかによって dependency direction が変わり、factorization と closure の import graph に影響する。

そのため、単純な DRY 化だけを目的に統合するのは推奨しにくい。

### 3. theorem 自体を削除しない

型が定義的に一致するなら 0411 は技術的には trivial wrapper である。

しかし public API 上は

```lean
goldenZeroSectorArithmeticExclusion_of_factorExclusion
```

という名前によって「factor-level exclusion から public arithmetic exclusion へ上げる」という設計意図が明示される。

従って documentation theorem として残す価値がある。

## 必要な Mathlib import

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

0411 の proof body 自体は Mathlib の tactic や theorem を直接利用しない。

直接必要なのは FLT5 内部の

- `GoldenZeroSectorFactorExclusion`
- `GoldenZeroSectorFactorArithmeticExclusion`
- `GoldenZeroSectorArithmeticExclusion`
- `goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion`

である。

### import 最適化候補

0411 単独では `import Mathlib` は明らかに広い。

概念上は、factorization receiver とその lifting theorem を提供する module、および public arithmetic receiver を定義する closure module があれば足りる。

ただし本解説では Lean build を実行していないため、実際にコンパイル可能な最小 import の正確な組合せは未確認である。

## Comparator challenge 化の可否

**可能だが、単独ではかなり低難度。**

challenge としては、二つの receiver alias が definitionally equal であることを Lean がどのように扱うかを見る題材になる。

例えば

```lean
abbrev A : Prop := P
abbrev B : Prop := P
axiom lift : H → A
```

に相当する最小 context を与え、

```lean
theorem bridge (h : H) : B := by
  ?_
```

を埋めさせる形である。

評価できるのは

- `abbrev` の transparency を理解しているか
- 不要な `simpa` や `change` を避けられるか
- module boundary 用 wrapper の意味を読めるか

である。

一方、数学的推論能力を測る Comparator challenge としては、先行する `goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion` の方がはるかに適している。

## 次に読むべき宣言

次は 0412

```lean
theorem goldenZeroSectorArithmeticExclusion :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorArithmeticExclusion_of_factorExclusion
    goldenZeroSectorFactorExclusion
```

である。

0410 が無条件の

```lean
GoldenZeroSectorFactorExclusion
```

を供給し、0411 がそれを public arithmetic receiver へ持ち上げる関数を与えた。

0412 は両者を実際に合成して

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
$$

そのものを仮定なしで確立する。

これにより、それ以前の closure 層で仮定として受け取っていた zero-sector arithmetic exclusion が完全に discharge され、FLT5 の unconditional endpoint へ進む準備が整う。
