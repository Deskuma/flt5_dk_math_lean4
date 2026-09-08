# 0346 — `GoldenZeroSectorFactorArithmeticExclusion`

## 宣言種別

この宣言は **`abbrev`** である。

```lean
/-- The raw arithmetic contract, repeated here to preserve the acyclic dependency
 direction from inversion to factorization. -/
abbrev GoldenZeroSectorFactorArithmeticExclusion : Prop :=
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

`theorem` や `def` ではなく、raw zero-sector arithmetic data から矛盾を導く命題型に短い名前を与える reducible な省略定義である。

## Lean の型

宣言そのものの型は

```lean
GoldenZeroSectorFactorArithmeticExclusion : Prop
```

である。

展開すると、任意の

```lean
r s : ℤ

a b : ℕ
```

に対し、正性・互いに素性・5 非可除性・golden norm 条件・積の恒等式・座標の互いに素性・10 乗分解条件をすべて仮定したなら `False` が従う、という全称命題になる。

したがって

```lean
h : GoldenZeroSectorFactorArithmeticExclusion
```

は、raw arithmetic candidate の全データと仮定を順に受け取り、最終的に矛盾を返す関数として使える。

## 数学的意味

この contract は、zero-sector factorization の前段で現れる算術データを packet に包まず、そのまま引数として並べた排除命題である。

仮定は次の構造を持つ。

まず自然数側で

$$
0<a,\qquad 0<b,\qquad \gcd(a,b)=1,\qquad 5\nmid b
$$

を要求する。

次に golden norm が符号を除いて $b$ に一致すること、すなわち

$$
\operatorname{goldenNorm}(r,s)=b
\quad\text{または}\quad
\operatorname{goldenNorm}(r,s)=-b
$$

を要求する。

さらに signed fifth-power factorization の積恒等式

$$
s\,\operatorname{goldenFifthSndFactor}(r,s)
=-5^6 a^{10}
$$

と、座標の primitive 条件

$$
\gcd(|r|,|s|)=1
$$

を要求する。

最後に zero-sector 由来の 10 乗分解

$$
|s|=5^6c^{10},
\qquad
|\operatorname{goldenFifthSndFactor}(r,s)|=d^{10}
$$

を満たす $c,d\in\mathbb N$ が存在すると仮定する。

これらすべてが同時に成立する raw arithmetic configuration は存在しない、というのがこの命題の内容である。

## 証明全体での役割

0345 `GoldenZeroSectorFactorExclusion` は

```lean
GoldenZeroSectorFactorPacket → False
```

という、certified factor packet を直接排除する最も圧縮された contract だった。

0346 はそれを raw arithmetic interface の形に展開するための受け口である。

つまり証明層は概念的に

$$
\text{raw arithmetic data}
\longrightarrow
\text{candidate}
\longrightarrow
\text{inversion packet}
\longrightarrow
\text{factor packet}
\longrightarrow
\bot
$$

という流れを持つ。

この `abbrev` 自体はまだその変換を実行しない。次の theorem `goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion` が、0345 の packet-level exclusion から今回の raw arithmetic exclusion を実際に構築する。

したがって 0346 は、factorization 層で得られた排除結果を、上位の zero-sector closure 層が利用できる形へ戻すための **算術 API 境界** である。

## 直接依存する定義・補題

この `abbrev` の右辺が直接参照するプロジェクト定義は主に次である。

- `goldenNorm`
- `goldenFifthSndFactor`

また Lean / Mathlib 側では

- `ℤ`, `ℕ`
- `Nat.Coprime`
- `Int.natAbs`
- divisibility `∣`
- existential quantifier `∃`
- conjunction `∧`
- disjunction `∨`
- `False`

を使用する。

一方、0345 `GoldenZeroSectorFactorExclusion`、`GoldenZeroSectorCandidate`、`GoldenZeroSectorInversionPacket`、`GoldenZeroSectorFactorPacket` はこの `abbrev` の定義本体からは直接参照されない。それらは次の bridge theorem が raw contract を実装するときに登場する。

## 構築の流れ

この宣言には tactic proof は存在しない。命題型をそのまま定義しているだけである。

構造を分解すると次の順序になる。

1. 任意の整数座標 `r s` と自然数パラメータ `a b` を取る。
2. `a,b` の正性を仮定する。
3. `a,b` が互いに素であることを仮定する。
4. `5 ∤ b` を仮定する。
5. golden norm が `±b` であることを仮定する。
6. signed product identity を仮定する。
7. `r.natAbs` と `s.natAbs` の互いに素性を仮定する。
8. `s` と second factor の絶対値が指定された 10 乗形に分解することを仮定する。
9. そこから `False` が従う、という contract を定義する。

重要なのは、最後の existential assumption が

```lean
∃ c d : ℕ,
  s.natAbs = 5 ^ 6 * c ^ 10 ∧
  (goldenFifthSndFactor r s).natAbs = d ^ 10
```

という形で一つにまとめられている点である。後続 theorem ではこれを `rcases` して `c,d` と二つの等式を取り出し、そのまま `goldenZeroSectorCandidate_of_raw` の constructor 入力へ渡す。

## Lean 固有の処理

### `abbrev` による contract の透明化

0345 と同じく `abbrev` なので、Lean は必要に応じてこの名前を右辺の全称関数型へ容易に展開する。

そのため次の theorem では

```lean
intro r s a b ha hb hab h5b hNorm hProduct hrs hsplit
```

と直接 `intro` できる。明示的な `unfold GoldenZeroSectorFactorArithmeticExclusion` は不要である。

### `ℤ` と `ℕ` の混在

`r,s` は整数、`a,b,c,d` は自然数である。

そのため norm 条件では

```lean
(b : ℤ)
```

という cast が必要になる一方、絶対値側では

```lean
r.natAbs
s.natAbs
```

によって自然数へ戻して `Nat.Coprime` やべき乗分解を扱う。

この整数・自然数境界は zero-sector factorization 全体で重要な Lean 上の bookkeeping である。

### 負号とべき乗の構文

積条件

```lean
s * goldenFifthSndFactor r s = -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10
```

では `5` と `a` を明示的に `ℤ` へ cast している。

また `-(5 : ℤ) ^ 6` は Lean の構文上 `-((5 : ℤ) ^ 6)` と読まれる。指数が偶数なので数値的には `-15625` であり、積全体の signed orientation を保持している。

### `natAbs`

整数の絶対値を自然数として返す `Int.natAbs` を使うことで、10 乗分解や自然数上の coprimality をそのまま扱える。

これは整数上の `abs` を使ってから cast するよりも、後続の `Nat` API と接続しやすい。

## 冗長・重複箇所

この contract は意図的に raw arithmetic assumptions を再列挙しているため、見た目には `GoldenZeroSectorCandidate` の fields と重複する。

特に

- `0 < a`
- `0 < b`
- `Nat.Coprime a b`
- `¬ 5 ∣ b`
- norm equality up to sign
- product equality
- coordinate coprimality
- `s` と second factor の power decomposition

は candidate constructor が保持する情報とほぼ対応する。

しかし source comment にある通り、これは依存方向を

$$
\text{inversion}\to\text{factorization}
$$

の向きに保ち、循環依存を避けるために raw contract をこの module 側へ再掲している設計である。

したがって単純な重複削除で candidate 型そのものを contract の引数にすると、module dependency graph を壊す可能性がある。ここはコード行数だけでは冗長と判断できない。

## 最適化候補

最も自然な最適化候補は raw assumptions を補助 structure にまとめることである。例えば

```lean
structure GoldenZeroSectorRawArithmeticData where
  r s : ℤ
  a b : ℕ
  ...
```

としてから

```lean
GoldenZeroSectorRawArithmeticData → False
```

とすれば contract は短くなる。

ただし、その structure をどの module に置くかによっては、現行コードが避けている dependency cycle を再導入する危険がある。よってこれは module graph を確認せずには推奨できない。

局所的には、現在の引数順は次の bridge theorem の `intro` と `goldenZeroSectorCandidate_of_raw` の constructor 順に一致しており、実装上かなり合理的である。

また最後の

```lean
(∃ c d : ℕ, P c ∧ Q d) → False
```

を

```lean
∀ c d : ℕ, P c → Q d → False
```

へ変形する案もあるが、前段から得られる情報が existential package なら現行形の方が自然である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は全体として

```lean
import Mathlib
```

を使用している。

本宣言単体で必要となる Mathlib 機能は、概ね

- integers / naturals
- `Nat.Coprime`
- `Int.natAbs`
- divisibility
- powers

である。

ただし `goldenNorm` と `goldenFifthSndFactor` を提供するプロジェクト側 module が既に必要 import を transitively 提供している可能性が高い。

そのため実際の module-level 最小 import は、これら二つの定義を提供する module の依存関係を見て決めるべきである。

Lean ビルドは今回行っていないため、具体的な最小 Mathlib import 名は未確認であり断定しない。

## Comparator challenge 化の可否

**可能であり、0345 より良い中級 challenge にできる。**

単純な型再現問題なら、次の raw contract の穴埋めを課せる。

```lean
abbrev Challenge : Prop :=
  ∀ (r s : ℤ) (a b : ℕ),
    0 < a →
    0 < b →
    Nat.Coprime a b →
    ¬ 5 ∣ b →
    ... →
    False
```

ただし本質的な Comparator challenge は次の bridge theorem の方である。

```lean
variable
  (hFactor : GoldenZeroSectorFactorExclusion)

example : GoldenZeroSectorFactorArithmeticExclusion := by
  -- raw assumptions を受け取り candidate を構築し、
  -- inversion packet → factor packet → contradiction へ接続する
```

これなら

- long implication chain の `intro`
- existential の `rcases`
- `let` による candidate construction
- dependent packet pipeline
- exclusion contract の適用

を一度に問えるため、Lean proof engineering の教材として価値が高い。

## 次に読むべき宣言

次は

```lean
/-- Excluding the three exact factor packets excludes every original zero-sector
candidate.  `SignedGoldenClosure` identifies this contract definitionally with its
public zero-sector arithmetic exclusion. -/
theorem goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorFactorArithmeticExclusion := by
  intro r s a b ha hb hab h5b hNorm hProduct hrs hsplit
  rcases hsplit with ⟨c, d, hsAbs, hHAbs⟩
  let source := goldenZeroSectorCandidate_of_raw r s a b
    ha hb hab h5b hNorm hProduct hrs c d hsAbs hHAbs
  exact hFactor (goldenZeroSectorFactorPacket_of_inversion
    (goldenZeroSectorInversionPacket source))
```

である。

宣言種別は **`theorem`**。

0346 が raw arithmetic exclusion の「型」を定義したのに対し、次の宣言は 0345 `GoldenZeroSectorFactorExclusion` を仮定してその型を実際に inhabit する bridge theorem である。

ここで初めて

$$
\text{raw arithmetic assumptions}
\to
\text{candidate}
\to
\text{inversion packet}
\to
\text{factor packet}
\to
\bot
$$

という pipeline が一行の証明として閉じる。
