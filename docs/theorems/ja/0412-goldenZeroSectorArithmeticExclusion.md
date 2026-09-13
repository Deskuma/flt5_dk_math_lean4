# 0412 `goldenZeroSectorArithmeticExclusion`

## 宣言種別

`theorem`

## Lean の型

```lean
theorem goldenZeroSectorArithmeticExclusion :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorArithmeticExclusion_of_factorExclusion
    goldenZeroSectorFactorExclusion
```

この theorem は、zero-sector の公開算術 exclusion contract

```lean
GoldenZeroSectorArithmeticExclusion
```

を仮定なしで構成する。

直前の 0410 `goldenZeroSectorFactorExclusion` が factor packet を無条件に排除し、0411 `goldenZeroSectorArithmeticExclusion_of_factorExclusion` がその factor-level exclusion を公開 arithmetic contract へ持ち上げる。0412 はこの二つを直接合成して、zero-sector closure に残っていた最後の算術仮定を消す宣言である。

## 数学的主張

`GoldenZeroSectorArithmeticExclusion` は、整数座標 `r, s` と正整数 `a, b` が、zero-sector から導かれる primitive 条件・ノルム条件・積恒等式・tenth-power split を同時に満たす状況を排除する命題である。

正本では次の形で定義されている。

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

従って 0412 の数学的内容は、上の条件を満たす quadruple `(r,s,a,b)` は存在しない、という無条件の排除である。

構造だけを書けば、

$$
\mathrm{GoldenZeroSectorFactorExclusion}
\Longrightarrow
\mathrm{GoldenZeroSectorArithmeticExclusion}
$$

を 0411 が与え、0410 が左辺を無条件に証明するので、

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
$$

が得られる。

## 証明全体での役割

この宣言は `SignedGoldenZeroSectorFinal` モジュールの到達点である。

zero-sector の証明経路は概略、

$$
\text{zero-sector arithmetic data}
\longrightarrow
\text{candidate}
\longrightarrow
\text{inversion packet}
\longrightarrow
\text{factor packet}
\longrightarrow
\text{descent packet}
\longrightarrow
\bot
$$

と進む。

0410 は、この下流の strict infinite descent を利用して factor packet receiver を無条件化した。

0411 は factor packet receiver から source-level arithmetic receiver への adapter を与えた。

0412 はその二つを合成し、`SignedGoldenClosure` が条件付きで要求していた

```lean
GoldenZeroSectorArithmeticExclusion
```

を実データとして供給する。

これにより、以後の final FLT5 closure では zero-sector arithmetic exclusion を外部仮定として受け取る必要がなくなる。

## 直接依存する定義・補題

### `GoldenZeroSectorArithmeticExclusion`

`SignedGoldenClosure` で公開される `abbrev : Prop`。

zero-sector の raw arithmetic data がすべて矛盾することを表す receiver contract である。

0412 の返り値そのものである。

### `goldenZeroSectorFactorExclusion`

```lean
theorem goldenZeroSectorFactorExclusion :
    GoldenZeroSectorFactorExclusion := by
  intro packet
  exact goldenZeroSectorCandidate_false packet.inversion.source
```

0410 で扱った theorem。

strict infinite descent で既に証明された

```lean
goldenZeroSectorCandidate_false
```

を factor packet 内に保持された provenance `packet.inversion.source` に適用し、すべての factor packet を無条件に否定する。

### `goldenZeroSectorArithmeticExclusion_of_factorExclusion`

```lean
theorem goldenZeroSectorArithmeticExclusion_of_factorExclusion
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion hFactor
```

0411 で扱った theorem。

factorization 層の exclusion receiver を closure 層の public arithmetic receiver に変換する adapter である。

0412 の証明本体は、この theorem に 0410 を代入するだけである。

## 証明または構築の流れ

証明は pure term-style の二段適用である。

```lean
goldenZeroSectorArithmeticExclusion_of_factorExclusion
  goldenZeroSectorFactorExclusion
```

Lean が見る型は次の通りである。

```lean
goldenZeroSectorArithmeticExclusion_of_factorExclusion
  : GoldenZeroSectorFactorExclusion →
      GoldenZeroSectorArithmeticExclusion
```

および

```lean
goldenZeroSectorFactorExclusion
  : GoldenZeroSectorFactorExclusion
```

なので、関数適用により直ちに

```lean
goldenZeroSectorArithmeticExclusion_of_factorExclusion
  goldenZeroSectorFactorExclusion
  : GoldenZeroSectorArithmeticExclusion
```

を得る。

新しい witness の構築、場合分け、書き換え、算術 tactic は一切ない。

## Lean 固有の処理

### 1. theorem を proposition の値として合成する

Lean では theorem はその型の項である。

従って

```lean
goldenZeroSectorFactorExclusion
```

は単なる「定理名」ではなく、型

```lean
GoldenZeroSectorFactorExclusion
```

を持つ証明項として、そのまま関数に渡せる。

0412 は Curry–Howard 対応が最も直接的に見える形の theorem である。

### 2. tactic block が不要

証明は

```lean
:=
  goldenZeroSectorArithmeticExclusion_of_factorExclusion
    goldenZeroSectorFactorExclusion
```

だけで閉じる。

`exact`、`apply`、`simpa`、`change` は不要である。

同じ証明を tactic-style で書けば、例えば

```lean
by
  exact goldenZeroSectorArithmeticExclusion_of_factorExclusion
    goldenZeroSectorFactorExclusion
```

とも書けるが、現行の term-style の方が依存関係を最も明瞭に表す。

### 3. `abbrev` の透過性は 0411 側で処理済み

0412 自身は `GoldenZeroSectorFactorExclusion` と `GoldenZeroSectorArithmeticExclusion` の内部構造を展開しない。

factorization 側 contract と public closure contract の definitional compatibility は 0411 の型検査時に既に吸収されている。

従って 0412 は module boundary の型変換の詳細から完全に独立している。

## 冗長・重複箇所

コード量だけを見ると、0412 は 0410 と 0411 の単純合成であり、インライン化可能である。

例えば後続コードから直接

```lean
goldenZeroSectorArithmeticExclusion_of_factorExclusion
  goldenZeroSectorFactorExclusion
```

を使えば同じ証明項を得られる。

しかし宣言を独立して残す意味は大きい。

1. `GoldenZeroSectorArithmeticExclusion` の無条件実装が一つの名前で参照できる。
2. downstream の closure theorem が descent / factorization の詳細を知らずに済む。
3. conditional receiver と unconditional provider の境界が明確になる。
4. proof dependency graph の監査が容易になる。

従ってこれは論理的重複というより API finalization のための薄い named theorem と見るのが適切である。

## 最適化候補

### 1. 現行の term-style を維持する

この theorem 自体については、現行形がほぼ最小である。

```lean
theorem goldenZeroSectorArithmeticExclusion :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorArithmeticExclusion_of_factorExclusion
    goldenZeroSectorFactorExclusion
```

これ以上の短縮は可読性をほとんど改善しない。

### 2. provider 命名の統一

将来的に receiver/provider architecture をさらに明示するなら、

```lean
...Exclusion_of_factorExclusion
```

と無条件 provider

```lean
goldenZeroSectorArithmeticExclusion
```

の命名規約を他の closure 境界にも揃える余地がある。

これは機能上の最適化ではなく API 一貫性の改善である。

### 3. 0410–0412 を一 theorem に統合しない

機械的な行数削減だけなら統合可能だが、推奨しにくい。

0410 は descent 結果、0411 は interface adapter、0412 は unconditional provider と責務が明確に分離されている。この分離は Comparator challenge 化や theorem 単位の監査にも有利である。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

0412 自身の proof term は既存 theorem の関数適用だけであり、新しい tactic や Mathlib theorem を直接呼ばない。

従って 0412 単独の追加 import 要求は実質的にない。実際に必要な import は、次の宣言を提供するモジュールに由来する。

```lean
GoldenZeroSectorArithmeticExclusion
goldenZeroSectorFactorExclusion
goldenZeroSectorArithmeticExclusion_of_factorExclusion
```

モジュール構成上は `SignedGoldenClosure`、`SignedGoldenZeroSectorFactorization`、`SignedGoldenZeroSectorDescent` と、それらを束ねる `SignedGoldenZeroSectorFinal` の依存が中心になる。

ただし最小 import 集合を Lean build で検証してはいないため、どこまで `Mathlib` umbrella import を縮小できるかは未確認である。

## Comparator challenge 化の可否

### 単独 challenge

可能だが、難度は非常に低い。

前提として

```lean
hFactor : GoldenZeroSectorFactorExclusion
```

ではなく、既に無条件 theorem

```lean
goldenZeroSectorFactorExclusion
```

と adapter

```lean
goldenZeroSectorArithmeticExclusion_of_factorExclusion
```

が環境に存在すれば、解答は一度の関数適用で終了する。

そのため theorem 単独では Comparator の推論能力評価には弱い。

### より有用な challenge

0410–0412 をまとめ、

- factor packet が candidate source を保持すること
- candidate が strict infinite descent で矛盾すること
- factor exclusion から arithmetic exclusion を lift できること

を必要最小限の補題だけ与えて最終

```lean
GoldenZeroSectorArithmeticExclusion
```

を構築させる形なら、proof graph の再構成能力を測る challenge になる。

特に「新しい算術を証明する」のではなく、「既存の層を正しい順番で合成して公開 contract を閉じる」問題として適している。

## 次に読むべき宣言

次は `Valuation.lean` に入り、

```lean
theorem padicValNat_lower_bound_d5
    {x q : ℕ}
    (hx : 0 < x)
    (hq : Nat.Prime q)
    (hqx : q ∣ x) :
    5 ≤ padicValNat q (x ^ 5) := by
  ...
```

を読むべきである。

0412 までで zero-sector の無条件 closure は完了する。次の宣言は別モジュールの独立な valuation route に移り、素数 `q` が正整数 `x` を割るなら第五冪 `x^5` における `q`-進付値は少なくとも 5 であることを証明する。

数学的には

$$
q \mid x
\Longrightarrow
v_q(x) \ge 1
\Longrightarrow
v_q(x^5)=5v_q(x)\ge5
$$

という基本的な第五冪の付値下界であり、後の clean-channel contradiction の下側評価を担当する。
