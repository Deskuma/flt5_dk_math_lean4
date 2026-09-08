# 0347 — `goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion`

## 宣言種別

この宣言は **`theorem`** である。

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

## Lean の型

```lean
goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorFactorArithmeticExclusion
```

0345 の packet-level exclusion

```lean
GoldenZeroSectorFactorExclusion
```

すなわち

```lean
GoldenZeroSectorFactorPacket → False
```

を仮定すると、0346 の raw arithmetic contract

```lean
GoldenZeroSectorFactorArithmeticExclusion
```

が得られる。

0346 は `abbrev` なので、証明本体ではその全称・含意の連鎖が自動的に展開され、`intro` で raw data と仮定を直接受け取れる。

## 数学的主張

数学的には、certified factor packet を一つでも与えれば矛盾する、という排除原理が確立しているなら、zero-sector の raw arithmetic configuration もすべて排除できることを示す。

raw 側の入力は整数 $r,s$ と自然数 $a,b$、さらに

$$
0<a,\qquad 0<b,\qquad \gcd(a,b)=1,\qquad 5\nmid b,
$$

$$
\operatorname{goldenNorm}(r,s)=\pm b,
$$

$$
s\,\operatorname{goldenFifthSndFactor}(r,s)=-5^6a^{10},
$$

$$
\gcd(|r|,|s|)=1,
$$

およびある $c,d\in\mathbb N$ に対する

$$
|s|=5^6c^{10},
\qquad
|\operatorname{goldenFifthSndFactor}(r,s)|=d^{10}
$$

である。

この theorem はこれらを `GoldenZeroSectorCandidate` に再包装し、既に構築済みの inversion packet と factor packet の pipeline に通した後、`hFactor` を適用して `False` を得る。

## 証明全体での役割

この theorem は zero-sector factorization 層の **公開 bridge** である。

前段では raw arithmetic data から候補を構築でき、さらに

$$
\text{candidate}
\longrightarrow
\text{inversion packet}
\longrightarrow
\text{factor packet}
$$

という certified pipeline が完成している。一方、後段では raw arithmetic contract の形で排除結果を受け取りたい。

0347 はこの二つを

$$
\text{factor-packet exclusion}
\Longrightarrow
\text{raw arithmetic exclusion}
$$

として接続する。

したがって新しい数論を証明する定理ではなく、既に証明された構築を一方向に合成して dependency boundary を閉じる theorem である。

## 直接依存する定義・補題

直接参照するプロジェクト宣言は次である。

- `GoldenZeroSectorFactorExclusion`
- `GoldenZeroSectorFactorArithmeticExclusion`
- `goldenZeroSectorCandidate_of_raw`
- `goldenZeroSectorInversionPacket`
- `goldenZeroSectorFactorPacket_of_inversion`

特に依存の流れは

```text
goldenZeroSectorCandidate_of_raw
  → goldenZeroSectorInversionPacket
  → goldenZeroSectorFactorPacket_of_inversion
  → hFactor
```

である。

0346 の contract 内部に現れる `goldenNorm`、`goldenFifthSndFactor`、`Nat.Coprime`、`Int.natAbs` などは型を展開した結果として関係するが、証明スクリプト中では個別の算術補題を呼ばない。

## 証明の流れ

1. `intro` で raw arithmetic contract のすべての変数・仮定を受け取る。
2. `hsplit` を `rcases` し、10 乗分解 witness `c,d` と等式 `hsAbs`, `hHAbs` を取り出す。
3. `goldenZeroSectorCandidate_of_raw` に全データを渡して `source : GoldenZeroSectorCandidate` を構築する。
4. `goldenZeroSectorInversionPacket source` で inversion certificate を得る。
5. `goldenZeroSectorFactorPacket_of_inversion` で certified exact factor packet を得る。
6. `hFactor` をその packet に適用して `False` を得る。

証明の核心は一行で表せば

```lean
hFactor (goldenZeroSectorFactorPacket_of_inversion
  (goldenZeroSectorInversionPacket source))
```

である。

## Lean 固有の処理

### `abbrev` の透明性

返り値の `GoldenZeroSectorFactorArithmeticExclusion` は `abbrev` なので、

```lean
intro r s a b ...
```

が直接使える。`unfold` は不要である。

### existential package の `rcases`

0346 の最後の仮定は

```lean
∃ c d : ℕ,
  s.natAbs = 5 ^ 6 * c ^ 10 ∧
  (goldenFifthSndFactor r s).natAbs = d ^ 10
```

なので、

```lean
rcases hsplit with ⟨c, d, hsAbs, hHAbs⟩
```

によって constructor が要求する witness と証明を一度に取り出す。

### `let source := ...`

長い constructor application を局所名 `source` に束ねている。これにより後半の dependent packet chain が読みやすくなり、raw data を再列挙せずに済む。

### proof-carrying data の合成

`goldenZeroSectorInversionPacket source` と `goldenZeroSectorFactorPacket_of_inversion ...` は単なる命題変形ではなく、証明を fields に持つ structure を順に構築する。Lean の型検査により、factor packet が同じ source に由来する inversion packet と整合していることが保証される。

## 冗長・重複箇所

この theorem 自体には数学的な重複証明はほとんどない。

raw assumptions を `intro` した直後に同じ情報を `goldenZeroSectorCandidate_of_raw` へすべて渡しているため引数列は長いが、これは 0346 が dependency cycle を避けるため raw contract を再掲している設計の帰結である。

また

```lean
let source := ...
exact hFactor (... source ...)
```

は `let` を使わず一式にインライン化できる。しかし constructor 引数が長くなるため、現行形の方が可読性は高い。

## 最適化候補

最適化余地は主に API ergonomics にある。

raw assumptions を将来 dependency-neutral な structure にまとめられるなら、`intro` と constructor application の長い引数列を短縮できる。ただし 0346 の解説で述べた通り、structure の配置を誤ると現在避けている module dependency cycle を再導入し得るため、単純なリファクタリングではない。

局所的には、この theorem は既に最短に近い。`simpa` や追加の rewrite は不要であり、packet pipeline を直接合成している点は良い。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

この theorem の証明スクリプト自体で必要なのは基本的な tactic / elaboration 機能である。

- `intro`
- `rcases`
- `let`
- structure / function application
- `False`

算術処理は前段 API 内に封じ込められており、この theorem 単体では `ring`, `omega`, `norm_num` などを使用しない。

プロジェクト定義を提供する module の import が大部分を transitively 供給すると考えられる。Lean ビルドは今回行っていないため、具体的な最小 Mathlib import 名は未確認であり断定しない。

## Comparator challenge 化の可否

**非常に適している。**

0346 の raw contract を理解した後の橋渡し問題として、次の形が良い。

```lean
example
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorFactorArithmeticExclusion := by
  -- raw assumptions を intro
  -- power split witness を rcases
  -- raw candidate を構築
  -- inversion → factor packet → False
```

問える能力は

- reducible contract の展開理解
- long implication chain の導入
- existential destructuring
- proof-carrying structure construction
- API composition

であり、数論そのものではなく Lean における証明アーキテクチャの理解を測る Comparator challenge になる。

## 次に読むべき宣言

次は

```lean
/-- The factor-packet receiver has exactly the public zero-sector contract. -/
theorem goldenZeroSectorArithmeticExclusion_of_factorExclusion
    (hFactor : GoldenZeroSectorFactorExclusion) :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorFactorArithmeticExclusion_of_factorExclusion hFactor
```

である。

0347 が構築した factorization-module 側の raw arithmetic exclusion を、公開 contract `GoldenZeroSectorArithmeticExclusion` と定義的に同一視して返す薄い adapter theorem である。ここで factor-packet exclusion が public zero-sector closure API に接続される。
