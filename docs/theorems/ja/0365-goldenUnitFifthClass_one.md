# 0365 — `goldenUnitFifthClass_one`

## 宣言種別

この宣言は **`private theorem`** である。

```lean
private theorem goldenUnitFifthClass_one : GoldenUnitFifthClass goldenOne := by
  refine ⟨⟨0, by decide⟩, goldenOne, ?_⟩
  decide
```

`GoldenUnitFifthClass` という five-sector 分類に、乗法単位元 `goldenOne` が属することを具体的 witness で証明する基底補題である。

## Lean の型

```lean
goldenUnitFifthClass_one :
  GoldenUnitFifthClass goldenOne
```

ただし `private theorem` なので、この名前はモジュール外へ公開する API ではなく、後続の unit-classification 証明の内部部品として使われる。

`GoldenUnitFifthClass` の定義は

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

である。本補題は `x = goldenOne` に対して

```lean
i     = 0
delta = goldenOne
```

を選ぶ。

## 数学的主張

数学的には極めて直接的で、

$$
1 = \varphi^0 \cdot 1^5
$$

を示している。

したがって `goldenOne` は fifth powers を法とする five-sector の sector `0` に属する。

指数側では

$$
0 \in \mathbf Z/5\mathbf Z
$$

という自明な class を concrete `Fin 5` witness として登録していると読める。

## 証明全体での役割

0359 `goldenUnit_descent` は measure が 1 より大きい golden unit をより小さい golden unit へ降下させる。一方、降下を strong induction で閉じるには、measure が最小値 `1` に到達した場合を処理しなければならない。

0356 `goldenUnit_measure_one_cases` は measure `1` の unit を

$$
\{1,-1,\varphi,-\varphi\}
$$

の四つに分類する。

後続 `goldenUnitFifthClass_of_unit` は、この四分岐それぞれについて fifth class membership を必要とする。本補題はその最初のケース

$$
x=1
$$

を担当する。

正本では後続 strong-induction の基底枝で

```lean
simpa [h] using goldenUnitFifthClass_one
```

という形で直接利用される。

したがって本補題は数学的には小さいが、strict descent を有限の基底ケースで閉じるための必要な leaf theorem である。

## 直接依存する定義・補題

プロジェクト内で直接関係するものは主に次である。

- `GoldenInt` — 黄金整数の型。
- `goldenOne` — 黄金整数環の乗法単位元。
- `goldenPhi` — sector の生成元として使われる黄金比 unit。
- `goldenMul` — `GoldenUnitFifthClass` の定義中で使われる乗法。
- `goldenPow` — `GoldenUnitFifthClass` の定義中で使われる冪。
- `GoldenUnitFifthClass` — `x = φ^i δ^5`, `i : Fin 5` を表す predicate。

証明本文から直接呼ばれる既存 theorem はない。証明は existential witness を具体化した後、閉じた等式を `decide` で認証するだけである。

Lean / Mathlib 側では主に次を使う。

- `refine`
- `Fin 5`
- `decide`
- existential / conjunction constructor syntax `⟨...⟩`

## 証明の流れ

### 1. sector witness と fifth-power witness を与える

```lean
refine ⟨⟨0, by decide⟩, goldenOne, ?_⟩
```

によって `GoldenUnitFifthClass goldenOne` の二つの存在量化 witness を同時に与える。

最初の

```lean
⟨0, by decide⟩ : Fin 5
```

は sector `0` を表す。`Fin 5` では値だけでなく `0 < 5` の証明も必要なので、閉じた算術命題を `decide` に任せている。

二つ目の witness は

```lean
goldenOne : GoldenInt
```

であり、これは fifth-power base `delta` に対応する。

この時点で残る目標は実質的に

$$
1 = \varphi^0 1^5
$$

という concrete equality だけになる。

### 2. concrete equality を計算で閉じる

```lean
decide
```

で残りの等式を閉じる。

ここでは変数も仮定も残っていないため、`GoldenInt` の具体的な equality が decidable であることを利用して kernel-checkable な計算結果を生成する。

## Lean 固有の処理

### `⟨0, by decide⟩ : Fin 5`

数学では単に「指数 0」と書けばよいが、Lean の `Fin 5` は値と範囲証明を持つ型である。

したがって

```lean
⟨0, proof that 0 < 5⟩
```

という構築が必要になる。ここでは範囲証明が閉じた命題なので `by decide` が最短である。

### 最後の `decide`

この証明では `simp`, `ring`, `norm_num` を使わず、完全具体化された equality の decision procedure に任せている。

これは 0361 `golden_phi_four_mul_inv_five` と同様、対象が concrete data にまで落ちているから可能な書き方である。

## 冗長・重複箇所

本補題単体にはほとんど冗長性がない。二行の proof term で目的を直接構成している。

ただし周辺には、measure `1` の四つの unit

$$
1,-1,\varphi,-\varphi
$$

それぞれについて類似した private theorem が続く。そのため「四つの concrete base case」という意味では構造的重複が存在する。

この重複は、各 unit がどの sector と fifth-power witness に属するかを明示するという利点がある。

## 最適化候補

1. **現状維持** — 本補題はすでにほぼ最小で、可読性も高い。
2. **`simp` による表現** — `GoldenUnitFifthClass`, `goldenOne`, `goldenPow` 等に十分な simp lemma があれば `simp [GoldenUnitFifthClass]` に近い形へ縮められる可能性がある。ただし実際に成立する最小形は Lean ビルドを行っていないため未確認である。
3. **四基底ケースのまとめ** — `1,-1,φ,-φ` の membership を一つの finite-case theorem にまとめる設計は可能だが、後続 strong induction では個別 theorem の方が `simpa [h] using ...` と直接接続しやすい。
4. **公開 API 化は不要** — 本補題は proof-local な基底ケースであり、`private` は自然な設計である。外部 API に昇格させる積極的理由は現時点では見当たらない。

## 必要 Mathlib import と import 最適化候補

standalone `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本補題単体が直接必要とする Mathlib 機能は非常に小さく、主として

- `Fin`
- `Decidable`
- `decide`
- 基本的な existential construction

である。

ただし `GoldenInt`, `goldenOne`, `goldenPow`, `GoldenUnitFifthClass` の定義側が要求する import を含める必要があるため、元モジュール全体の厳密な最小 import はこの二行だけからは決められない。

Lean ビルドは禁止されているため、具体的な最小 import 集合は未確認である。

## Comparator challenge 化の可否

**可能。難度は非常に低い micro challenge 向き** である。

例えば challenge は次の形にできる。

```lean
example : GoldenUnitFifthClass goldenOne := by
  -- fill proof
```

必要な発想は二つだけである。

1. sector witness として `0 : Fin 5` を選ぶ。
2. fifth-power witness として `goldenOne` を選ぶ。

その後の equality は concrete computation で閉じられる。

大規模 FLT5 文脈を切り離して Comparator の「existential witness construction」「`Fin` witness」「decidable concrete equality」の最小テストにするには適している。一方、数学的推論能力を測る challenge としては簡単すぎる。

## 次に読むべき宣言

次は **0366 `goldenUnitFifthClass_neg_one`**、種別は **`private theorem`** である。

正本では直後に

```lean
private theorem goldenUnitFifthClass_neg_one :
    GoldenUnitFifthClass (-goldenOne) := by
  ...
```

が続く。

これは measure `1` の第二の基底 unit `-1` を five-sector 表現へ登録する補題である。0365〜0368 で `1,-1,φ,-φ` の四基底を揃えた後、それらが `goldenUnitFifthClass_of_unit` の strong-induction base case に投入される。
