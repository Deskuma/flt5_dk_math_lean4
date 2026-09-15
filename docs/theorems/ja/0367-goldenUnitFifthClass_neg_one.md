# 0367 — `goldenUnitFifthClass_neg_one`

## 宣言種別

この宣言は **`private theorem`** である。

```lean
private theorem goldenUnitFifthClass_neg_one :
    GoldenUnitFifthClass (-goldenOne) := by
  refine ⟨⟨0, by decide⟩, -goldenOne, ?_⟩
  decide
```

## Lean の型

概念的な型は次である。

```lean
goldenUnitFifthClass_neg_one :
  GoldenUnitFifthClass (-goldenOne)
```

`GoldenUnitFifthClass` は直前の unit-class 層で

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

と定義されている。したがって本定理は、黄金整数 `-goldenOne` が五つの代表 sector のいずれかに属することを、具体的 witness まで与えて示す。

## 数学的主張

本定理が選ぶ witness は

$$
i=0,
\qquad
\delta=-1
$$

である。

したがって主張は単純に

$$
-1
=\varphi^0(-1)^5
=1\cdot(-1)
=-1
$$

という恒等式である。

指数 5 が奇数なので負号を独立した unit representative として残す必要がなく、fifth-power witness 側へ吸収できる。すなわち、unit class を

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

の五つだけで表せる理由の最小の具体例が `-1` である。

## 証明全体での役割

0356 `goldenUnit_measure_one_cases` は measure 1 の golden unit を

$$
1,\;-1,\;\varphi,\;-\varphi
$$

の四つに分類する。

後続 `goldenUnitFifthClass_of_unit` は `goldenUnitMeasure` による strong induction で任意の golden unit を fifth class に分類する。その基底部分で measure 1 の四候補を処理するため、個別に

- `goldenUnitFifthClass_one`
- `goldenUnitFifthClass_neg_one`
- `goldenUnitFifthClass_phi`
- `goldenUnitFifthClass_neg_phi`

が用意されている。

本定理はそのうち `-1` の枝を閉じる。Lean 正本では `goldenUnitFifthClass_of_unit` 内で

```lean
simpa [h] using goldenUnitFifthClass_neg_one
```

という形で直接使われる。

したがって内容自体は小さいが、strict descent の strong induction を measure 1 で閉じるための基底証明の一つである。

## 直接依存する定義・補題

プロジェクト側で直接関係する主な宣言は次である。

- `GoldenInt` — 黄金整数を表す型。
- `goldenOne` — 黄金整数における明示的な 1。
- `goldenPhi` — 黄金比 unit `φ`。
- `goldenMul` — 黄金整数の乗法。
- `goldenPow` — 黄金整数の冪。
- `GoldenUnitFifthClass` — `x = φ^i δ^5`, `i : Fin 5` という five-sector predicate。

証明本文では他の project theorem を rewrite していない。`GoldenUnitFifthClass` の existential witness を直接構成し、残った閉じた等式を計算で認証している。

後続で本定理を直接消費するのは `goldenUnitFifthClass_of_unit` である。

## 証明・構築の流れ

### 1. sector 0 を選ぶ

```lean
refine ⟨⟨0, by decide⟩, -goldenOne, ?_⟩
```

ここで `GoldenUnitFifthClass (-goldenOne)` の二つの existential witness を同時に与える。

第一 witness は

```lean
⟨0, by decide⟩ : Fin 5
```

であり、sector `0` を選ぶ。`Fin 5` の値には `0 < 5` の証明が必要だが、閉じた数値命題なので `decide` で処理される。

第二 witness は

```lean
-goldenOne : GoldenInt
```

である。

これにより残るゴールは概念的には

$$
-1=\varphi^0(-1)^5
$$

だけになる。

### 2. 具体等式を計算で閉じる

```lean
decide
```

で残った等式を閉じる。

`goldenOne`, `goldenPhi`, `goldenMul`, `goldenPow` が具体的な計算可能データとして与えられているため、この閉じた等式は reduction と decidable equality により判定できる。

## Lean 固有の処理

### nested existential の witness 構築

`GoldenUnitFifthClass` は

```lean
∃ i : Fin 5, ∃ delta : GoldenInt, ...
```

なので、

```lean
⟨⟨0, by decide⟩, -goldenOne, ?_⟩
```

という constructor notation だけで sector と fifth-power base をまとめて供給できる。

### `Fin 5`

単なる自然数 `0` ではなく `Fin 5` を要求するため、境界証明を含む値を構築する必要がある。ここでは `by decide` がその proof field を埋める。

### 最後の `decide`

`ring` や `norm_num` を使わず、完全に閉じた proposition の decidability を利用している。これは project 固有の algebraic wrapper が十分計算可能に定義されていることを利用した非常に短い証明である。

## 冗長・重複箇所

直前の `goldenUnitFifthClass_one` は

```lean
refine ⟨⟨0, by decide⟩, goldenOne, ?_⟩
decide
```

というほぼ同一形である。本定理との差は fifth-power witness が `goldenOne` か `-goldenOne` かだけである。

さらに `goldenUnitFifthClass_phi` と `goldenUnitFifthClass_neg_phi` も measure-one 基底ケースを個別 theorem として並べる設計になっている。

この重複は機械的にはまとめられるが、四つの基底ケースを名前付き theorem として保持することで `goldenUnitFifthClass_of_unit` の基底分岐が読みやすくなる利点がある。

## 最適化候補

### 1. `±1` 基底ケースの共通化

たとえば符号を表す有限データを導入し、`1` と `-1` を一つの補題から導くことは可能と考えられる。ただし、現状は各証明が二行しかなく、抽象化するとかえって補助定義が増える可能性がある。

### 2. witness notation のさらに短い記述

elaboration が許せば、定義展開を `simpa [GoldenUnitFifthClass]` 等へ寄せる余地はある。しかし実際に短くなるか、現在の project 定義で安定するかは Lean ビルドを行っていないため未確認である。

### 3. 基底四定理の統一 API

`goldenUnit_measure_one_cases` が返す四候補を直接 `GoldenUnitFifthClass` へ写す補題を一つ用意すれば、strong-induction 本体の四枝を局所化できる。ただし個々の定理名による監査性との交換条件になる。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用していることを確認できる。

本定理単体で表面上必要なのは、`Fin 5`、existential constructor、negation、power、decidable equality、`decide` と、project 側の `GoldenInt` / unit-class 定義群である。`ring`, `omega`, `nlinarith`, `fin_cases` などの tactic は本定理本文では使用しない。

そのため `Mathlib` 全体より小さい import 集合へ縮小できる可能性は高い。ただし、`GoldenInt` と関連インスタンスの依存を含めた厳密な最小 import は、今回は Lean ビルドを行わない条件なので確認していない。従って具体的な最小 module 名は推測として固定しない。

## Comparator challenge 化の可否

**可能。特に micro challenge 向きである。**

challenge としては、既存定義

```lean
GoldenUnitFifthClass (-goldenOne)
```

のみを goal として与え、モデルが

1. sector `0 : Fin 5` を選ぶ、
2. fifth-power witness に `-goldenOne` を選ぶ、
3. 残りの閉じた等式を計算または基本代数で閉じる、

ところまでを生成できるか評価できる。

数学的難度は非常に低いため、大規模推論能力の比較には向かない。一方、existential witness の選択、`Fin` の境界証明、project 固有定義の reducibility、`decide` の利用を試す小型 Comparator 課題としては明瞭である。

## 次に読むべき宣言

Lean 正本で直後にある未解説宣言は

```lean
private theorem goldenUnitFifthClass_phi : GoldenUnitFifthClass goldenPhi := by
  refine ⟨⟨1, by decide⟩, goldenOne, ?_⟩
  decide
```

である。

したがって次は **0368 `goldenUnitFifthClass_phi`** を読むべきである。`-1` では負号を fifth power に吸収したのに対し、`φ` では representative sector 自体を `0` から `1` へ移す最初の基底例になる。