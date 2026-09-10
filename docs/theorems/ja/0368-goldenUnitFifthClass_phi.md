# 0368 — `goldenUnitFifthClass_phi`

## 宣言種別

この宣言は **`private theorem`** である。

```lean
private theorem goldenUnitFifthClass_phi : GoldenUnitFifthClass goldenPhi := by
  refine ⟨⟨1, by decide⟩, goldenOne, ?_⟩
  decide
```

## Lean の型

概念的な型は次である。

```lean
goldenUnitFifthClass_phi :
  GoldenUnitFifthClass goldenPhi
```

`GoldenUnitFifthClass` は

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

と定義されている。したがって本定理は、黄金比 unit `goldenPhi` 自身が fifth-power modulo の五つの sector の一つに属することを、具体的 witness とともに示す。

## 数学的主張

本定理が選ぶ witness は

$$
i=1,
\qquad
\delta=1
$$

である。したがって数学的内容は

$$
\varphi
=\varphi^1 1^5
=\varphi
$$

という最も基本的な sector `1` の代表元恒等式である。

直前の `goldenUnitFifthClass_one` と `goldenUnitFifthClass_neg_one` が sector `0` を具体化したのに対し、本定理では初めて exponent representative が `1` となる。つまり

$$
\varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\}
$$

という五分類において `goldenPhi` が sector `1` の標準代表であることを固定する。

## 証明全体での役割

0356 `goldenUnit_measure_one_cases` は measure 1 の golden unit を

$$
1,\;-1,\;\varphi,\;-\varphi
$$

の四候補へ分類する。

後続 `goldenUnitFifthClass_of_unit` は `goldenUnitMeasure` による strong induction を使い、任意の golden unit を `GoldenUnitFifthClass` に分類する。その基底部分では measure 1 の四候補をそれぞれ fifth class に入れる必要がある。

本定理はそのうち `x = goldenPhi` の枝を閉じる基底補題である。これにより strict descent が measure 1 まで到達したとき、`φ` という terminal unit を sector `1` へ確実に着地させられる。

一方、measure が 1 より大きい induction step では `goldenUnit_descent` により小さい unit へ降下し、`goldenUnitFifthClass_mul_phi` または `goldenUnitFifthClass_mul_phiInv` を使って class を元の unit へ持ち上げる。本定理はその再帰の底にある四つの concrete endpoint の一つである。

## 直接依存する定義・補題

プロジェクト側で直接関係する主な宣言は次である。

- `GoldenInt` — 黄金整数を表す型。
- `goldenOne` — 黄金整数における明示的な `1`。
- `goldenPhi` — 黄金比 unit `φ`。
- `goldenMul` — 黄金整数の乗法。
- `goldenPow` — 黄金整数の冪。
- `GoldenUnitFifthClass` — `x = φ^i δ^5`, `i : Fin 5` という five-sector predicate。

証明本文では既存の project theorem を `rw` や `exact` で呼び出していない。`GoldenUnitFifthClass` の existential witness を直接構成し、残った閉じた等式を `decide` で認証している。

証明全体の文脈では `goldenUnit_measure_one_cases` が本定理を必要とするケースを供給し、後続 `goldenUnitFifthClass_of_unit` が本定理を消費する。

## 証明・構築の流れ

### 1. sector `1` を選ぶ

```lean
refine ⟨⟨1, by decide⟩, goldenOne, ?_⟩
```

`GoldenUnitFifthClass goldenPhi` の二つの existential witness を同時に供給する。

第一 witness は

```lean
⟨1, by decide⟩ : Fin 5
```

であり、sector `1` を選ぶ。`Fin 5` の値を構築するには `1 < 5` が必要であるが、これは閉じた数値命題なので `decide` で証明できる。

第二 witness は

```lean
goldenOne : GoldenInt
```

である。これにより残る等式は概念的に

$$
\varphi=\varphi^1\cdot1^5
$$

となる。

### 2. 具体等式を計算で閉じる

```lean
decide
```

で残った proposition を閉じる。

`goldenPhi`, `goldenOne`, `goldenPow`, `goldenMul` が具体的かつ計算可能なデータとして実装され、黄金整数の等式が decidable であるため、この完全に閉じた等式は reduction によって認証できる。

## Lean 固有の処理

### nested existential の constructor notation

`GoldenUnitFifthClass` は

```lean
∃ i : Fin 5, ∃ delta : GoldenInt, ...
```

という二重 existential なので、

```lean
⟨⟨1, by decide⟩, goldenOne, ?_⟩
```

で `i` と `delta` を一度に渡せる。最後の `?_` が残る equality proof の hole である。

### `Fin 5` による sector の有限化

自然数 `1` だけではなく `Fin 5` を witness にすることで、sector exponent が型レベルで `0,1,2,3,4` に制限される。本定理の `by decide` は `1 < 5` という subtype の境界条件だけを閉じている。

### 最後の `decide`

証明は `ring`、`norm_num`、`simp` を使わず、閉じた equality の decidability に委ねる。このため proof term は極めて小さい。一方で、人間向けの代数的説明としては `φ = φ^1 · 1^5` が本質であり、`decide` はその具体実装を計算で確認しているだけである。

## 冗長・重複箇所

直前の measure-one 基底補題群とは強い構文的重複がある。

`goldenUnitFifthClass_one` は sector `0`, witness `goldenOne`、`goldenUnitFifthClass_neg_one` は sector `0`, witness `-goldenOne`、本定理は sector `1`, witness `goldenOne` を選ぶ。直後の `goldenUnitFifthClass_neg_phi` は sector `1`, witness `-goldenOne` を選ぶ。

したがって四補題は実質的に

$$
(\pm1)=\varphi^0(\pm1)^5,
\qquad
(\pm\varphi)=\varphi^1(\pm1)^5
$$

という $2\times2$ の小さな表を個別 theorem として展開したものと見なせる。

この重複は抽象化可能だが、strong induction の四つの terminal branch に対応する名前付き theorem を残すことで、後続証明の監査性と読みやすさを高めている。

## 最適化候補

### 1. `goldenUnitFifthClass_one` から導出する

既に

```lean
goldenUnitFifthClass_mul_phi
```

があるため、`GoldenUnitFifthClass goldenOne` から `goldenOne * goldenPhi` の class を得て、`goldenOne * goldenPhi = goldenPhi` を簡約すれば本定理を導ける可能性がある。

ただし現在の二行証明より依存関係が増え、単純な具体基底ケースとしての局所性が失われる。従ってコード量と依存の小ささでは現行実装の方が有利である。

### 2. measure-one 四基底の共通化

符号と sector `0/1` をパラメータ化した補助補題を作れば四 theorem の重複を減らせる。ただし抽象化のための補助データが二行の concrete proof より複雑になる可能性が高い。

### 3. `decide` 依存を明示的代数へ置換する

`golden_pow_eq` や乗法恒等元の補題を使って `simp` 的に証明する設計も考えられる。これは定義の reducibility に依存しにくい証明へする場合には価値があるが、現在の定義群で実際に短く安定するかは Lean ビルドを行っていないため未確認である。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用していることを確認できる。

本定理本文そのものが表面上必要とする Lean/Mathlib 機能は、`Fin 5`、existential constructor、冪・乗法を含む project 定義の型付け、decidable equality、`decide` である。`ring`, `omega`, `nlinarith`, `fin_cases` などの tactic は本文では使わない。

そのため本定理だけを isolated challenge として切り出すなら `Mathlib` 全体よりかなり狭い import にできる可能性がある。しかし `GoldenInt`、`goldenPow`、`goldenMul` とそれらの instances が実際に要求する import を含めた厳密な最小 module 集合は、今回は Lean ビルドを行わない条件なので確認していない。具体的な最小 import 名を断定することは避ける。

## Comparator challenge 化の可否

**可能。micro challenge として適している。**

challenge goal を

```lean
GoldenUnitFifthClass goldenPhi
```

とし、定義群だけを与えれば、モデルが

1. `Fin 5` の sector witness として `1` を選ぶ、
2. fifth-power base として `goldenOne` を選ぶ、
3. `φ = φ^1 · 1^5` を計算または基本代数で閉じる、

という witness synthesis を実行できるか評価できる。

単独では数学的難度が低いため、大きな探索能力の比較には向かない。しかし 0365, 0367, 0368 と直後の `goldenUnitFifthClass_neg_phi` を一組にし、四つの measure-one terminal unit を最小依存で class 化させる課題にすると、project 固有の finite witness 構築と algebraic normalization の比較には使いやすい。

## 次に読むべき宣言

Lean 正本で直後にある未解説宣言は

```lean
private theorem goldenUnitFifthClass_neg_phi :
    GoldenUnitFifthClass (-goldenPhi) := by
  refine ⟨⟨1, by decide⟩, -goldenOne, ?_⟩
  decide
```

である。

したがって次は **0369 `goldenUnitFifthClass_neg_phi`** を読むべきである。本定理が `φ = φ^1 · 1^5` を sector `1` の正の基底として登録するのに対し、次は

$$
-\varphi=\varphi^1(-1)^5
$$

として負号を fifth-power witness 側へ吸収し、measure-one の四基底ケースを完成させる。