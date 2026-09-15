# 0362 — `golden_sector_zero_mul_phiInv`

## 宣言種別

この宣言は **`private theorem`** である。

```lean
private theorem golden_sector_zero_mul_phiInv (delta : GoldenInt) :
    (goldenPhi ^ 0 * delta ^ 5) * goldenPhiInv =
      goldenPhi ^ 4 * (goldenPhiInv * delta) ^ 5 := by
  rw [mul_pow]
  calc
    (goldenPhi ^ 0 * delta ^ 5) * goldenPhiInv =
        goldenPhiInv * delta ^ 5 := by ring
    _ = (goldenPhi ^ 4 * goldenPhiInv ^ 5) * delta ^ 5 := by
      rw [golden_phi_four_mul_inv_five]
    _ = goldenPhi ^ 4 * (goldenPhiInv ^ 5 * delta ^ 5) := by ring
```

`GoldenUnitFifthClass` の sector `0` を `goldenPhiInv` 倍したとき、代表指数を `4` に巻き戻し、余分な `goldenPhiInv ^ 5` を fifth-power base 側へ吸収する局所補題である。

## Lean の型

```lean
golden_sector_zero_mul_phiInv :
  (delta : GoldenInt) →
    (goldenPhi ^ 0 * delta ^ 5) * goldenPhiInv =
      goldenPhi ^ 4 * (goldenPhiInv * delta) ^ 5
```

任意の `delta : GoldenInt` に対する黄金整数環内の等式である。`private` なので、この宣言名は外部 API ではなく `GoldenUnitClassification.lean` 内部の補助定理として使われる。

## 数学的主張

`goldenPhi = φ`、`goldenPhiInv = φ⁻¹` と読むと、左辺は

$$
(\varphi^0\delta^5)\varphi^{-1}
=\delta^5\varphi^{-1}.
$$

0361 `golden_phi_four_mul_inv_five` は

$$
\varphi^4(\varphi^{-1})^5=\varphi^{-1}
$$

を与える。したがって

$$
\delta^5\varphi^{-1}
=\varphi^4(\varphi^{-1})^5\delta^5
=\varphi^4(\varphi^{-1}\delta)^5.
$$

つまり fifth powers を法とした unit class では

$$
0\xrightarrow{\times\varphi^{-1}}4
$$

という循環遷移になる。

指数だけなら `0 - 1 ≡ 4 (mod 5)` という単純な事実だが、Lean では負の指数を直接使わず、`φ⁻¹` の fifth power を新しい fifth-power witness に吸収することで、`Fin 5` の代表 `4` に戻している。

## 証明全体での役割

0360 `GoldenUnitFifthClass` は

$$
x=\varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\}
$$

という five-sector 表現を定義した。

0359 `goldenUnit_descent` では、より小さい unit `y` から元の `x` を

$$
x=y\varphi
\quad\text{または}\quad
x=y\varphi^{-1}
$$

として復元する。そのため unit class の strong induction を閉じるには、既に class を持つ要素を `φ` または `φ⁻¹` 倍しても再び `GoldenUnitFifthClass` を持つことを示す必要がある。

`φ⁻¹` 倍について sector `1,2,3,4` は指数を単純に一つ下げればよい。一方 sector `0` だけは `-1` が `Fin 5` の自然数代表ではないため特別処理が必要である。本定理はその唯一の wrap-around case を担当する。

実際、後続 `goldenUnitFifthClass_mul_phiInv` の `i = 0` 分岐では、本定理がそのまま witness 変換として使われる。

## 直接依存する定義・補題

直接名前として現れる主要なプロジェクト内宣言は次である。

- `GoldenInt` — 黄金整数の座標型。
- `goldenPhi` — 黄金比 unit `φ`。
- `goldenPhiInv` — `φ` の積逆元。
- 0361 `golden_phi_four_mul_inv_five` — `φ⁴(φ⁻¹)⁵ = φ⁻¹` を与える wrap-around 等式。

Lean 側では通常の環演算 `*`, `^` と Mathlib の `mul_pow`, `ring` を使用する。

数学的背景として `golden_phi_mul_inv : goldenPhi * goldenPhiInv = 1` も存在するが、本定理の証明では直接呼ばれない。

## 証明の流れ

### 1. 積の 5 乗を展開する

最初に

```lean
rw [mul_pow]
```

を実行する。

これにより右辺の

```lean
(goldenPhiInv * delta) ^ 5
```

が

```lean
goldenPhiInv ^ 5 * delta ^ 5
```

へ変形され、0361 の補題を適用できる形になる。

### 2. sector 0 の左辺を単純化する

```lean
(goldenPhi ^ 0 * delta ^ 5) * goldenPhiInv
```

を

```lean
goldenPhiInv * delta ^ 5
```

へ変形する。この段階は

```lean
by ring
```

で閉じている。

数学的には `φ⁰ = 1` と可換性による並べ替えだけである。

### 3. wrap-around 等式を挿入する

中央の等式

```lean
goldenPhiInv * delta ^ 5 =
  (goldenPhi ^ 4 * goldenPhiInv ^ 5) * delta ^ 5
```

は

```lean
rw [golden_phi_four_mul_inv_five]
```

で証明する。

ここが本定理の本質である。`φ⁻¹` を `φ⁴(φ⁻¹)⁵` に置き換えることで、指数代表を `4` に戻す。

### 4. fifth-power witness の形へ再結合する

最後に

```lean
(goldenPhi ^ 4 * goldenPhiInv ^ 5) * delta ^ 5
```

を

```lean
goldenPhi ^ 4 * (goldenPhiInv ^ 5 * delta ^ 5)
```

へ並べ替える。ここも `ring` が処理する。

冒頭の `rw [mul_pow]` と合わせることで、最終的には

```lean
goldenPhi ^ 4 * (goldenPhiInv * delta) ^ 5
```

という `GoldenUnitFifthClass` の要求形式になる。

## Lean 固有の処理

### `rw [mul_pow]`

`mul_pow` は

$$
(ab)^n=a^n b^n
$$

を使う標準補題である。`GoldenInt` は可換環として構成されているため適用できる。

ここでは単なる整理ではなく、既存補題 `golden_phi_four_mul_inv_five` の左辺を露出させる役割がある。

### `calc`

三段階の等式変形を明示し、

1. sector 0 の簡約、
2. 0361 の wrap-around 挿入、
3. fifth-power witness への再結合、

という数学的構造をそのまま Lean 上へ写している。

### `ring`

1 段目と 3 段目は抽象的な整数論ではなく、可換環の結合則・交換則・単位元・冪の正規化だけである。そのため `ring` で閉じられる。

## 冗長・重複箇所

証明は短く、重大な冗長性はない。

ただし 1 段目の

```lean
by ring
```

は `pow_zero`, `one_mul`, `mul_comm` などの rewrite でも書ける。3 段目も `mul_assoc` と交換則だけで処理可能である。

現在の `ring` は簡潔で、環演算の細かな並べ替えを proof script から隠している。その代わり、この補題が本質的には非常に小さなモノイド計算であることはコードだけでは見えにくい。

また `golden_sector_zero_mul_phiInv` と次の `golden_sector_succ_mul_phiInv` はともに `φ⁻¹` 倍による sector 遷移を担当しており、概念的には一つの `Fin 5` 循環作用としてまとめられる。

## 最適化候補

1. **現状維持** — `calc` が sector `0 → 4` の数学的意味を明瞭に示しており、十分に小さい。
2. **`ring` 依存を弱める** — `pow_zero`, `one_mul`, `mul_assoc`, `mul_comm` 等だけで証明すれば、この補題が必要とする代数構造をより弱くできる可能性がある。
3. **sector 遷移の一般化** — `Fin 5` 上の加減算と fifth-power witness の補正を一つの一般補題にすれば、zero case と successor case を統合できる可能性がある。ただし Lean の `Fin` 算術と witness transport が増え、現行の明示 case split より複雑になる可能性も高い。
4. **explicit API の統一** — 本 theorem は `goldenMul` / `goldenPow` ではなく ring notation `*` / `^` を使う。周辺 API と記法を統一する設計余地はあるが、現状では `[simp]` bridge が既に整備されており、変更効果は限定的と考えられる。

これらの置換候補は Lean ビルドを行っていないため成立性を未確認である。

## 必要 Mathlib import と import 最適化候補

standalone `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem 自体が直接必要とする Mathlib 機能は主として

- 自然数冪と `mul_pow`,
- 可換環の基本等式,
- `ring` tactic,

である。

したがって本 theorem 単体が `Mathlib` 全体を必要とするわけではない。実際の `GoldenUnitClassification.lean` では、`GoldenInt`, `goldenPhi`, `goldenPhiInv`, 0361 と後続の unit-class API を供給するプロジェクト import に加え、`ring` が利用できれば足りる可能性がある。

厳密な最小 import 集合は Lean ビルドを行っていないため未確認である。

## Comparator challenge 化の可否

**適している。**

challenge は例えば次の形にできる。

```lean
private theorem golden_sector_zero_mul_phiInv (delta : GoldenInt) :
    (goldenPhi ^ 0 * delta ^ 5) * goldenPhiInv =
      goldenPhi ^ 4 * (goldenPhiInv * delta) ^ 5 := by
  ?_
```

前提として 0361

```lean
golden_phi_four_mul_inv_five :
  goldenPhi ^ 4 * goldenPhiInv ^ 5 = goldenPhiInv
```

を与える。

0361 のような完全具体計算より一段上で、任意の `delta` を含むため、モデルは

- `mul_pow` を使って fifth power を分配すること、
- wrap-around 補題を正しい向きで挿入すること、
- 可換環計算で witness 形へ戻すこと、

を理解する必要がある。小規模ながら「局所補題を一般 witness 変換へ持ち上げる」能力を測る Comparator challenge として良い。

## 次に読むべき宣言

次は **0363 `golden_sector_succ_mul_phiInv`**、種別は **`private theorem`** である。

```lean
private theorem golden_sector_succ_mul_phiInv (delta : GoldenInt) (n : ℕ) :
    (goldenPhi ^ (n + 1) * delta ^ 5) * goldenPhiInv =
      goldenPhi ^ n * delta ^ 5 := by
  calc
    (goldenPhi ^ (n + 1) * delta ^ 5) * goldenPhiInv =
        goldenPhi ^ n * delta ^ 5 * (goldenPhi * goldenPhiInv) := by
      rw [pow_succ]
      ring
    _ = goldenPhi ^ n * delta ^ 5 := by
      rw [show goldenPhi * goldenPhiInv = 1 by exact golden_phi_mul_inv, mul_one]
```

0362 が `0 → 4` の wrap-around を担当するのに対し、0363 は一般の successor sector

$$
n+1\xrightarrow{\times\varphi^{-1}}n
$$

を処理する。両者を合わせることで、後続 `goldenUnitFifthClass_mul_phiInv` の 5 分岐すべてを閉じられる。