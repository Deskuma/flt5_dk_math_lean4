# 0363 — `golden_sector_succ_mul_phiInv`

## 宣言種別

この宣言は **`private theorem`** である。

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

0362 `golden_sector_zero_mul_phiInv` が sector `0` の wrap-around `0 → 4` を担当したのに対し、本定理は successor sector の通常遷移

$$
n+1 \xrightarrow{\times\varphi^{-1}} n
$$

を一括して与える局所補題である。

## Lean の型

```lean
golden_sector_succ_mul_phiInv :
  (delta : GoldenInt) → (n : ℕ) →
    (goldenPhi ^ (n + 1) * delta ^ 5) * goldenPhiInv =
      goldenPhi ^ n * delta ^ 5
```

任意の `delta : GoldenInt` と `n : ℕ` に対する黄金整数環内の等式である。`private` 宣言なので、外部 API ではなく unit-class 分類内部の補助定理として使われる。

## 数学的主張

`goldenPhi = φ`、`goldenPhiInv = φ⁻¹` と読むと、主張は

$$
(\varphi^{n+1}\delta^5)\varphi^{-1}
=\varphi^n\delta^5
$$

である。

指数法則と逆元関係

$$
\varphi^{n+1}=\varphi^n\varphi,
\qquad
\varphi\varphi^{-1}=1
$$

を使えば、

$$
\varphi^{n+1}\delta^5\varphi^{-1}
=\varphi^n\delta^5(\varphi\varphi^{-1})
=\varphi^n\delta^5
$$

となる。

0362 と異なり fifth-power witness `delta` 自体を変更する必要はない。sector が `1,2,3,4` のどれかなら、`φ⁻¹` 倍は指数を単純に 1 下げるだけだからである。

## 証明全体での役割

0360 `GoldenUnitFifthClass` は

$$
x=\varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\}
$$

という five-sector 表現を定義した。

0359 `goldenUnit_descent` を strong induction に接続するためには、より小さい unit が fifth class に属するとき、それを `φ` または `φ⁻¹` 倍しても fifth class に留まることを示す必要がある。

`φ⁻¹` 倍では、sector `0` だけが `-1 ≡ 4 (mod 5)` の wrap-around を必要とするため 0362 が別途処理する。本定理は残る successor cases を一つの一般式で処理し、後続 `goldenUnitFifthClass_mul_phiInv` の `i = 1,2,3,4` 各分岐で `n = 0,1,2,3` として使われる。

したがって 0362 と 0363 を合わせると、`Fin 5` 上の `−1` 作用が完全に実装される。

## 直接依存する定義・補題

主要なプロジェクト内依存は次である。

- `GoldenInt` — 黄金整数の座標型。
- `goldenPhi` — 黄金比 unit `φ`。
- `goldenPhiInv` — `φ` の積逆元。
- `golden_phi_mul_inv` — `goldenPhi * goldenPhiInv = 1`。

Mathlib 側では主に次を使う。

- `pow_succ`
- `mul_one`
- `rw`
- `ring`

0361 `golden_phi_four_mul_inv_five` や 0362 `golden_sector_zero_mul_phiInv` には直接依存しない。概念上は対になるが、証明依存としては独立している。

## 証明の流れ

### 1. successor power を一段分解する

最初の `calc` ステップで

```lean
rw [pow_succ]
ring
```

を使う。

`pow_succ` により

```lean
goldenPhi ^ (n + 1)
```

を

```lean
goldenPhi ^ n * goldenPhi
```

へ展開する。その後 `ring` が積の結合・交換を正規化し、

```lean
goldenPhi ^ n * delta ^ 5 *
  (goldenPhi * goldenPhiInv)
```

という逆元対が明示された形へ整える。

### 2. `φ * φ⁻¹ = 1` を消去する

第 2 ステップでは

```lean
rw [show goldenPhi * goldenPhiInv = 1 by exact golden_phi_mul_inv, mul_one]
```

を使う。

`show ... by exact ...` によって、既存 theorem `golden_phi_mul_inv` を rewrite に使う等式として明示し、

```lean
goldenPhi * goldenPhiInv
```

を `1` に変える。続く `mul_one` が末尾の単位元を消去し、目標の

```lean
goldenPhi ^ n * delta ^ 5
```

を得る。

## Lean 固有の処理

### `pow_succ`

自然数指数に対する標準等式

$$
a^{n+1}=a^n a
$$

を展開する。数学的主張の核心である「指数を 1 下げる」操作を、逆元との積へ変換する入口である。

### `ring`

ここでの `ring` は黄金整数固有の数論を証明しているわけではない。`pow_succ` 後の積を並べ替え、`goldenPhi * goldenPhiInv` を隣接させるための可換環正規化を担当する。

### `show ... by exact golden_phi_mul_inv`

単に `rw [golden_phi_mul_inv]` と書くより、rewrite したい具体的等式の型を明示する書き方である。型推論の曖昧さを避け、証明の意図も読みやすい。

## 冗長・重複箇所

証明は短く、本質的な重複は少ない。

ただし 0362 と 0363 はともに「`φ⁻¹` 倍による sector transition」を実装しているため、概念的には同じ循環作用の二分割である。現状は `Fin 5` の zero case と successor case を明示的に分けることで、負指数や modular arithmetic を proof term に持ち込まずに済んでいる。

また最初の `ring` は、実際には結合則・交換則・`pow_succ` 後の並べ替えだけなので、より弱い algebraic rewrite だけでも置換できる可能性がある。

## 最適化候補

1. **現状維持** — theorem は非常に短く、0362 と役割分担も明確である。
2. **`ring` の縮小** — `mul_assoc`, `mul_left_comm`, `mul_comm` などで直接並べ替えれば、必要 tactic 依存を減らせる可能性がある。
3. **`simpa` 化** — `pow_succ` と `golden_phi_mul_inv` を適切な simp set に入れれば、さらに短い証明になる可能性がある。ただし rewrite 順序が見えにくくなる。
4. **`Fin 5` 循環作用への一般化** — 0362 と統合して `i ↦ i - 1 mod 5` を一つの補題にできる可能性がある。一方で witness 補正を伴う zero case のため、現在の明示的二分割の方が Lean 上は単純である可能性が高い。

これらは Lean ビルドを行っていないため未検証である。

## 必要 Mathlib import と import 最適化候補

standalone `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem 単体で直接必要なのは、自然数冪、可換環演算、`pow_succ`, `mul_one`, `ring` と、プロジェクト側の黄金整数・逆元 API である。

したがって `Mathlib` 全体は過剰である可能性が高い。ただし実際の `GoldenUnitClassification.lean` の最小 import は周辺宣言の依存も含めて決まるため、Lean ビルドなしには確定できない。

## Comparator challenge 化の可否

**適している。**

例えば次を hole とできる。

```lean
private theorem golden_sector_succ_mul_phiInv (delta : GoldenInt) (n : ℕ) :
    (goldenPhi ^ (n + 1) * delta ^ 5) * goldenPhiInv =
      goldenPhi ^ n * delta ^ 5 := by
  ?_
```

前提として

```lean
golden_phi_mul_inv : goldenPhi * goldenPhiInv = 1
```

を与える。

challenge は、モデルが

- `pow_succ` で指数を一段分解すること、
- 逆元対を露出するよう積を並べ替えること、
- `φφ⁻¹ = 1` を使って閉じること、

を認識できるかを測れる。0362 よりさらに純粋な algebraic micro challenge である。

## 次に読むべき宣言

次は **0364 `goldenUnitFifthClass_mul_phiInv`**、種別は **`theorem`** である。

この theorem は `GoldenUnitFifthClass x` の witness `⟨i, delta, hx⟩` を取り出し、`fin_cases i` で 5 sector に分岐する。sector `0` では 0362 `golden_sector_zero_mul_phiInv` を、sector `1,2,3,4` では本 0363 `golden_sector_succ_mul_phiInv` を使い、

$$
GoldenUnitFifthClass(x)
\Longrightarrow
GoldenUnitFifthClass(x\varphi^{-1})
$$

を完成させる。
