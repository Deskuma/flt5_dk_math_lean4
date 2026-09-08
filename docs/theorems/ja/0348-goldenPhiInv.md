# 0348 — `goldenPhiInv`

## 宣言種別

この宣言は **`def`** である。

```lean
/-- The integral inverse `phi - 1` of `phi` in the coordinate model. -/
def goldenPhiInv : GoldenInt := ⟨-1, 1⟩
```

## Lean の型

```lean
goldenPhiInv : GoldenInt
```

`GoldenInt` は基底 `1, φ` による整数座標

```lean
structure GoldenInt where
  fst : ℤ
  snd : ℤ
```

を持ち、座標 `⟨a, b⟩` は数学的に $a+b\varphi$ を表す。したがって

```lean
⟨-1, 1⟩
```

は

$$
-1+\varphi=\varphi-1
$$

を表す。

## 数学的意味

この定義は黄金比基底元 $\varphi$ の整数環内での逆元候補

$$
\varphi^{-1}=\varphi-1
$$

を明示的な `GoldenInt` として導入する。

この座標環では既に

$$
\varphi^2=\varphi+1
$$

が証明されているため、形式的には

$$
\varphi(\varphi-1)
=\varphi^2-\varphi
=1
$$

となる。実際、直後の宣言 `golden_phi_mul_inv` と `golden_inv_mul_phi` が左右両方向の積が `goldenOne` になることを証明する。

したがって `goldenPhiInv` 自体は逆元性を証明する theorem ではなく、後続証明で使用する **具体的な逆元要素の定義** である。

## 証明全体での役割

ここから `GoldenUnitClassification` モジュールに入り、黄金整数環の unit を初等的に分類する。

このモジュールの方針は、非基底 unit に `φ` または `φ⁻¹` を掛けて座標 measure を減少させ、最終的に基底 unit まで descent することである。そのため `φ` と同じく、環内に具体的に存在する `φ⁻¹` が必要になる。

`goldenPhiInv` は次の流れの入口である。

```text
goldenPhiInv
  → golden_phi_mul_inv / golden_inv_mul_phi
  → goldenUnit_phiInv
  → golden_mul_phiInv_coords
  → goldenUnit_descent
  → golden unit classification
```

つまり FLT5 の zero-sector factorization を終えた後、unit class を fifth-power class へ整理するための descent machinery に必要な基本要素を与える。

## 直接依存する定義・補題

この `def` の本体が直接依存するプロジェクト宣言は `GoldenInt` だけである。

- `GoldenInt` — $a+b\varphi$ を整数座標 `⟨a,b⟩` で表す structure

数学的な意味を読むためには、既出の次の宣言が関係する。

- `goldenPhi : GoldenInt := ⟨0, 1⟩`
- `goldenOne : GoldenInt := ⟨1, 0⟩`
- `golden_phi_sq` — $\varphi^2=\varphi+1$
- `goldenMul` / `Mul GoldenInt` — 黄金整数の乗法

ただし、これらは `goldenPhiInv` の定義本体そのものには出現しない。

## 構築の流れ

構築は一段だけである。

1. 返り値を `GoldenInt` とする。
2. `fst = -1`, `snd = 1` の座標を constructor notation `⟨-1, 1⟩` で与える。
3. これにより $-1+\varphi=\varphi-1$ を環の要素として固定する。

この宣言単体には proof term や tactic script は存在しない。

## Lean 固有の処理

### structure constructor notation

```lean
⟨-1, 1⟩
```

は `GoldenInt.mk (-1) 1` の省略記法である。期待型が `GoldenInt` なので、Lean は二つの整数を `fst`, `snd` に割り当てる。

### 負の整数リテラル

`-1` は期待型 `ℤ` により整数として解釈される。`GoldenInt.fst` の型が `ℤ` であるため追加の cast は不要である。

### `def` と証明の分離

逆元性を定義時に dependent field として持たせず、まず裸の環要素を `def` で置き、その後

```lean
golden_phi_mul_inv
golden_inv_mul_phi
goldenUnit_phiInv
```

で性質を証明する設計になっている。この分離により座標計算用の要素としても再利用しやすい。

## 冗長・重複箇所

この宣言は一行の concrete definition であり、冗長な箇所はない。

数学的には `goldenPhi - goldenOne` として定義する選択肢もあるが、現在の `⟨-1, 1⟩` は座標を直接露出し、後続の `decide` や座標正規化が単純になる利点がある。

したがって、意味上の重複というより **座標表示と代数表示のどちらを canonical definition にするか** という設計選択である。

## 最適化候補

局所的な最適化はほぼ不要である。

候補としては

```lean
def goldenPhiInv : GoldenInt := goldenPhi - goldenOne
```

のように代数的意味を前面に出す書き方が考えられる。しかしこれが後続の `decide`、`simp`、座標式に有利かどうかは Lean ビルドを行わずには確認できない。また現行の coordinate model では `⟨-1,1⟩` の方が最も直接的である。

よって現状では変更を推奨する根拠は弱い。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

`goldenPhiInv` 単体が Mathlib から必要とする機能は非常に少なく、実質的には整数型 `ℤ`、負の数値リテラル、structure constructor を支える Lean/Mathlib 基盤だけである。ただし `GoldenInt` 自体が前段で ring structure などを構築しており、モジュール単位での最小 import はこの一行だけからは決定できない。

Lean ビルドを行っていないため、`GoldenUnitClassification.lean` の厳密な最小 import 集合は **未確認** である。standalone 全体の `import Mathlib` を細分化できる可能性はあるが、本宣言だけを根拠に具体的 import を断定しない。

## Comparator challenge 化の可否

**可能。ただし単体ではかなり易しい。**

challenge とするなら、単なる座標定義を当てさせるより、次の性質まで含める方が適切である。

```lean
def candidatePhiInv : GoldenInt := ?_

example :
    goldenMul goldenPhi candidatePhiInv = goldenOne := by
  ...

example :
    goldenMul candidatePhiInv goldenPhi = goldenOne := by
  ...
```

これなら $\varphi^2=\varphi+1$ を座標環へ翻訳し、正しい逆元 `⟨-1,1⟩` を構成できるかを比較できる。

定義だけを穴埋めにする場合は探索空間が小さすぎるため、Comparator challenge としての識別力は低い。

## 次に読むべき宣言

次は **0349 `golden_phi_mul_inv`** を読むべきである。宣言種別は **`theorem`**。

```lean
theorem golden_phi_mul_inv :
    goldenMul goldenPhi goldenPhiInv = goldenOne := by decide
```

0348 が置いた `goldenPhiInv = φ - 1` が実際に $\varphi$ の右逆元であることを、具体的座標計算によって証明する最初の verification theorem である。

その次には反対向き

```lean
golden_inv_mul_phi
```

が続き、両方向の逆元性から `goldenUnit_phiInv` が構築される。
