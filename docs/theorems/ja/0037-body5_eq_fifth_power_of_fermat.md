# 0037 — `body5_eq_fifth_power_of_fermat`

## 宣言

```lean
theorem body5_eq_fifth_power_of_fermat
    {x y z : ℕ}
    (hyz : y ≤ z)
    (hEq : Fermat5Equation x y z) :
    Body5 (z - y) y = x ^ 5 := by
  calc
    Body5 (z - y) y = z ^ 5 - y ^ 5 := by
      simpa [Nat.sub_add_cancel hyz] using
        (body5_eq_add_pow_sub (z - y) y)
    _ = x ^ 5 := fifth_sub_eq_of_add_eq hEq
```

## Lean の型

```lean
body5_eq_fifth_power_of_fermat :
  {x y z : ℕ} →
  y ≤ z →
  Fermat5Equation x y z →
  Body5 (z - y) y = x ^ 5
```

自然数 `x`, `y`, `z` が第五冪 Fermat 方程式を満たし、自然数減算を安全に戻すための順序条件 `y ≤ z` があるなら、gap 座標での full body が `x^5` に等しいことを述べます。

## 数学的主張

`g=z-y` と置くと、前号より

$$
Body5(g,y)=(g+y)^5-y^5
$$

です。`y≤z` により $(z-y)+y=z$ なので、

$$
Body5(z-y,y)=z^5-y^5
$$

となります。一方、

$$
x^5+y^5=z^5
$$

から、

$$
z^5-y^5=x^5
$$

です。したがって、

$$
Body5(z-y,y)=x^5
$$

を得ます。

## 証明全体での役割

本定理は `Body5` の一般恒等式を、反例候補 `CounterexamplePack` が持つ Fermat 方程式へ接続する特殊化 bridge です。

後続の clean-channel 反証では、素数 `q` が `Body5 (z-y) y` を一度だけ割ることから、この body は第五冪になれないと示します。本定理は同じ body が実際には `x^5` であることを供給し、局所 valuation obstruction と Fermat 方程式を直接衝突させます。

## 直接依存する定義・補題

### `Fermat5Equation`

```lean
def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5
```

### `Body5`

```lean
def Body5 (g y : ℕ) : ℕ :=
  g * GN5 g y
```

### `body5_eq_add_pow_sub`

```lean
theorem body5_eq_add_pow_sub (g y : ℕ) :
    Body5 g y = (g + y) ^ 5 - y ^ 5
```

### `fifth_sub_eq_of_add_eq`

```lean
theorem fifth_sub_eq_of_add_eq
    {x y z : ℕ}
    (hEq : Fermat5Equation x y z) :
    z ^ 5 - y ^ 5 = x ^ 5
```

### `Nat.sub_add_cancel`

`hyz : y ≤ z` から `(z-y)+y=z` を得て、gap 座標を元の `z` へ戻します。

## 証明の流れ

1. `calc` で `Body5 (z-y) y` から `z^5-y^5`、さらに `x^5` へ進む中間点を固定する。
2. `body5_eq_add_pow_sub (z-y) y` を使い、body を `((z-y)+y)^5-y^5` に変える。
3. `Nat.sub_add_cancel hyz` により `(z-y)+y` を `z` へ簡約する。
4. `fifth_sub_eq_of_add_eq hEq` で差を `x^5` に置き換える。

## Lean 固有の処理

### 自然数減算と順序条件

`Nat` の減算は切り捨てです。`hyz : y ≤ z` は、`z-y` を数学的な非負 gap として扱い、`Nat.sub_add_cancel hyz` を使うために必要です。

### `simpa ... using`

先行定理の右辺は `((z-y)+y)^5-y^5` です。`simpa [Nat.sub_add_cancel hyz]` がその座標復元だけを行い、目標の `z^5-y^5` に一致させます。

### `calc`

二つの独立した bridge、すなわち「body から第五冪差」と「Fermat 方程式から差の評価」を明示的に連結します。

## 冗長・重複箇所

`fifth_sub_eq_of_add_eq` と `body5_eq_add_pow_sub` を単純に合成しており、新しい数論的内容はありません。しかし、後続定理が毎回 gap 復元と Fermat 方程式の減算を繰り返さずに済むため、重要な API 補題です。

`CounterexamplePack` からは `right_lt_of_fermat5Equation` を通じて `hyz` を導出できますが、本定理はより一般的に `Fermat5Equation` と順序条件だけを受け取ります。この分離は再利用性を高めています。

## 最適化候補

現行の `calc` は証明の数学的二段構造を最も明瞭に示します。一行化するなら次も候補です。

```lean
  simpa [Nat.sub_add_cancel hyz] using
    (body5_eq_add_pow_sub (z - y) y).trans (fifth_sub_eq_of_add_eq hEq)
```

ただし中間式の型合わせが読みにくくなり、Lean の elaboration に依存するため、現行版の方が監査しやすいです。

`hyz` を定理内部で `hEq` と `x>0` から導く案もありますが、ここでは `x>0` を仮定していません。現在の一般型を維持するのが適切です。

## 必要 Mathlib import と import 最適化候補

standalone 版は `import Mathlib` を使用しています。本定理自体が必要とするものは、自然数の累乗・減算、`Nat.sub_add_cancel`、等式推論、およびプロジェクト内の `Fermat5Equation`, `Body5`, `body5_eq_add_pow_sub`, `fifth_sub_eq_of_add_eq` です。

高度な algebra tactic は使っていません。実モジュールでは `Basic` と `GN5` を経由して必要宣言を得る import が本質です。最小 import の具体形は Lean ビルドを行っていないため未検証です。

## Comparator challenge 化の可否

初級から中級の challenge に適しています。

```lean
theorem body5_eq_fifth_power_of_fermat_challenge
    {x y z : ℕ}
    (hyz : y ≤ z)
    (hEq : Fermat5Equation x y z) :
    Body5 (z - y) y = x ^ 5 := by
  -- body の一般恒等式、gap の復元、Fermat 方程式を接続する
  sorry
```

比較対象は、現行 `calc`、`rw` 中心の証明、`simpa ... using` を一度にまとめる証明です。評価点は自然数減算の安全な扱いと、既存 bridge の再利用です。

## 根拠と推測の区別

宣言型、証明の二段構造、直接依存、ソース順序は、リポジトリ内の生成済み `Flt5DkMath/FLT5StandAlone.lean` に含まれる `DkMath/FLT/Five/BranchB.lean` 部分を根拠としています。

import 最小化案と一行証明案は未検証の設計提案です。本作業では Lean ビルドを行っていません。既存 PDF は証明全体の物語的背景として参照対象ですが、本記事の形式的根拠は Lean コードです。

## 次に読むべき宣言

次は `BranchB.lean` で本定理を消費し、clean channel が存在する場合に Fermat 反例を直接反証する定理です。正確な宣言名は次回、現在のブランチ上のソース順を再確認して確定します。
