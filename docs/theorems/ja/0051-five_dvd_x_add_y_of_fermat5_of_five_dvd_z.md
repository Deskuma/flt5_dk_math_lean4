# 0051 — `five_dvd_x_add_y_of_fermat5_of_five_dvd_z`

## 1. 対象宣言

```lean
theorem five_dvd_x_add_y_of_fermat5_of_five_dvd_z
    {x y z : ℕ} (hEq : Fermat5Equation x y z)
    (h5z : 5 ∣ z) :
    5 ∣ x + y := by
  have hEqNat : x ^ 5 + y ^ 5 = z ^ 5 := by
    simpa [Fermat5Equation] using hEq
  have hmod := congrArg (fun n : ℕ => n % 5) hEqNat
  have hz0 : z % 5 = 0 := Nat.mod_eq_zero_of_dvd h5z
  apply Nat.dvd_of_mod_eq_zero
  simpa [Nat.add_mod, pow_five_mod_five, hz0] using hmod
```

完全修飾名は `DkMath.FLT.Five.five_dvd_x_add_y_of_fermat5_of_five_dvd_z` である。

## 2. Lean の型

```lean
{ x y z : ℕ } →
Fermat5Equation x y z →
5 ∣ z →
5 ∣ x + y
```

自然数上の FLT5 方程式と `5 ∣ z` から、左辺の底の和 `x + y` が 5 で割り切れることを示す。

## 3. 数学的主張

仮定は

$$
x^5+y^5=z^5,\qquad 5\mid z
$$

である。法 5 へ移すと右辺は 0 となり、既刊 0049 の

$$
n^5\equiv n\pmod 5
$$

を使って

$$
x+y\equiv 0\pmod 5
$$

を得る。したがって

$$
5\mid(x+y)
$$

である。

これは前号 0050 の difference-gap 補題と対をなす。0050 は一方の左辺座標が 5 で割れる場合に `z-x` を作り、本定理は結果座標が 5 で割れる場合に符号付き和 `x+y` を作る。

## 4. 証明全体での役割

この定理は signed Branch A への **sum-gap routing bridge** である。後続の signed routing では Branch B 側の有限剰余類分類から得られる場合分けを、二種類の向きへ変換する。

```text
5 ∣ y
  → 5 ∣ z - x
  → SignedBranchAOrientation.differenceGap

5 ∣ z
  → 5 ∣ x + y
  → SignedBranchAOrientation.sumGap
```

特に後続の `signedBranchA_normalForm_of_branchB` では、`5 ∣ z` の場合に本定理を直接用いて `SignedBranchAOrientation.sumGap` を構成する。したがって、通常の Fermat 方程式を signed five-adic 降下が受け取れる「和 gap」の証拠へ変換する局所 adapter である。

## 5. 直接依存する定義・補題

- `Fermat5Equation`：`x^5 + y^5 = z^5` を表す入口定義。
- `pow_five_mod_five`：第五冪を法 5 で底へ落とす既刊 0049 の補題。
- `congrArg`：方程式の両辺へ `fun n => n % 5` を適用する。
- `Nat.mod_eq_zero_of_dvd`：`5 ∣ z` から `z % 5 = 0` を得る。
- `Nat.add_mod`：和の剰余を各項の剰余へ分解する。
- `Nat.dvd_of_mod_eq_zero`：剰余 0 を整除へ戻す。
- `simpa`：第五冪の剰余、和の剰余、`z % 5 = 0` を同時に正規化する。

`CounterexamplePack`、正値性、互いに素性には直接依存しない。方程式と `5 ∣ z` だけで閉じる。

## 6. 証明の流れ

1. `Fermat5Equation` を展開し、通常の自然数等式 `hEqNat` を得る。
2. `congrArg` で両辺に `% 5` を適用し、剰余等式 `hmod` を得る。
3. `h5z` から `hz0 : z % 5 = 0` を得る。
4. 目標を `Nat.dvd_of_mod_eq_zero` により `(x+y)%5=0` へ変える。
5. `Nat.add_mod`、`pow_five_mod_five`、`hz0` で `hmod` を簡約し、目標を閉じる。

## 7. Lean 固有の処理

`hEqNat` は定義包装を外すための中間等式である。`simpa [Fermat5Equation] using hEq` により、`congrArg` がそのまま使える形へ変換する。

`congrArg (fun n : ℕ => n % 5)` は、合同式専用の構造を導入せず、等式へ同じ関数を適用する一般原理で法 5 の等式を得ている。

`apply Nat.dvd_of_mod_eq_zero` により、整除目標を剰余 0 の目標へ前向きに変換する。その後の `simpa` は

```lean
Nat.add_mod
pow_five_mod_five
hz0
```

を一括して用い、`hmod` を目標形へ正規化する。

前号と異なり自然数減算を扱わないため、順序や切り詰め減算に関する注意は不要である。

## 8. 冗長・重複箇所

`hEqNat` と `hmod` は一つの式に圧縮できる。しかし、入口定義の展開と法 5 への写像を分離しており、監査性は高い。

前号 0050 と証明骨格が大きく重複する。双方とも、

1. `Fermat5Equation` を展開する。
2. `% 5` を両辺へ適用する。
3. 一座標の剰余を 0 にする。
4. `pow_five_mod_five` で第五冪を底へ落とす。

という共通核を持つ。

本定理の最後の `apply` と `simpa` は十分短く、局所的な冗長性はほとんどない。

## 9. 最適化候補

最も自然な共通化は、Fermat 方程式から

```lean
(x + y) % 5 = z % 5
```

を導く補題である。例えば次のような形が考えられる。

```lean
theorem add_mod_five_eq_of_fermat5
    {x y z : ℕ} (hEq : Fermat5Equation x y z) :
    (x + y) % 5 = z % 5 := by
  ...
```

これがあれば、本定理は `h5z` から右辺を 0 に置き換える短い consumer になる。前号 0050 も同じ共通核から構成できる。

別案として `Nat.ModEq 5 (x+y) z` を返す補題を置くこともできるが、現行コードは `%` 等式だけで閉じるため、抽象化による型変換コストとの比較が必要である。

この定理単独では現状がすでに簡潔であり、最適化の主眼は重複除去にある。

## 10. 必要 Mathlib import と import 最適化候補

生成済み standalone ソースは `import Mathlib` で検証されている。対象宣言は生成順上 `DkMath/FLT/Five/SignedBranchA.lean` に属する。

直接必要な Mathlib 機能は自然数の剰余、整除、`Nat.add_mod`、`congrArg`、`simpa` である。分割元モジュールの正確な import 行は対象リポジトリ内では確認できなかったため、次は推測を含む最小候補である。

- `Mathlib.Data.Nat.ModEq`
- `Mathlib.Data.Nat.Prime.Basic`
- `Mathlib.Tactic`

`Nat.Prime.Basic` はこの定理単独では不要である可能性が高く、同一モジュール内の前後宣言のために残っている候補である。厳密な import 最適化には分割元ソースを用いた単体ビルドが必要である。本回は Lean ビルドを行っていない。

## 11. Comparator challenge 化

適している。challenge は次の型に固定できる。

```lean
theorem challenge
    {x y z : ℕ} (hEq : Fermat5Equation x y z)
    (h5z : 5 ∣ z) :
    5 ∣ x + y := by
  ...
```

比較観点は次の通りである。

- `%` 等式を直接操作するか、`Nat.ModEq` を使うか。
- `pow_five_mod_five` を再利用するか、一般的なフェルマー小定理を用いるか。
- 前号との共通合同核を抽出するか、局所証明を独立させるか。
- `apply Nat.dvd_of_mod_eq_zero` とするか、完成した剰余等式を項として渡すか。

短いが、合同算術の API 設計と再利用方針を比較できる良い課題である。

## 12. 次に読むべき定理

次は

```lean
DkMath.FLT.Five.SignedBranchAOrientation
```

を読む。

これは exponent-five 方程式の例外的五進方向を、

- `differenceGap`
- `sumGap`

の二つの constructor で表す inductive interface である。本号と前号が供給した二種類の整除事実を、signed five-adic 降下へ渡す最初の構造化層となる。
