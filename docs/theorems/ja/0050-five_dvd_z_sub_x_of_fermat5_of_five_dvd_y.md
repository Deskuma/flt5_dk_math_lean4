# 0050 — `five_dvd_z_sub_x_of_fermat5_of_five_dvd_y`

## 1. 対象宣言

```lean
theorem five_dvd_z_sub_x_of_fermat5_of_five_dvd_y
    {x y z : ℕ} (hEq : Fermat5Equation x y z)
    (h5y : 5 ∣ y) :
    5 ∣ z - x := by
  have hEqNat : x ^ 5 + y ^ 5 = z ^ 5 := by
    simpa [Fermat5Equation] using hEq
  have hmod := congrArg (fun n : ℕ => n % 5) hEqNat
  have hy0 : y % 5 = 0 := Nat.mod_eq_zero_of_dvd h5y
  have hxz : x % 5 = z % 5 := by
    simpa [Nat.add_mod, pow_five_mod_five, hy0] using hmod
  exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hxz.symm)
```

完全修飾名は `DkMath.FLT.Five.five_dvd_z_sub_x_of_fermat5_of_five_dvd_y` である。

## 2. Lean の型

```lean
{ x y z : ℕ } →
Fermat5Equation x y z →
5 ∣ y →
5 ∣ z - x
```

自然数上の FLT5 方程式と `5 ∣ y` から、自然数の切り詰め減算で表した差 `z - x` が 5 で割り切れることを示す。

## 3. 数学的主張

仮定は

$$
x^5+y^5=z^5,\qquad 5\mid y
$$

である。法 5 では `y^5` が消え、既刊 0049 の

$$
n^5\equiv n\pmod 5
$$

を使うと

$$
x\equiv z\pmod 5
$$

を得る。したがって

$$
5\mid(z-x)
$$

である。

Lean の結論は整数差ではなく `Nat` の `z - x` である。ただし同じ剰余を持つ二自然数の切り詰め差も法 5 で 0 になるため、定理型だけなら `x ≤ z` を別途仮定する必要はない。

## 4. 証明全体での役割

この定理は signed Branch A への **difference-gap routing bridge** である。Branch B 候補について別の有限剰余類分類から `5 ∣ y` が得られた場合、左辺二項を交換した `CounterexamplePack.swap` と組み合わせて、交換後の自然 gap `z-x` が 5 で割れる向きを構成する。

後続の `signedBranchA_normalForm_of_branchB` では、

```text
5 ∣ y
  + CounterexamplePack.swap
  + 5 ∣ z - x
        ↓
SignedBranchAOrientation.differenceGap
```

という形で直接消費される。すなわち、法 5 の合同情報を signed five-adic 降下が受け取れる構造化された分岐証拠へ変換する局所補題である。

## 5. 直接依存する定義・補題

- `Fermat5Equation`：`x^5 + y^5 = z^5` を表す入口定義。
- `pow_five_mod_five`：第五冪を法 5 で底へ落とす既刊 0049 の補題。
- `congrArg`：方程式の両辺へ `fun n => n % 5` を適用する。
- `Nat.mod_eq_zero_of_dvd`：`5 ∣ y` から `y % 5 = 0` を得る。
- `Nat.add_mod`：和の剰余を各項の剰余へ分解する。
- `Nat.sub_mod_eq_zero_of_mod_eq`：二数の剰余が等しいとき、対応する自然差の剰余が 0 であることを示す。
- `Nat.dvd_of_mod_eq_zero`：剰余 0 を整除へ戻す。

`CounterexamplePack`、正値性、互いに素性には直接依存しない。方程式と `5 ∣ y` だけで閉じる。

## 6. 証明の流れ

1. `Fermat5Equation` を展開し、通常の自然数等式 `hEqNat` を得る。
2. `congrArg` で両辺に `% 5` を適用し、法 5 の等式 `hmod` を作る。
3. `h5y` から `hy0 : y % 5 = 0` を得る。
4. `Nat.add_mod`、`pow_five_mod_five`、`hy0` で `hmod` を簡約し、`hxz : x % 5 = z % 5` を得る。
5. `hxz.symm` から `(z-x)%5=0` を作り、`Nat.dvd_of_mod_eq_zero` で `5 ∣ z-x` に戻す。

## 7. Lean 固有の処理

`hEqNat` は定義包装を外すための中間等式である。`simpa [Fermat5Equation] using hEq` により、後続の `congrArg` が扱いやすい通常の等式へ変換している。

`congrArg (fun n : ℕ => n % 5)` は合同式専用 API を使わず、等式へ同じ関数を適用する一般原理で法 5 の情報を得る。

最後に `hxz.symm` が必要なのは、目標が `z - x` だからである。補題 `Nat.sub_mod_eq_zero_of_mod_eq` へ `z % 5 = x % 5` の向きを渡すため、`x % 5 = z % 5` を反転している。

`Nat` の減算は切り詰め減算だが、ここでは剰余一致から直接整除を出しており、順序証明を挟まない。

## 8. 冗長・重複箇所

`hEqNat` は一行で `congrArg` と定義展開を合成できるため、論理的には省略可能である。しかし、方程式の包装解除と法 5 への写像を分離することで監査しやすくなっている。

`hmod` と `hxz` も一つの `have` に圧縮できるが、第五冪方程式の剰余等式と、底の剰余一致という異なる意味段階を分離しているため、現状の分解は妥当である。

後続の `five_dvd_x_add_y_of_fermat5_of_five_dvd_z` と証明骨格が重複する。双方とも方程式を `% 5` へ写し、`pow_five_mod_five` と一座標の剰余 0 を使う。

## 9. 最適化候補

最も自然な抽象化候補は、第五冪方程式から底の法 5 関係

```lean
(x + y) % 5 = z % 5
```

を一度だけ導く共通補題である。これを用いれば、本定理と次の和 gap 補題は、一座標の剰余を 0 に置換する短い consumer になる。

一方、局所定理が現在のまま独立していることで、依存関係と各方向の数学的意味は明瞭である。共通化による短縮量は小さいため、重複除去を優先する場合にのみ検討すべきである。

`Nat.ModEq 5 x z` を中間表現に採用する案もあるが、現在は `%` 等式だけで短く閉じており、型変換を増やす利点は限定的である。

## 10. 必要 Mathlib import と import 最適化候補

生成済み standalone ソースは `import Mathlib` で検証されている。対象宣言は生成順上 `DkMath/FLT/Five/SignedBranchA.lean` に属することも確認できる。

直接必要な Mathlib 機能は自然数の剰余、整除、`Nat.add_mod`、自然差の剰余補題、および `simpa` である。分割元モジュールの実ファイルはこのリポジトリには収録されておらず、正確な import 行は確認できなかった。したがって、次は推測を含む最小候補である。

- `Mathlib.Data.Nat.ModEq`
- `Mathlib.Data.Nat.Prime.Basic`
- `Mathlib.Tactic`

実際の import 最適化には分割元ソースを用いた単体ビルドが必要である。本回は Lean ビルドを行っていない。

## 11. Comparator challenge 化

適している。challenge は次の型に固定できる。

```lean
theorem challenge
    {x y z : ℕ} (hEq : Fermat5Equation x y z)
    (h5y : 5 ∣ y) :
    5 ∣ z - x := by
  ...
```

比較観点は次の通りである。

- `%` 等式を直接操作するか、`Nat.ModEq` を使うか。
- `pow_five_mod_five` を再利用するか、一般的なフェルマー小定理を用いるか。
- `x ≤ z` を導いて整数的な差として扱うか、自然差の剰余補題で順序を回避するか。
- 次の和 gap 補題と共通核を抽出するか。

短いが、自然数減算、合同式、API 選択の差が現れる良い比較課題である。

## 12. 次に読むべき定理

次は

```lean
DkMath.FLT.Five.five_dvd_x_add_y_of_fermat5_of_five_dvd_z
```

を読む。

これは `5 ∣ z` の場合に同じ法 5 正規化を用いて

$$
5\mid(x+y)
$$

を導き、signed Branch A の `sumGap` 方向を供給する対になる定理である。