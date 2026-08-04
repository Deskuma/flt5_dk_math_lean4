# 0028 — `branchB_fifth_power_factor_split`

## 宣言

```lean
theorem branchB_fifth_power_factor_split
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    (∃ a : ℕ, z - y = a ^ 5) ∧
      (∃ b : ℕ, GN5 (z - y) y = b ^ 5) := by
  have hyz : y ≤ z := (right_lt_of_fermat5Equation hPack.hx hPack.hEq).le
  have hbody : (z - y) * GN5 (z - y) y = x ^ 5 := by
    rw [← pow_five_sub_pow_five_eq_gap_mul_GN5 hyz]
    exact fifth_sub_eq_of_add_eq hPack.hEq
  exact fifth_power_factor_split (branchB_coprime_gap_GN5 hPack hBranch) hbody
```

## Lean の型

この定理は、正の原始的な FLT5 反例候補 `hPack` と Branch B 条件 `5 ∤ z-y` を受け取り、第五冪差の二因子をそれぞれ完全第五冪として返す。

```lean
CounterexamplePack x y z →
  (¬ 5 ∣ z - y) →
  ((∃ a : ℕ, z - y = a ^ 5) ∧
    (∃ b : ℕ, GN5 (z - y) y = b ^ 5))
```

## 数学的主張

`CounterexamplePack` から

$$
x^5+y^5=z^5
$$

が得られる。$y<z$ なので自然数差は通常の差として働き、第五冪差の因数分解により

$$
x^5=z^5-y^5=(z-y)GN5(z-y,y)
$$

となる。

Branch B の仮定

$$
5\nmid z-y
$$

と原始性から、既出の定理 `branchB_coprime_gap_GN5` は

$$
\gcd\bigl(z-y,GN5(z-y,y)\bigr)=1
$$

を与える。互いに素な二因子の積が第五冪なので、前号 `fifth_power_factor_split` により、ある $a,b\in\mathbb N$ が存在して

$$
z-y=a^5,
\qquad
GN5(z-y,y)=b^5
$$

となる。

## 証明全体での役割

本定理は Branch B の算術情報を **exact elementary normal form** へ変換する境界定理である。

前段では、反例方程式を gap と `GN5` の積へ分解し、Branch B 条件の下で二因子の互いに素性を確立した。本定理はそれらを一般冪分離エンジンへ入力し、後続層が直接扱える二つの第五冪方程式へ変換する。

この時点で Branch B の否定に必要なのは、`GN5 (z-y) y` が第五冪ではあり得ないという独立な障害だけになる。直後の `branchB_false_of_GN5_not_fifth_power` は、本定理の第二成分をその障害へ渡す。

## 直接依存する定義・補題

1. `CounterexamplePack`
   - 正値性、`Nat.Coprime x y`、方程式 `Fermat5Equation x y z` を保持する。
2. `right_lt_of_fermat5Equation`
   - `hPack.hx` と `hPack.hEq` から $y<z$ を得る。
3. `pow_five_sub_pow_five_eq_gap_mul_GN5`
   - $y\le z$ の下で $z^5-y^5=(z-y)GN5(z-y,y)$ を与える。
4. `fifth_sub_eq_of_add_eq`
   - FLT5 方程式を $z^5-y^5=x^5$ へ変換する。
5. `branchB_coprime_gap_GN5`
   - `hPack` と `5∤z-y` から gap と `GN5` の互いに素性を与える。
6. `fifth_power_factor_split`
   - 互いに素な二因子の積が第五冪なら、各因子も第五冪であることを返す。

## 証明の流れ

1. `right_lt_of_fermat5Equation` から $y<z$ を得て `.le` で $y\le z$ へ弱める。

```lean
have hyz : y ≤ z :=
  (right_lt_of_fermat5Equation hPack.hx hPack.hEq).le
```

2. 第五冪差の因数分解を逆向きに rewrite し、反例方程式の差分形を使って積の恒等式を作る。

```lean
have hbody : (z - y) * GN5 (z - y) y = x ^ 5 := by
  rw [← pow_five_sub_pow_five_eq_gap_mul_GN5 hyz]
  exact fifth_sub_eq_of_add_eq hPack.hEq
```

3. Branch B の互いに素性と `hbody` を `fifth_power_factor_split` に渡す。

```lean
exact fifth_power_factor_split
  (branchB_coprime_gap_GN5 hPack hBranch) hbody
```

4. 一般定理の返値が目標と同型なので、追加の分解・再構成なしに終了する。

## Lean 固有の処理

### 自然数減算のための順序証明

`Nat` の減算は切り捨て減算である。そのため、抽象的な差の因数分解を実際の `z-y` へ接続する補題は `y ≤ z` を要求する。`CounterexamplePack` にこの順序は直接保存されていないので、方程式と `x>0` から導出している。

### rewrite の向き

目標 `hbody` の左辺を第五冪差へ変えるため、

```lean
rw [← pow_five_sub_pow_five_eq_gap_mul_GN5 hyz]
```

と定理を逆向きに使う。rewrite 後の目標は `z^5-y^5=x^5` となり、`fifth_sub_eq_of_add_eq` と完全に一致する。

### 構造体射影

`hPack.hx` と `hPack.hEq` を直接渡すことで、正値性と方程式の供給元を明示している。`hPack` 全体は互いに素性定理にもそのまま渡される。

### 結論形の一致

`fifth_power_factor_split` の一般変数 `g,n` は、型推論により `z-y` と `GN5 (z-y) y` に決まる。返される連言は本定理の目標そのものであり、`simpa` は不要である。

## 冗長・重複箇所

本定理自身には素因数反証や多項式展開の重複はない。既出 API を三段で合成する薄い orchestration theorem である。

ただし `hyz` と `hbody` の構成は、後続の normal-form provider でも似た形で再登場する可能性がある。実際に同一の証明断片が複数モジュールへ現れるなら、`CounterexamplePack` から

```lean
(z - y) * GN5 (z - y) y = x ^ 5
```

を返す専用補題へ抽出する価値がある。現時点では本記事が確認した範囲に基づく最適化提案であり、全リポジトリでの重複数は未検証である。

## 最適化候補

1. `counterexamplePack_gap_mul_GN5_eq_fifth` のような専用補題を設け、`hyz` と `hbody` の二段を共通化できる。
2. 現在の proof は依存関係が明確で、変更耐性も高い。短縮のみを目的とした tactic 圧縮は推奨しない。
3. `have hyz` を `hbody` 内へインライン化できるが、自然数減算の安全条件が見えにくくなる。
4. 結論を専用構造体として束ねる後続 normal form が主要 API なら、本定理は elementary bridge として残し、構造体版を別定理にする現在の階層が適切である。

## 必要 Mathlib import と import 最適化候補

standalone 生成物は `import Mathlib` を使用しており、本定理単独の最小 import は確認されていない。

本定理が直接必要とする機能は、自然数の順序・減算・冪、`Nat.Coprime`、gcd/単元を用いる前号の冪分離定理、およびリポジトリ内の `Basic`・`GN5`・`Reduction` 宣言である。実際のモジュールでは前段宣言を import すれば Mathlib 依存の多くは推移的に供給される可能性が高い。

最小化を行う場合は、次を個別に検証する必要がある。

1. 自然数の冪と順序・減算。
2. gcd と `Nat.Coprime`。
3. `GCDMonoid`、`IsUnit`、`exists_eq_pow_of_mul_eq_pow`。
4. `rw` が利用する等式補題群。

正確な Mathlib モジュール名と十分性は、Lean ビルドを行っていないため未検証である。

## Comparator challenge 化の可否

適している。個々の算術は短いが、既存 API を正しい順序で合成できるかを比較できる。

### 課題案

```lean
{x y z : ℕ}
(hPack : CounterexamplePack x y z)
(hBranch : ¬ 5 ∣ z - y)
⊢ (∃ a : ℕ, z - y = a ^ 5) ∧
    (∃ b : ℕ, GN5 (z - y) y = b ^ 5)
```

比較候補は次の通り。

1. 現行の三補題合成版。
2. `calc` で第五冪 body 恒等式を構成する版。
3. 因数分解と互いに素性を再証明する自前版。
4. 専用 `CounterexamplePack` body 補題を先に作る版。
5. 結論を normal-form 構造体へ直接梱包する版。

評価軸は、依存の再利用率、自然数減算の安全性、証明長、局所補題の意味の明瞭さ、Mathlib 変更への耐性である。Comparator としては、短い自前証明より既存の証明済み API を正確に発見して合成する能力が重視される。

## 根拠と推測の区別

宣言の型、証明本体、使用する直接依存、直後に `branchB_false_of_GN5_not_fifth_power` が続くことは、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` で確認した。

本定理を exact elementary normal form の境界とみなす説明は、ソースコメントと後続宣言の構造に基づく解釈である。専用 body 補題への抽出、最小 import、Comparator の別解候補は未検証提案である。既存 PDF は補助的な物語資料であり、Lean 宣言と食い違う場合は Lean ソースを正本とする。

## 次に読むべき定理

```lean
DkMath.FLT.Five.branchB_false_of_GN5_not_fifth_power
```

これは任意に与えられた

$$
\neg\exists b\in\mathbb N,
\quad GN5(z-y,y)=b^5
$$

という `GN5` の第五冪排除証明と、本定理が供給する第二成分を直接衝突させ、Branch B の反例候補から `False` を導く消費定理である。
