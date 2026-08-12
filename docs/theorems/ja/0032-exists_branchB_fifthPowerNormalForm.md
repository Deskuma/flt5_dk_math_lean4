# 0032 — `exists_branchB_fifthPowerNormalForm`

## 宣言

```lean
theorem exists_branchB_fifthPowerNormalForm
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    ∃ a b : ℕ, BranchBFifthPowerNormalForm x y z a b
```

## 数学的主張

正の原始的な第五冪方程式候補

$$
x^5+y^5=z^5
$$

が Branch B 条件

$$
5\nmid z-y
$$

を満たすなら、自然数 $a,b$ が存在し、次の完全な標準形が得られる。

$$
z-y=a^5,\qquad GN5(a^5,y)=b^5,
$$

$$
x=ab,\qquad z=y+a^5,
$$

$$
a>0,\qquad b>0,
$$

$$
\gcd(a,y)=\gcd(a,b)=\gcd(b,y)=1,
$$

$$
5\nmid a.
$$

これは前号の構造体 `BranchBFifthPowerNormalForm` に必要な全フィールドを実際に供給する存在定理である。

## 証明全体での役割

本定理は Reduction 層で得た因子分離を、後続層が直接消費できる単一の標準形パケットへ変換する provider である。後続の Branch B、square/golden bridge、さらに黄金整数側の処理は、元の `CounterexamplePack` から個別事実を再導出せず、この構造体を入口として利用できる。

したがって本定理は、新しい数論的障害を示すというより、既に証明された事実を正規化し、座標を $z-y$ から $a^5$ へ固定し、必要な副条件をキャッシュする証明工学上の結節点である。

## 直接依存する定義・補題

リポジトリ内で直接使われる主要宣言は次のとおりである。

- `CounterexamplePack`
- `BranchBFifthPowerNormalForm`
- `branchB_fifth_power_factor_split`
- `right_lt_of_fermat5Equation`
- `pow_five_sub_pow_five_eq_gap_mul_GN5`
- `fifth_sub_eq_of_add_eq`
- `gap_pos_of_fermat5Equation`
- `coprime_gap_y_of_counterexamplePack`
- `branchB_coprime_gap_GN5`
- `coprime_GN5_y_of_coprime`

Mathlib 側では、少なくとも次の一般補題・機構が現れる。

- `mul_pow`
- `Nat.pow_left_injective`
- `Nat.coprime_pow_left_iff`
- `Nat.coprime_pow_right_iff`
- `Nat.Coprime.pow_left`
- `dvd_pow_self`
- `omega`
- `rw`、`simpa`、`rcases`

## 証明の流れ

### 1. gap と `GN5` の第五冪根を取り出す

```lean
rcases branchB_fifth_power_factor_split hPack hBranch with
  ⟨⟨a, hgap⟩, ⟨b, hGN0⟩⟩
```

ここで、

$$
hgap:z-y=a^5,
$$

$$
hGN0:GN5(z-y,y)=b^5
$$

を得る。

### 2. `GN5` を正規化座標へ移す

```lean
have hGN : GN5 (a ^ 5) y = b ^ 5 := by
  simpa [hgap] using hGN0
```

構造体が要求するのは `GN5 (a^5) y` なので、gap の等式で書き換える。

### 3. full body を再構成する

`y≤z` を得て自然数差の因数分解を使い、

$$
(z-y)GN5(z-y,y)=x^5
$$

を構成する。

```lean
have hyz : y ≤ z :=
  (right_lt_of_fermat5Equation hPack.hx hPack.hEq).le
have hbody : (z - y) * GN5 (z - y) y = x ^ 5 := by
  rw [← pow_five_sub_pow_five_eq_gap_mul_GN5 hyz]
  exact fifth_sub_eq_of_add_eq hPack.hEq
```

### 4. $x=ab$ を回収する

$z-y=a^5$ と `GN5(z-y,y)=b^5` を代入すると、

$$
(ab)^5=x^5
$$

となる。第五冪写像の単射性から、

$$
x=ab
$$

を得る。

```lean
have hxpow : (a * b) ^ 5 = x ^ 5 := by
  rw [mul_pow, ← hgap, ← hGN0]
  exact hbody
have hx : x = a * b :=
  (Nat.pow_left_injective (by decide : 5 ≠ 0) hxpow).symm
```

### 5. $z=y+a^5$ を回収する

自然数差の等式 `hgap` と既知の順序から、`omega` が

$$
z=y+a^5
$$

を閉じる。

### 6. $a,b$ の正値性を示す

$a=0$ なら $z-y=a^5=0$ となり、既知の gap 正値性に矛盾する。

$b=0$ なら $x=ab=0$ となり、`hPack.hx : 0<x` に矛盾する。

### 7. 三つの互いに素性を第五冪から降ろす

まず、

$$
\gcd(a^5,y)=1
$$

を `coprime_gap_y_of_counterexamplePack` と `hgap` から得て、`Nat.coprime_pow_left_iff` で

$$
\gcd(a,y)=1
$$

へ降ろす。

次に、

$$
\gcd(a^5,b^5)=1
$$

を Branch B の gap–`GN5` 互いに素性から得て、左右の power-coprime iff を順に使い、

$$
\gcd(a,b)=1
$$

へ降ろす。

最後に `coprime_GN5_y_of_coprime` を `a^5` と $y$ に適用し、`hGN` で書き換えて、

$$
\gcd(b^5,y)=1
$$

から

$$
\gcd(b,y)=1
$$

を得る。

### 8. $5\nmid a$ を示す

$5\mid a$ と仮定すると $5\mid a^5$ であり、`hgap` により $5\mid z-y$ となる。これは Branch B 条件に矛盾する。

### 9. 構造体を構成する

最後に `a,b` と十二個のフィールド証明を順に渡して存在主張を閉じる。

```lean
exact ⟨a, b, hPack, hBranch, hgap, hGN, hx, hz,
  ha, hb, hay, hab, hby, h5a⟩
```

## Lean 固有の処理

### 自然数減算と順序証明

`z-y` は自然数の切り捨て減算であるため、差の因数分解を実際の $z,y$ に適用するには `y≤z` が必要である。本定理は `right_lt_of_fermat5Equation` の厳密不等式を `.le` で弱めている。

### `rw [← hgap]` の向き

`hxpow` の証明では `(a*b)^5` を `a^5*b^5` に展開した後、`← hgap` と `← hGN0` によって既知の full body へ戻す。正規形へ進む向きではなく、既に証明済みの `hbody` と一致させる向きで rewrite している。

### power-coprime iff の引数位置

`Nat.coprime_pow_left_iff` と `Nat.coprime_pow_right_iff` は、どちら側の冪を除去するかを型で明示する。`a^5` と `b^5` の双方を除去する箇所では二段階の適用が必要である。

### `Nat.pow_left_injective`

自然数上で指数 $5$ が非零であることを `by decide` で供給し、第五冪等式から底の等式を回収している。

## 冗長・重複箇所

確認できる重複は、第五冪指数の正値性・非零性を示す

```lean
(by decide : 0 < 5)
(by decide : 5 ≠ 0)
```

が複数回現れる点である。ただし定数指数なので実行コストは小さく、局所可読性との交換条件になる。

また `hbody` は前の `branchB_fifth_power_factor_split` 内でもほぼ同じ形で構成されている。現在の実装は各定理を独立に読める利点がある一方、同一の body bridge を再計算している。

## 最適化候補

以下は未検証の提案であり、現在の Lean ソースが誤っていることを意味しない。

1. `CounterexamplePack` から

$$
(z-y)GN5(z-y,y)=x^5
$$

を返す名前付き補題を抽出すれば、`branchB_fifth_power_factor_split` と本定理の重複を除ける。

2. 第五冪の coprime 降下をまとめる局所補題、例えば

```lean
Nat.Coprime (a ^ 5) (b ^ 5) → Nat.Coprime a b
```

の専用 wrapper があれば、二段の `.mp` を読みやすくできる。

3. `a_pos` は `hgap` と `gap_pos` から `Nat.pow_pos.mp` 系の既存 API で短縮できる可能性がある。ただし Mathlib v4.33.0 における最適な補題名は未検証である。

4. `b_pos` は `hx=x*a` 型の零積反証ではなく、`GN5(a^5,y)=b^5` と `GN5` の正値性から得る設計も考えられるが、現在の $x=ab$ 経路の方が依存が少ない。

## 必要 Mathlib import と import 最適化候補

確認済みの standalone 生成物は `import Mathlib` を使用しており、本定理は `omega`、自然数の冪、整除性、互いに素性、gcd monoid 周辺を必要とする。

元の分割ソース `NormalForm.lean` の個別 import 行は、この回に取得できたリポジトリ資料からは確認できなかった。したがって、次の細分化候補は推測である。

- `Mathlib.Data.Nat.GCD.Basic`
- `Mathlib.Algebra.GroupPower.Lemmas`
- `Mathlib.Tactic.Omega`
- 前段の DkMath モジュール `Reduction`

実際の import 最小化は `lake env lean` による検証が必要だが、本作業では Lean ビルドを行っていない。

## Comparator challenge 化

適している。特に次の三段階に分けられる。

1. **初級** — `hgap : z-y=a^5` と gap 正値性から `0<a` を示す。
2. **中級** — `hgap`、`hGN0`、full-body 等式から `x=a*b` を示す。
3. **上級** — `Coprime (a^5) (b^5)` から power-coprime iff を使って `Coprime a b` を回収する。

完全版は多数の依存を束ねるため challenge としては長いが、構造体 provider の設計比較には向いている。

## 根拠と推測の区別

定理型、証明手順、使用宣言、直後の宣言順は、リポジトリ内の生成済み `Flt5DkMath/FLT5StandAlone.lean` を根拠として確認した。import 細分化案と helper 抽出案は未検証の提案である。

## 次に読むべき宣言

```text
DkMath.FLT.Five.BranchBFifthPowerCore
```

これは elementary reduction 後に残る未知の算術核を、`BranchBFifthPowerNormalForm` を受け取って `False` を返す universal receiver として表す略称である。本定理が provider なら、次の宣言は後続証明が満たすべき consumer interface を定める。
