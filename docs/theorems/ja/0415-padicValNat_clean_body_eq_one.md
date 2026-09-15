# 0415 `padicValNat_clean_body_eq_one`

## 宣言種別

`theorem`

## Lean の型

```lean
theorem padicValNat_clean_body_eq_one
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    padicValNat q (g * GN5 g y) = 1 := by
  letI : Fact (Nat.Prime q) := ⟨h.prime⟩
  have hBodyNe : g * GN5 g y ≠ 0 := by
    intro hzero
    apply h.not_sq_dvd_body
    rw [hzero]
    exact dvd_zero _
  apply Nat.le_antisymm (padicValNat_clean_body_upper_bound h)
  exact (@padicValNat_dvd_iff_le q (Fact.mk h.prime)
    (g * GN5 g y) 1 hBodyNe).mp (by simpa using h.dvd_body)
```

この theorem は、`CleanGN5Channel g y q` が与えられたとき、full fifth-power body

```lean
g * GN5 g y
```

における素数 `q` の `padicValNat` が正確に 1 であることを示す。

## 数学的主張

`CleanGN5Channel g y q` には、少なくとも次の二つの full-body 事実が既に備わっている。

```lean
h.dvd_body : q ∣ g * GN5 g y
h.not_sq_dvd_body : ¬ q ^ 2 ∣ g * GN5 g y
```

前者から

$$
q\mid g\,GN_5(g,y)
$$

なので、body が非零である限り

$$
1\le v_q(g\,GN_5(g,y))
$$

を得る。

一方、0414 `padicValNat_clean_body_upper_bound` は後者を使って

$$
v_q(g\,GN_5(g,y))\le1
$$

を既に証明している。

従って反対向きの二つの不等式から

$$
v_q(g\,GN_5(g,y))=1
$$

となる。

Lean 上ではこの二方向を

```lean
Nat.le_antisymm
```

で結合して等号を得ている。

## 証明全体での役割

0413 `padicValNat_lower_bound_d5` は、素数 `q` が正の自然数 `x` を割るなら

$$
5\le v_q(x^5)
$$

を与える。

0414 `padicValNat_clean_body_upper_bound` は clean channel の body に対して

$$
v_q(g\,GN_5(g,y))\le1
$$

を与えた。

0415 はさらに `h.dvd_body` を使って下界も加え、clean body の局所指数を

$$
v_q(g\,GN_5(g,y))=1
$$

まで鋭化する。

この exact valuation が、直後の

```lean
counterexample_false_of_clean_GN5Channel_by_padicValNat
```

で直接使われる。そこでは Fermat-five の body identity

$$
(z-y)GN_5(z-y,y)=x^5
$$

によって同じ自然数を一方では第五冪、もう一方では clean body として読む。

第五冪側では

$$
5\le v_q(x^5),
$$

clean-body 側では

$$
v_q((z-y)GN_5(z-y,y))=1.
$$

body identity で両者を同一視すると

$$
5\le1
$$

に帰着して矛盾する。

従って 0415 は valuation route における **exact local multiplicity certificate** であり、0413 の第五冪側 lower bound と最終 contradiction theorem を接続する中心補題である。

## 直接依存する定義・補題

### `CleanGN5Channel`

`CleanGN5Channel g y q` は、素数 `q` が `GN5 g y` に現れ、gap `g` には現れず、`GN5 g y` では二乗まで持ち上がらない clean prime channel を表す。

0415 が直接利用するのは次である。

```lean
h.prime : Nat.Prime q
h.dvd_body : q ∣ g * GN5 g y
h.not_sq_dvd_body : ¬ q ^ 2 ∣ g * GN5 g y
```

`h.dvd_body` が付値の下界を、`h.not_sq_dvd_body` が 0414 を経由して上界を供給する。

### `padicValNat_clean_body_upper_bound`

直前の 0414。

```lean
padicValNat_clean_body_upper_bound h :
  padicValNat q (g * GN5 g y) ≤ 1
```

0415 はこの theorem をそのまま `Nat.le_antisymm` の第一引数に渡す。

### `padicValNat_dvd_iff_le`

非零な自然数 `n` に対して、概念的には

$$
q^k\mid n
\Longleftrightarrow
k\le v_q(n)
$$

を結ぶ Mathlib の bridge theorem である。

0415 では `k = 1` として `.mp` 方向を使い、

```lean
q ∣ g * GN5 g y
```

から

```lean
1 ≤ padicValNat q (g * GN5 g y)
```

を得る。

### `Nat.le_antisymm`

自然数順序の反対向きの不等式

```lean
v ≤ 1
1 ≤ v
```

から

```lean
v = 1
```

を構成する。

## 証明または構築の流れ

### 1. 素数性を typeclass instance にする

```lean
letI : Fact (Nat.Prime q) := ⟨h.prime⟩
```

`padicValNat` 周辺の Mathlib API が要求する素数性を局所 instance として供給する。

### 2. full body の非零性を得る

```lean
have hBodyNe : g * GN5 g y ≠ 0 := by
  intro hzero
  apply h.not_sq_dvd_body
  rw [hzero]
  exact dvd_zero _
```

もし body が 0 なら

$$
q^2\mid0
$$

なので `h.not_sq_dvd_body` に反する。

この非零証明は 0414 と完全に同じである。

### 3. 0414 から上界を取得する

```lean
apply Nat.le_antisymm (padicValNat_clean_body_upper_bound h)
```

目標

```lean
padicValNat q (g * GN5 g y) = 1
```

に `Nat.le_antisymm` を適用し、第一方向

```lean
padicValNat q (g * GN5 g y) ≤ 1
```

を 0414 で即座に閉じる。

残る目標は

```lean
1 ≤ padicValNat q (g * GN5 g y)
```

だけになる。

### 4. body divisibility を valuation lower bound に変換する

```lean
exact (@padicValNat_dvd_iff_le q (Fact.mk h.prime)
  (g * GN5 g y) 1 hBodyNe).mp (by simpa using h.dvd_body)
```

`h.dvd_body` は

```lean
q ∣ g * GN5 g y
```

という形であり、`padicValNat_dvd_iff_le` の `k = 1` 側は

```lean
q ^ 1 ∣ g * GN5 g y
```

を期待する。

`simpa` が `q ^ 1 = q` を正規化し、必要な divisibility を渡す。

その後 `.mp` によって

$$
1\le v_q(g\,GN_5(g,y))
$$

を得て、antisymmetry が等号を完成させる。

## Lean 固有の処理

### 1. proposition から `Fact` instance への再包装

```lean
letI : Fact (Nat.Prime q) := ⟨h.prime⟩
```

は数学上の新しい仮定ではない。`h.prime` を typeclass search が利用できる形へ変えているだけである。

### 2. `@` による implicit / instance 引数の明示

```lean
@padicValNat_dvd_iff_le q (Fact.mk h.prime)
  (g * GN5 g y) 1 hBodyNe
```

と書くことで、Mathlib theorem の暗黙引数を全て露出させて適用形を固定している。

0413・0414・0415 が同じ形式を共有しているため、この valuation section の証明スタイルは統一されている。

### 3. `.mp` と 0414 の `.mpr` の対称性

0414 は

$$
2\le v_q(body)
\Longrightarrow q^2\mid body
$$

を得るため `.mpr` を使った。

0415 は逆に

$$
q\mid body
\Longrightarrow1\le v_q(body)
$$

を得るため `.mp` を使う。

同じ equivalence theorem の両方向が隣接する二つの theorem で使われており、valuation/divisibility correspondence が非常に明瞭に表れている。

### 4. `simpa` による `q ^ 1` の消去

`h.dvd_body` は `q ∣ body`、bridge theorem は `q ^ 1 ∣ body` を要求するため、

```lean
by simpa using h.dvd_body
```

が指数 1 の正規化を吸収している。

### 5. `Nat.le_antisymm`

この証明では `omega` や `linarith` は不要である。上界と下界が既に明示的に得られるので、順序の反対称性だけで exact valuation が構成できる。

## 冗長・重複箇所

### `hBodyNe` が 0414 と完全に重複する

0414 と 0415 は共に次を持つ。

```lean
have hBodyNe : g * GN5 g y ≠ 0 := by
  intro hzero
  apply h.not_sq_dvd_body
  rw [hzero]
  exact dvd_zero _
```

これは明確な局所重複である。

`CleanGN5Channel.body_ne` のような helper theorem を `CleanChannel.lean` 側に置けば、両方を簡潔にできる。

### `letI` と `Fact.mk h.prime` の重複

局所 instance を登録した後にも

```lean
Fact.mk h.prime
```

を明示的に渡している。

証明の安定性を優先した書き方と考えられるが、typeclass inference が十分なら簡略化できる可能性がある。

### exact-one theorem の論理自体は薄い

0415 の数学的中身は

```text
upper bound ≤ 1
+ divisibility gives lower bound ≥ 1
= exact valuation 1
```

であるため、0414 より新しい算術内容は少ない。

ただし最終 contradiction theorem から見ると `= 1` という API は極めて使いやすく、wrapper theorem として残す価値は高い。

## 最適化候補

### 1. `CleanGN5Channel.body_ne` を追加する

最も明確な最適化候補である。

概念的には

```lean
theorem CleanGN5Channel.body_ne
    (h : CleanGN5Channel g y q) :
    g * GN5 g y ≠ 0 := by
  intro hzero
  apply h.not_sq_dvd_body
  rw [hzero]
  exact dvd_zero _
```

を一度だけ証明すれば、0414 と 0415 の重複を除去できる。

### 2. exact valuation を clean-channel 基本 API へ寄せる

`CleanGN5Channel` は意味論的に「body で局所指数がちょうど 1」の channel である。

従って valuation API を主要な公開 interface として重視するなら、`padicValNat_clean_body_eq_one` を `CleanChannel.lean` 近くへ移す設計も考えられる。

一方、現状は direct divisibility contradiction と valuation contradiction を独立 route として分離する構成なので、`Valuation.lean` に置く現在の設計にも明確な理由がある。

### 3. bridge theorem 適用の boilerplate を helper 化する

0413〜0415 はすべて `Fact` と `padicValNat_dvd_iff_le` を明示的に扱う。

例えば「prime + divisibility + nonzero から valuation ≥ 1」を局所 helper にすればコード量は減る。

ただしこの三 theorem は短く、Mathlib bridge を直接見せる教育的価値もあるため必須ではない。

### 4. `simpa using h.dvd_body` の意図を明示する named fact を置く

例えば

```lean
have hqPowOne : q ^ 1 ∣ g * GN5 g y := by
  simpa using h.dvd_body
```

と分ければ初心者には読みやすくなるが、現行の一行形式の方が簡潔である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

0415 が直接必要とする Mathlib 機能は少なくとも次である。

- `padicValNat`
- `padicValNat_dvd_iff_le`
- `Fact`
- `Nat.Prime`
- `Nat.le_antisymm`
- 自然数の divisibility / power simplification

ただし、このリポジトリで固定されている Mathlib 版に対する **正確な最小 import 集合は未確認** である。今回 Lean build は実行していないため、`import Mathlib` をどの個別 module 群まで安全に縮小できるかは断定できない。

import 最適化を行うなら、まず `Valuation.lean` 単独で必要な `padicValNat` API の定義元 module を特定し、その後 clean-channel / GN5 側の import を足す方法が安全である。

## Comparator challenge 化の可否

**可能。小〜中規模 challenge として適している。**

候補となる challenge は次である。

> `CleanGN5Channel g y q` から、`padicValNat q (g * GN5 g y) = 1` を証明せよ。既存の upper-bound theorem は使用してよい。

必要な発想は三つだけである。

1. `not_sq_dvd_body` から body 非零性を作る。
2. 0414 から `v_q(body) ≤ 1` を得る。
3. `dvd_body` と `padicValNat_dvd_iff_le` から `1 ≤ v_q(body)` を得て `Nat.le_antisymm` する。

より難しい challenge にするなら 0414 の利用を禁止し、`h.not_sq_dvd_body` から upper bound もその場で再構築させればよい。この場合、`padicValNat_dvd_iff_le` の両方向を一つの課題で扱える。

一方、数学的創造性より Mathlib API の扱いが主題になるため、研究型 Comparator challenge より **Lean API / proof-refactoring challenge** としての適性が高い。

## 次に読むべき宣言

次は 0416 `counterexample_false_of_clean_GN5Channel_by_padicValNat`。

```lean
theorem counterexample_false_of_clean_GN5Channel_by_padicValNat
    {x y z q : ℕ}
    (hPack : CounterexamplePack x y z)
    (hClean : CleanGN5Channel (z - y) y q) :
    False := by
  have hyz : y ≤ z := Nat.le_of_lt (right_lt_of_fermat5Equation hPack.hx hPack.hEq)
  have hBodyEq : Body5 (z - y) y = x ^ 5 :=
    body5_eq_fifth_power_of_fermat hyz hPack.hEq
  have hqDivPow : q ∣ x ^ 5 := by
    rw [← hBodyEq]
    exact hClean.dvd_body
  have hqDivX : q ∣ x := hClean.prime.dvd_of_dvd_pow hqDivPow
  have hlower : 5 ≤ padicValNat q (x ^ 5) :=
    padicValNat_lower_bound_d5 hPack.hx hClean.prime hqDivX
  have hexact : padicValNat q (Body5 (z - y) y) = 1 := by
    simpa [Body5] using padicValNat_clean_body_eq_one hClean
  rw [hBodyEq] at hexact
  omega
```

0416 は 0413 と 0415 を Fermat-five の body identity 上で直接衝突させる theorem である。

構造は

$$
\text{Fermat body}=x^5,
$$

$$
5\le v_q(x^5),
$$

$$
v_q(\text{Fermat body})=1
$$

を一つに重ねるだけであり、`Valuation.lean` の独立 proof route はここで完成する。