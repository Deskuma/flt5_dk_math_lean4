# 0309 — `GoldenZeroSectorCandidate.factor_product`

## 宣言種別

これは **`theorem`** である。

0308 `GoldenZeroSectorCandidate.factor_product_twenty` で得た

$$
A B = 20s^4
$$

を、zero-sector candidate が保持する符号除去式と fifth-power mass `Q` の定義を用いて

$$
A B = 4Q^5
$$

へ正規化する。`SignedGoldenZeroSectorInversion` のモジュール説明でも、この等式は certified inversion の中心式として明示されている。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- Central fifth-power product of the positive inversion factors. -/
theorem factor_product (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d =
      4 * (zeroSectorQ p.c : ℤ) ^ 5 := by
  calc
    zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d =
        20 * p.s ^ 4 := p.factor_product_twenty
    _ = 4 * (zeroSectorQ p.c : ℤ) ^ 5 := by
      rw [p.s_eq_neg_five_pow_mul_tenth]
      unfold zeroSectorQ
      push_cast
      ring
```

結論は整数上の等式である。

$$
A(r,s,d)B(r,s,d)=4Q(c)^5.
$$

ここで

$$
Q(c)=5^5c^8.
$$

## 数学的意味

0308 では

$$
AB=20s^4
$$

まで到達した。candidate の sign removal theorem は

$$
s=-5^6c^{10}
$$

を与えるので、四乗すると符号が消えて

$$
s^4=5^{24}c^{40}
$$

となる。従って

$$
20s^4=20\cdot 5^{24}c^{40}
      =4\cdot 5^{25}c^{40}.
$$

一方、

$$
Q=5^5c^8
$$

だから

$$
Q^5=5^{25}c^{40}.
$$

ゆえに

$$
20s^4=4Q^5,
$$

したがって

$$
AB=4Q^5
$$

を得る。

この theorem の本質は、単なる積 `20*s^4` を「小さい 2-adic coefficient `4` と完全 fifth power `Q^5`」へ再編成する点にある。後続の gcd 分解や 2-adic branch analysis にとって、この形が直接扱いやすい。

## 証明全体での役割

本 theorem は zero-sector inversion の中心的な正規化点である。

0307 `discriminant_eq` で quartic identity を差平方

$$
U^2-W^2=20s^4
$$

へ変換し、0308 `factor_product_twenty` で

$$
AB=20s^4
$$

という multiplicative form にした。本 0309 はさらに candidate 固有の tenth-power split を反映して

$$
AB=4Q^5
$$

へ変換する。

これにより後続は `s` の巨大な冪を直接追う必要がなくなり、二つの inversion factor `A`,`B` の積が fifth power にほぼ等しいという情報を利用できる。

モジュール冒頭の説明にも

```text
A*B = 4*Q^5 for Q = 5^5*c^8
```

と明記されており、これは inversion packet の主要保存量の一つである。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate.factor_product_twenty`

```lean
theorem factor_product_twenty (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d =
      20 * p.s ^ 4
```

本 theorem の第一段階をそのまま供給する直前の theorem である。

### `GoldenZeroSectorCandidate.s_eq_neg_five_pow_mul_tenth`

```lean
theorem s_eq_neg_five_pow_mul_tenth (p : GoldenZeroSectorCandidate) :
    p.s = -((5 : ℤ) ^ 6 * (p.c : ℤ) ^ 10)
```

`GoldenZeroSectorCandidate` が保持する

```lean
s_natAbs_eq : s.natAbs = 5 ^ 6 * c ^ 10
```

と `s < 0` から、`s` の符号を完全に復元した先行 theorem である。本 proof はこの等式を `rw` して `s^4` を `c` の冪へ変える。

### `zeroSectorQ`

```lean
def zeroSectorQ (c : ℕ) : ℕ :=
  5 ^ 5 * c ^ 8
```

fifth-power mass

$$
Q=5^5c^8
$$

を定義する。`Q^5=5^25 c^40` となり、`20*s^4` の 5-adic 部分をちょうど吸収する指数設計になっている。

### `zeroSectorA`, `zeroSectorB`

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d

def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

本 theorem の左辺を構成する二つの inversion factor である。

### `push_cast`

`zeroSectorQ p.c : ℤ` の中にある自然数演算を整数側へ押し出し、`ring` が一つの可換環恒等式として処理できる形にする。

### `ring`

指数を含む整数多項式恒等式を正規化し、

$$
20(-5^6c^{10})^4=4(5^5c^8)^5
$$

を閉じる。

## 証明または構築の流れ

1. `calc` の最初の段で 0308 `p.factor_product_twenty` を直接適用し、

$$
AB=20s^4
$$

へ移る。
2. `rw [p.s_eq_neg_five_pow_mul_tenth]` により `s` を

$$
-5^6c^{10}
$$

へ置換する。
3. `unfold zeroSectorQ` により右辺の `Q` を

$$
5^5c^8
$$

へ展開する。
4. `push_cast` により `p.c : ℕ` に由来する自然数演算を整数演算へ整理する。
5. `ring` が指数法則と係数計算を正規化し、`20*s^4 = 4*Q^5` を閉じる。
6. 以上を `calc` で合成して最終式 `A*B = 4*Q^5` を得る。

## Lean 固有の処理

重要なのは `zeroSectorQ : ℕ → ℕ` であるのに対し、積 `A*B` は `ℤ` 上にある点である。そのため theorem の右辺は

```lean
4 * (zeroSectorQ p.c : ℤ) ^ 5
```

と明示的な cast を含む。

`unfold zeroSectorQ` の後には `5 ^ 5 * p.c ^ 8` が自然数側から整数へ cast された形で現れるため、`ring` の前に `push_cast` を挟むことで cast を積・冪の内部へ分配している。

また `rw [p.s_eq_neg_five_pow_mul_tenth]` により符号を含む exact equality を使うが、指数が 4 なので最終的には負号は消える。Lean ではこの偶数冪の処理も `ring` にまとめて任せている。

## 冗長・重複箇所

proof は短く、局所的な重複はほとんどない。

ただし数学的には

$$
20(-5^6c^{10})^4=4(5^5c^8)^5
$$

という指数正規化は FLT5 固有の重要な数値恒等式であり、現在は `rw`・`unfold`・`push_cast`・`ring` の内部に埋め込まれている。

同じ正規化を後続で再利用する箇所が増えるなら、例えば `twenty_mul_visible_fourth_eq_four_mul_Q_fifth` のような独立補題へ切り出す余地がある。ただし本 theorem だけを見れば現在の 4 行 proof の方が簡潔である。

## 最適化候補

候補の一つは、`s` の sign removal と `Q` の定義から直接

```lean
have hmass : 20 * p.s ^ 4 = 4 * (zeroSectorQ p.c : ℤ) ^ 5 := by
  rw [p.s_eq_neg_five_pow_mul_tenth]
  unfold zeroSectorQ
  push_cast
  ring
```

という named lemma を先に作ることである。これにより `factor_product` 自体は 0308 とその mass identity の合成だけになる。

一方、現在の実装は theorem 数を増やさず、正規化の全体像を一箇所で読めるという利点がある。

`norm_num` で定数指数部分を先に整理する案も考えられるが、変数 `c` の冪も含むため `ring` の方が自然である。最小 proof や import 最小化の可否は、今回 Lean build を行わない条件のため未検証である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。本 theorem が直接利用する機能は少なくとも次である。

- `ℕ` と `ℤ` の冪・積
- `Nat` から `Int` への cast
- `calc`
- `rw`
- `unfold`
- `push_cast`
- `ring`
- 先行 theorem `factor_product_twenty`
- 先行 theorem `s_eq_neg_five_pow_mul_tenth`

本 proof では `omega`、`linarith`、`nlinarith`、`positivity`、`exact_mod_cast` は直接使わない。

元 generated source は `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` である。厳密な最小 Mathlib import 集合は Lean build 禁止条件のため確認していない。`ring` と `push_cast` の tactic import、整数・自然数 cast の必要部分まで絞れる可能性はあるが、ここでは推測として確定しない。

## Comparator challenge 化の可否

**可能。難度は中級。**

比較課題として適しているのは次の点である。

- `s_eq_neg_five_pow_mul_tenth` を再利用するか、`s_natAbs_eq` から再構築してしまうか。
- `zeroSectorQ` の抽象化を保ったまま証明する方法と、`unfold` して `ring` へ渡す方法の比較。
- `push_cast` を使う proof と、明示的な `norm_cast` / `exact_mod_cast` 系の変換を使う proof の比較。
- `20*s^4 = 4*Q^5` を独立補題へ切り出す設計と、現行の局所正規化を比較する。

単なる代数計算ではなく、`ℕ` と `ℤ` の境界、既存 theorem の再利用、抽象化境界の選択を評価できるため Comparator challenge に向いている。

## PDF との照合

対象 branch には既存の日英 PDF

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することは repository 上で確認済みである。

ただし GitHub コネクタの通常 text fetch では binary PDF 本文を取得できないため、本実行では PDF 内の具体的ページ・節・式番号と本 theorem を直接照合していない。従って PDF 上の位置については推測しない。

本解説の Lean code、宣言順、定義、直接依存、後続宣言との関係は `Flt5DkMath/FLT5StandAlone.lean` を正本としている。

## 次に読むべき宣言

次の宣言は 0310 `GoldenZeroSectorCandidate.factor_difference`、種別は **`theorem`** である。

Lean 正本では

```lean
/-- Exact distance between the upper and lower inversion factors. -/
theorem factor_difference (p : GoldenZeroSectorCandidate) :
    zeroSectorB p.r p.s p.d - zeroSectorA p.r p.s p.d =
      8 * (p.d : ℤ) ^ 5 := by
  unfold zeroSectorA zeroSectorB zeroSectorW
  ring
```

と続く。

0309 が積

$$
AB=4Q^5
$$

を固定するのに対し、0310 は二因子の正確な距離

$$
B-A=8d^5
$$

を固定する。積と差を同時に保持することで、後続の inversion factor arithmetic に必要な拘束が揃っていく。