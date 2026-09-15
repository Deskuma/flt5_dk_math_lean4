# 0310 — `GoldenZeroSectorCandidate.factor_difference`

## 宣言種別

これは **`theorem`** である。

0309 `GoldenZeroSectorCandidate.factor_product` が inversion factors の積

$$
AB = 4Q^5
$$

を固定したのに対し、本 theorem は二因子の正確な差

$$
B-A = 8d^5
$$

を固定する。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- Exact distance between the upper and lower inversion factors. -/
theorem factor_difference (p : GoldenZeroSectorCandidate) :
    zeroSectorB p.r p.s p.d - zeroSectorA p.r p.s p.d =
      8 * (p.d : ℤ) ^ 5 := by
  unfold zeroSectorA zeroSectorB zeroSectorW
  ring
```

結論は整数 `ℤ` 上の等式である。

$$
B(r,s,d)-A(r,s,d)=8d^5.
$$

ここで

$$
A=U-W,
\qquad
B=U+W,
\qquad
W=4d^5.
$$

## 数学的意味

定義をそのまま代入すると

$$
B-A=(U+W)-(U-W)=2W.
$$

さらに

$$
W=4d^5
$$

なので

$$
B-A=2\cdot4d^5=8d^5.
$$

従って本 theorem は新しい数論的仮定を導入するものではなく、inversion factor の定義に埋め込まれている対称性を exact equality として API 化する theorem である。

## 証明全体での役割

zero-sector inversion では 0309 により

$$
AB=4Q^5
$$

という multiplicative constraint が得られた。本 0310 はそれと独立な additive constraint

$$
B-A=8d^5
$$

を与える。

積だけでは `A`,`B` の配置は十分に拘束されないが、差が固定されることで二因子の距離まで決まる。後続では positive integer representatives `A0`,`B0` を導入した後、本 theorem を使って

$$
B_0=A_0+8d^5
$$

という自然数上の subtraction-free identity `B0_eq_A0_add` を構築する。

さらに `GoldenZeroSectorInversionPacket` は、この自然数版 factor difference をフィールドとして保持し、後続の gcd・2-adic branch analysis で利用する。したがって本 theorem は短い恒等式ながら、整数上の対称因子表示と自然数上の factor arithmetic をつなぐ基礎 API である。

## 直接依存する定義・補題

### `zeroSectorA`

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d
```

lower inversion factor

$$
A=U-W
$$

を定義する。

### `zeroSectorB`

```lean
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

upper inversion factor

$$
B=U+W
$$

を定義する。

### `zeroSectorW`

```lean
def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

二因子を分離する fifth-power coordinate

$$
W=4d^5
$$

を定義する。

### `ring`

`zeroSectorA`、`zeroSectorB`、`zeroSectorW` の展開後に残る可換環恒等式

$$
(U+4d^5)-(U-4d^5)=8d^5
$$

を正規化して閉じる。

## 証明または構築の流れ

1. `unfold zeroSectorA zeroSectorB zeroSectorW` で三つの定義を展開する。
2. 左辺を

$$
(U+4d^5)-(U-4d^5)
$$

という整数式にする。
3. `ring` が `U` の相殺と係数整理を行い、

$$
8d^5
$$

を得る。

証明中で `GoldenZeroSectorCandidate` の hypothesis field は一つも参照していない。必要なのは `p.r`,`p.s`,`p.d` を定義へ代入することだけである。

## Lean 固有の処理

`p.d : ℕ` に対して `zeroSectorW` は

```lean
4 * (p.d : ℤ) ^ 5
```

を返すため、結論も `ℤ` 上に置かれている。cast は `zeroSectorW` の定義内部に既に明示されており、本 proof では `push_cast` や `exact_mod_cast` は必要ない。

また subtraction が存在するため、自然数ではなく整数を使うことが証明を非常に単純にしている。後続の `B0_eq_A0_add` で初めて subtraction-free な `ℕ` の式へ移す設計になっている。

`unfold` 後の目標は純粋な polynomial identity なので、`ring` が適切な tactic である。

## 冗長・重複箇所

本 proof は

```lean
unfold zeroSectorA zeroSectorB zeroSectorW
ring
```

だけであり、局所的な冗長性はほぼない。

数学的には一般恒等式

$$
(U+W)-(U-W)=2W
$$

を独立補題にしてから `W=4d^5` を適用する設計も可能である。しかし、この identity が他の場所で繰り返し必要にならない限り、現行の直接展開の方が短く明瞭である。

## 最適化候補

最も自然な候補は、`zeroSectorA` と `zeroSectorB` に対する一般 API

```lean
zeroSectorB r s d - zeroSectorA r s d = 2 * zeroSectorW d
```

を candidate 非依存 theorem として切り出すことである。そうすれば本 theorem は `zeroSectorW` の展開だけに縮められる。

ただし現在の theorem は既に二行 proof であり、宣言数を増やすほどの利益があるかは後続の再利用頻度次第である。

また `ring_nf` や `norm_num` を組み合わせる必要はなく、現状の `ring` 一回が簡潔である。Lean build を行わない条件のため、さらに短い proof や最小 import の実証確認はしていない。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem が直接必要とする機能は少なくとも次である。

- `ℕ`、`ℤ`
- `Nat` から `Int` への cast
- 整数の加減算・乗算・冪
- `unfold`
- `ring`
- `zeroSectorA`
- `zeroSectorB`
- `zeroSectorW`

本 proof は `omega`、`linarith`、`nlinarith`、`positivity`、`push_cast`、`exact_mod_cast` を直接使用しない。

元 generated source は `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` である。`Mathlib` 全体ではなく ring tactic と整数・自然数の基本代数部分まで import を絞れる可能性が高いが、厳密な最小集合は Lean build 禁止条件のため未検証である。

## Comparator challenge 化の可否

**可能。難度は初級〜中級。**

短い theorem なので、証明探索そのものより proof engineering の比較に向く。

- `unfold` + `ring` の最短 proof。
- `change` で `U`,`W` の形を明示してから一般差平方型の恒等式として解く proof。
- `zeroSectorB - zeroSectorA = 2 * zeroSectorW` という再利用可能 lemma を先に設計する proof。
- `ring` と `ring_nf` の可読性・安定性比較。

特に「candidate hypothesis を使わず、定義だけで証明できること」を検出できるかは Comparator の評価点になる。

## PDF との照合

対象 branch には既存の日英 PDF

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを repository 上で確認した。

ただし GitHub コネクタの通常の text fetch は binary PDF 本文を返さないため、本実行では PDF 内の具体的ページ・節・式番号との直接照合はできていない。その位置については推測しない。

本解説の Lean code、宣言順、定義、直接依存、後続宣言との関係は `Flt5DkMath/FLT5StandAlone.lean` を正本として確認した。

## 次に読むべき宣言

次の宣言は 0311 `GoldenZeroSectorCandidate.factor_sum`、種別は **`theorem`** である。

Lean 正本では

```lean
/-- Exact sum of the two inversion factors. -/
theorem factor_sum (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d + zeroSectorB p.r p.s p.d =
      2 * zeroSectorU p.r p.s := by
  unfold zeroSectorA zeroSectorB
  ring
```

と続く。

0310 が差

$$
B-A=8d^5
$$

を固定するのに対し、0311 は和

$$
A+B=2U
$$

を固定する。積・差・和が揃うことで inversion factors の算術情報が明示的な API として完成に近づく。