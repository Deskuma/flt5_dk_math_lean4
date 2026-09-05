# 0308 — `GoldenZeroSectorCandidate.factor_product_twenty`

## 宣言種別

これは **`theorem`** である。

0307 `GoldenZeroSectorCandidate.discriminant_eq` の直後に置かれ、差平方として得られた discriminant identity を、zero-sector inversion の二つの因子 `A = U-W` と `B = U+W` の積へ変換する。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- Before sign removal, the two inversion factors multiply to `20*s^4`. -/
theorem factor_product_twenty (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d =
      20 * p.s ^ 4 := by
  calc
    zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d =
        zeroSectorU p.r p.s ^ 2 - zeroSectorW p.d ^ 2 := by
      unfold zeroSectorA zeroSectorB
      ring
    _ = 20 * p.s ^ 4 := p.discriminant_eq
```

結論は整数上の等式

$$
A(r,s,d)B(r,s,d)=20s^4
$$

である。

## 数学的意味

zero-sector inversion では

$$
U=X^2+5s^2,
$$

$$
W=4d^5,
$$

$$
A=U-W,
$$

$$
B=U+W
$$

と定義する。

したがって純粋な差平方恒等式により

$$
AB=(U-W)(U+W)=U^2-W^2.
$$

0307 `discriminant_eq` はすでに

$$
U^2-W^2=20s^4
$$

を証明しているため、これらを接続すると

$$
AB=20s^4
$$

を得る。

この theorem 自体は新しい数論的情報を作るのではなく、0307 で得た diagonal discriminant の情報を、後続の gcd・2-adic splitting・fifth-power factorization が扱いやすい「二因子の積」という形へ移し替えるものである。

## 証明全体での役割

0307 が quartic identity を差平方

$$
U^2-W^2=20s^4
$$

へ圧縮したのに対し、0308 はその差平方を明示的な inversion factors の積へ変換する。

ここが geometric/algebraic reconstruction から multiplicative arithmetic への境界である。後続ではこの積をさらに、candidate の符号除去式

$$
s=-5^6c^{10}
$$

を使って

$$
AB=4Q^5,
\qquad
Q=5^5c^8
$$

という中心的 fifth-power product に書き換える。その入口が本 theorem である。

特に後続の `A0_mul_B0`、`GoldenZeroSectorInversionPacket.factor_product`、さらに二進付値による factor branch 分解は、この multiplicative form を保存して利用する。

## 直接依存する定義・補題

### `zeroSectorA`

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d
```

下側 inversion factor

$$
A=U-W
$$

を定義する。

### `zeroSectorB`

```lean
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

上側 inversion factor

$$
B=U+W
$$

を定義する。

### `zeroSectorU`, `zeroSectorW`

```lean
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2

def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

`A` と `B` の中心と半差を与える。

### `GoldenZeroSectorCandidate.discriminant_eq`

```lean
theorem discriminant_eq (p : GoldenZeroSectorCandidate) :
    zeroSectorU p.r p.s ^ 2 - zeroSectorW p.d ^ 2 = 20 * p.s ^ 4
```

0308 が消費する主要な先行 theorem である。

### `ring`

`A` と `B` を unfold した後、

$$
(U-W)(U+W)=U^2-W^2
$$

を整数環の恒等式として閉じる。

## 証明または構築の流れ

1. `calc` の最初の段で `zeroSectorA` と `zeroSectorB` の積から開始する。
2. `unfold zeroSectorA zeroSectorB` により目標を

$$
(U-W)(U+W)=U^2-W^2
$$

へ展開する。
3. `ring` が差平方恒等式を正規化して閉じる。
4. 二段目では `p.discriminant_eq` をそのまま適用し、

$$
U^2-W^2=20s^4
$$

を得る。
5. よって `A*B = 20*s^4` が完成する。

## Lean 固有の処理

最初の `unfold` は `zeroSectorA` と `zeroSectorB` だけを展開し、`zeroSectorU`、`zeroSectorW`、`zeroSectorX` までは展開しない。`ring` にとって `U` と `W` は ring atom として扱えば十分だからである。

これは抽象化境界として良い選択である。`U=X^2+5s^2` や `W=4d^5` の内部を再展開せず、0307 で確立済みの discriminant identity を直接再利用できる。

また二段目は

```lean
_ = 20 * p.s ^ 4 := p.discriminant_eq
```

と theorem を直接 term として渡しており、`exact` や追加の `rw` を必要としない。

## 冗長・重複箇所

proof は非常に短く、実質的な重複はない。

概念上は、差平方恒等式

$$
(U-W)(U+W)=U^2-W^2
$$

は一般的な ring identity であり、FLT5 固有ではない。この一行を毎回 `ring` に任せることは可能だが、同型の変換が多数現れるなら一般補題として切り出す余地はある。

ただし本箇所だけを見る限り、一般補題を導入すると名前解決・引数指定が増え、現行 proof より冗長になる可能性が高い。

## 最適化候補

最も自然な候補は `mul_sub_mul_add` 型の既存恒等式、あるいは一般差平方補題を利用して `ring` を除くことである。例えば概念的には

```lean
have hsq :
    (zeroSectorU p.r p.s - zeroSectorW p.d) *
      (zeroSectorU p.r p.s + zeroSectorW p.d) =
    zeroSectorU p.r p.s ^ 2 - zeroSectorW p.d ^ 2 := by
  ring
```

を共通補題化できる。

しかし現行の

```lean
unfold zeroSectorA zeroSectorB
ring
```

は十分短く、`zeroSectorU` と `zeroSectorW` の抽象化も保つため、局所的にはかなり良い実装である。

また 0307 と 0308 を一 theorem に統合することも技術的には可能だが、`discriminant_eq` と factorization の責務が分離されている現行設計の方が依存関係を読みやすい。

これら最適化案の Lean 上での最小形は、本実行では Lean build を行わないため未検証である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。本 theorem が直接必要とする機能は少なくとも次である。

- `ℤ` の加法・減法・乗法・冪
- `calc`
- `unfold`
- `ring` tactic
- `zeroSectorA`, `zeroSectorB`, `zeroSectorU`, `zeroSectorW`
- `GoldenZeroSectorCandidate.discriminant_eq`

本 proof では `omega`、`linarith`、`positivity`、`norm_num`、`exact_mod_cast` は使用しない。

元 generated source は `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` である。厳密な最小 Mathlib import 集合は Lean build 禁止条件のため未確認であり、import 最適化を確定するにはこの source module の import graph を個別検証する必要がある。

## Comparator challenge 化の可否

**可能。難度は初級〜中級。**

課題としては次を比較できる。

- `unfold zeroSectorA zeroSectorB; ring` による直接 proof。
- 一般差平方補題を適用する proof。
- 0307 `discriminant_eq` を再証明せずに再利用できるか。
- `zeroSectorU` と `zeroSectorW` を不要に unfold した場合に proof がどれだけ肥大化するか。

単なる `ring` challenge よりも、「既に得た theorem をどの抽象化境界で再利用するか」を評価する Comparator に向いている。

## PDF との照合

対象 branch には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを GitHub 正本で確認した。

ただし GitHub コネクタの通常 text fetch は binary PDF 本文を返さないため、本実行では PDF 内の具体的ページ・節・式番号と 0308 を直接照合できていない。従って PDF 上の位置は推測しない。

本解説の Lean code、宣言順、直接依存、後続宣言との関係は repository 内 `Flt5DkMath/FLT5StandAlone.lean` を正本としている。

## 次に読むべき宣言

次の宣言は 0309 `GoldenZeroSectorCandidate.factor_product`、種別は **`theorem`** である。

Lean 正本では

```lean
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

と続く。

0308 の

$$
AB=20s^4
$$

に sign-removed coordinate

$$
s=-5^6c^{10}
$$

を代入し、

$$
Q=5^5c^8
$$

を用いて

$$
AB=4Q^5
$$

へ正規化する。zero-sector inversion における中心的な fifth-power product theorem である。