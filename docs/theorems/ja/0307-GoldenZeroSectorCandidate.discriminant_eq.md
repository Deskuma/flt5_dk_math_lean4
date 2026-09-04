# 0307 — `GoldenZeroSectorCandidate.discriminant_eq`

## 宣言種別

これは **`theorem`** である。

0306 `GoldenZeroSectorCandidate.square_reconstruction` の直後に置かれ、zero-sector inversion で導入した `U` と `W` を用いて、quartic identity を差平方の形へ変換する。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- The diagonal quartic identity becomes a difference of two squares. -/
theorem discriminant_eq (p : GoldenZeroSectorCandidate) :
    zeroSectorU p.r p.s ^ 2 - zeroSectorW p.d ^ 2 = 20 * p.s ^ 4 := by
  have hdiag := sixteen_mul_goldenFifthSndFactor_eq p.r p.s
  rw [p.H_eq_tenth] at hdiag
  unfold zeroSectorU zeroSectorW
  calc
    (zeroSectorX p.r p.s ^ 2 + 5 * p.s ^ 2) ^ 2 -
        (4 * (p.d : ℤ) ^ 5) ^ 2 =
        (zeroSectorX p.r p.s ^ 4 +
          10 * zeroSectorX p.r p.s ^ 2 * p.s ^ 2 +
          5 * p.s ^ 4 - 16 * (p.d : ℤ) ^ 10) +
          20 * p.s ^ 4 := by ring
    _ = 20 * p.s ^ 4 := by rw [← hdiag]; ring
```

結論は整数上の等式

$$
U(r,s)^2-W(d)^2=20s^4
$$

である。

## 数学的意味

定義は

$$
X=2r+s,
$$

$$
U=X^2+5s^2,
$$

$$
W=4d^5.
$$

一方、先行 theorem `sixteen_mul_goldenFifthSndFactor_eq` は

$$
16H(r,s)=X^4+10X^2s^2+5s^4
$$

を与え、candidate の `H_eq_tenth` は

$$
H(r,s)=d^{10}
$$

を与える。従って

$$
16d^{10}=X^4+10X^2s^2+5s^4.
$$

ここで

$$
U^2=(X^2+5s^2)^2
=X^4+10X^2s^2+25s^4,
$$

$$
W^2=(4d^5)^2=16d^{10}.
$$

したがって差を取ると

$$
U^2-W^2
=20s^4.
$$

この theorem は quartic factor の diagonalization と tenth-power split を、後続の因数分解に直接使える差平方へ圧縮する。

## 証明全体での役割

zero-sector inversion の中心的な変換点である。0306 までは `U` の内部に平方座標が保持されていることを確認していたが、0307 では `W` を導入して

$$
U^2-W^2
$$

という因数分解可能な形へ進む。

次の 0308 `factor_product_twenty` は単に

$$
(U-W)(U+W)=U^2-W^2
$$

を使って

$$
A\,B=20s^4
$$

を得る。したがって 0307 は quartic identity と inversion factors を接続する橋である。

## 直接依存する定義・補題

### `sixteen_mul_goldenFifthSndFactor_eq`

```lean
theorem sixteen_mul_goldenFifthSndFactor_eq (r s : ℤ) :
    16 * goldenFifthSndFactor r s =
      zeroSectorX r s ^ 4 +
        10 * zeroSectorX r s ^ 2 * s ^ 2 +
        5 * s ^ 4
```

quartic factor の diagonal identity を供給する。

### `GoldenZeroSectorCandidate.H_eq_tenth`

```lean
theorem H_eq_tenth (p : GoldenZeroSectorCandidate) :
    goldenFifthSndFactor p.r p.s = (p.d : ℤ) ^ 10
```

quartic factor を tenth power へ置換する。

### `zeroSectorU`, `zeroSectorW`

```lean
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2

def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

結論の二つの平方を構成する。

### `ring`

両段階の多項式恒等式を正規化して閉じる。

## 証明または構築の流れ

1. `sixteen_mul_goldenFifthSndFactor_eq p.r p.s` を `hdiag` として取得する。
2. `rw [p.H_eq_tenth] at hdiag` により $H=d^{10}$ を代入する。
3. `zeroSectorU` と `zeroSectorW` を unfold し、目標を $X,s,d$ の多項式等式へ戻す。
4. 最初の `ring` で

$$
U^2-W^2
=
\bigl(X^4+10X^2s^2+5s^4-16d^{10}\bigr)+20s^4
$$

へ整理する。
5. `rw [← hdiag]` で括弧内を 0 に置換可能な形へ戻す。
6. 最後の `ring` で残差を消し、$20s^4$ を得る。

## Lean 固有の処理

`rw [p.H_eq_tenth] at hdiag` は結論側ではなく補助等式 `hdiag` を書き換えている点が重要である。これにより quartic factor を source identity の段階で tenth power に変換し、その後は純粋な整数環計算として処理できる。

また `zeroSectorX` は unfold されない。`ring` にとって `zeroSectorX p.r p.s` は一つの ring atom で十分であり、`2*r+s` まで展開する必要がない。この proof は diagonalization の抽象境界を保っている。

## 冗長・重複箇所

proof は短く、明白な重複は少ない。ただし 0306 `square_reconstruction` を直接使わず `zeroSectorU` を unfold しているため、概念上は平方再構成の情報を再展開している。

これは必ずしも欠点ではない。0307 は quartic diagonal identity の係数を直接合わせる必要があるため、`U=X^2+5s^2` の具体形を展開する方が `ring` に適している。

## 最適化候補

候補の一つは、candidate に依存しない代数部分を一般補題へ分離することである。例えば

```lean
theorem zeroSector_discriminant_algebra
    (X s d : ℤ)
    (h : 16 * d ^ 10 = X ^ 4 + 10 * X ^ 2 * s ^ 2 + 5 * s ^ 4) :
    (X ^ 2 + 5 * s ^ 2) ^ 2 - (4 * d ^ 5) ^ 2 = 20 * s ^ 4 := by
  nlinarith [h]
```

のような形が考えられる。ただし tactic の安定性や型の整合性は Lean build を行っていないため未検証である。

また `square_reconstruction` を使う proof への書換えも候補だが、現行の二段 `ring` の方が短く安定している可能性が高い。

## 必要 Mathlib import と import 最適化候補

standalone 正本では Mathlib 全体を利用している。本 theorem が直接必要とする機能は少なくとも次である。

- `ℤ` と冪・減法・乗法
- rewrite (`rw`)
- `ring` tactic
- `zeroSectorU`, `zeroSectorW`, `zeroSectorX`
- `sixteen_mul_goldenFifthSndFactor_eq`
- `H_eq_tenth`

`omega`, `linarith`, `positivity`, `norm_num`, `exact_mod_cast` は本 proof では使わない。

厳密な最小 import は Lean build 禁止条件のため未確認である。元 source module `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` の import graph を個別に検証する必要がある。

## Comparator challenge 化の可否

**可能。難度は中級。**

単なる `ring` 穴埋めより、次の観点を比較させる課題に向く。

- `hdiag` に `H_eq_tenth` を先に rewrite する設計。
- `zeroSectorX` を unfold せず ring atom として残す設計。
- 1回の巨大な `ring` で閉じる proof と、現行の `calc` 二段 proof の比較。
- `square_reconstruction` を介する proof が本当に簡潔になるかの比較。

## PDF との照合

対象 branch には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを GitHub 正本で確認した。

ただし GitHub コネクタの通常 text fetch は binary PDF 本文を返さないため、本実行では PDF 内の具体的ページ・節・式番号と 0307 を直接照合できていない。従って PDF 上の位置は推測しない。

本解説の Lean code、宣言順、直接依存、後続宣言との関係は repository 内 `Flt5DkMath/FLT5StandAlone.lean` を正本としている。

## 次に読むべき宣言

次の宣言は 0308 `GoldenZeroSectorCandidate.factor_product_twenty`、種別は **`theorem`** である。

Lean 正本では

```lean
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

と続く。

0307 の

$$
U^2-W^2=20s^4
$$

を、$A=U-W$、$B=U+W$ によって

$$
AB=20s^4
$$

へ変換する最初の factorization theorem である。