# 0306 — `GoldenZeroSectorCandidate.square_reconstruction`

## 宣言種別

これは **`theorem`** である。

0305 `GoldenZeroSectorCandidate.U_nonneg` が補助量 `U` の非負性を固定した直後に置かれ、zero-sector inversion で導入された `U` と diagonal coordinate `X` の間の正確な平方再構成を与える。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- The reconstructed square coordinate is retained exactly. -/
theorem square_reconstruction (p : GoldenZeroSectorCandidate) :
    zeroSectorU p.r p.s - 5 * p.s ^ 2 = zeroSectorX p.r p.s ^ 2 := by
  unfold zeroSectorU
  ring
```

結論は整数上の等式

```lean
zeroSectorU p.r p.s - 5 * p.s ^ 2 = zeroSectorX p.r p.s ^ 2
```

である。

## 数学的意味

直前の 0305 で確認した定義は

```lean
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s

def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

である。従って

$$
X(r,s)=2r+s,
$$

$$
U(r,s)=X(r,s)^2+5s^2.
$$

この定義から単純に $5s^2$ を移項すると

$$
U(r,s)-5s^2=X(r,s)^2
$$

となる。

つまり `U` は単なる非負な補助量ではなく、`5s²` を除いた残差が **厳密に平方** になるよう設計された diagonal quantity である。この theorem はその設計不変量を named theorem として公開している。

## 証明全体での役割

0305 `U_nonneg` は

$$
U\ge0
$$

という順序情報を与えた。0306 はそれより強く、

$$
U-5s^2=X^2
$$

という exact algebraic reconstruction を固定する。

この後の 0307 `GoldenZeroSectorCandidate.discriminant_eq` では `U` と `W=4d^5` を用いて

$$
U^2-W^2=20s^4
$$

という difference-of-squares 形式へ進む。したがって 0306 は、`U` が元の座標情報を失った抽象的補助量ではなく、その内部に平方座標 $X^2$ を保持していることを明示する境界 theorem と読める。

ただし現行の 0307 の Lean proof は 0306 を直接 rewrite せず、`zeroSectorU` を unfold して `ring` で展開している。そのため **論理的・概念的には後続の基礎であるが、現行コード上の直接依存ではない**。この点は theorem museum では区別しておく必要がある。

## 直接依存する定義・補題

### `zeroSectorU`

proof で直接 unfold される定義である。

```lean
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

これを展開すると目標は

```lean
zeroSectorX p.r p.s ^ 2 + 5 * p.s ^ 2 - 5 * p.s ^ 2 =
  zeroSectorX p.r p.s ^ 2
```

という純粋な環等式になる。

### `zeroSectorX`

`zeroSectorU` 内部の平方座標である。

```lean
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s
```

本 theorem では `zeroSectorX` 自体を unfold する必要はない。`ring` にとって `zeroSectorX p.r p.s` は一つの環要素として扱えば十分だからである。

### `ring`

Mathlib の ring normalization tactic。`zeroSectorU` 展開後の加減算を正規化して等式を閉じる。

candidate 固有の仮定、coprimality、positivity、parity、five-adic 条件などへの依存は一切ない。

## 証明または構築の流れ

1. `unfold zeroSectorU` により左辺を定義展開する。
2. 目標は概念的に

   ```lean
   X ^ 2 + 5 * s ^ 2 - 5 * s ^ 2 = X ^ 2
   ```

   となる。
3. `ring` が整数環の加法・乗法・減法・冪を正規化し、両辺が同一多項式であることを確認する。
4. `GoldenZeroSectorCandidate` の field hypothesis は使わずに終了する。

紙上では定義代入と相殺だけの一行証明である。

## Lean 固有の処理

Lean 上のポイントは、`zeroSectorU` だけを unfold し、`zeroSectorX` は抽象的なまま残していることである。

```lean
unfold zeroSectorU
ring
```

で十分なのは、`ring` が `zeroSectorX p.r p.s` の内部構造を知らなくても、その値を整数環の一要素として扱えるためである。

これは 0305 と同様に「必要な定義だけを展開する」proof style であり、内部定義変更への耐性を高める。もし `zeroSectorX` の具体式 `2*r+s` が変更されても、`zeroSectorU` が `X²+5s²` の形を保持する限り、本 theorem の proof はそのまま成立する。

また `ring` は `simp` より一般的な多項式正規化を使っているが、この目標は単純な相殺なので、別証明が存在する可能性はある。ただし現行形は短く安定している。

## 冗長・重複箇所

本 theorem 自体は二行であり、proof term の冗長性はほぼない。

一方で数学的には `zeroSectorU` の定義そのものを再述しているに近い。従って「定義から直ちに得られる補題を別 declaration にする必要があるか」という API 設計上の検討余地はある。

しかし後続で

```lean
p.square_reconstruction
```

として平方再構成を意味付きで参照できる利点がある。定義 unfold を各 proof に散らすより、抽象化境界として named theorem を保持する方が、zero-sector inversion の数学的構造は読みやすい。

また 0307 は現状この theorem を直接使わず `zeroSectorU` を再展開するため、概念の重複は存在する。将来的に 0307 の証明を `square_reconstruction` ベースで書き直せるかは最適化候補になる。

## 最適化候補

第一候補は 0305 と同様、candidate 非依存性を型レベルへ反映する一般補題である。

概念的には

```lean
theorem zeroSector_square_reconstruction (r s : ℤ) :
    zeroSectorU r s - 5 * s ^ 2 = zeroSectorX r s ^ 2 := by
  unfold zeroSectorU
  ring
```

を置き、現在の theorem を specialization にできる。

```lean
theorem square_reconstruction (p : GoldenZeroSectorCandidate) :
    zeroSectorU p.r p.s - 5 * p.s ^ 2 = zeroSectorX p.r p.s ^ 2 :=
  zeroSector_square_reconstruction p.r p.s
```

これにより candidate hypothesis を本質的に必要としない事実が API 上でも明確になる。

第二候補は後続 `discriminant_eq` が `zeroSectorU` を再展開している点を見直し、0306 を介して変形できるか検討することである。ただし 0307 は quartic identity と大きな `ring` 展開を組み合わせており、0306 を使うことが必ずしも proof を短くするとは限らない。

これらは Lean build を行っていないため **未検証の最適化案** であり、本 museum 作業では source code を変更しない。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は generated artifact であり、source manifest に複数の `DkMath/FLT/Five/...` module が列挙されている。現行 standalone 環境では Mathlib 全体を利用する構成である。

本 theorem が直接必要とする機能は少なくとも次である。

- 整数環 `ℤ`
- subtraction / multiplication / powers
- `ring` tactic
- `zeroSectorU`, `zeroSectorX` の定義

0305 で使った `positivity` は本 theorem には不要であり、`omega`, `linarith`, `norm_num`, `exact_mod_cast` も使用しない。

Mathlib の厳密な最小 import は、今回 Lean build を行わないという条件のため **未確認** である。import 最適化をする場合は元 source module の import graph を確認し、整数環と ring tactic を供給する最小 module 群をビルドで検証すべきである。

## Comparator challenge 化の可否

**可能。難度は初級。**

statement と `zeroSectorU` の定義が与えられていれば、期待される核は

```lean
unfold zeroSectorU
ring
```

である。

Comparator challenge としては、単純な穴埋めより次の比較が有益である。

- `zeroSectorX` まで unfold する必要がないことを見抜けるか。
- `ring` と `ring_nf` のどちらが自然か。
- candidate hypothesis を一切使わずに閉じられるか。
- 定義展開を最小限に保つ proof と、すべて展開する proof の安定性を比較できるか。

特に「抽象関数値を ring atom として残してよい」という Lean の多項式正規化の感覚を学ぶ小問として適している。

## PDF との照合

対象 branch には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを GitHub 正本で確認した。

ただし GitHub コネクタの通常 text fetch は binary PDF 本文を返さないため、本実行では PDF 内の具体的ページ・節・式番号と 0306 を直接照合できていない。従って PDF 上の位置については推測しない。

本解説の Lean code、宣言順、直接依存、後続宣言との関係は repository 内 `Flt5DkMath/FLT5StandAlone.lean` を正本としている。

## 次に読むべき宣言

次の宣言は 0307 `GoldenZeroSectorCandidate.discriminant_eq`、種別は **`theorem`** である。

Lean 正本では 0306 の直後に

```lean
/-- The diagonal quartic identity becomes a difference of two squares. -/
theorem discriminant_eq (p : GoldenZeroSectorCandidate) :
    zeroSectorU p.r p.s ^ 2 - zeroSectorW p.d ^ 2 = 20 * p.s ^ 4 := by
  have hdiag := sixteen_mul_goldenFifthSndFactor_eq p.r p.s
  rw [p.H_eq_tenth] at hdiag
  unfold zeroSectorU zeroSectorW
  calc
    ...
```

と続く。

0306 が

$$
U-5s^2=X^2
$$

として平方座標を再構成したのに対し、0307 は quartic identity と `H=d^{10}` を組み合わせ、

$$
U^2-W^2=20s^4
$$

という difference-of-squares へ進む。ここから inversion factors の積への因数分解が始まる。