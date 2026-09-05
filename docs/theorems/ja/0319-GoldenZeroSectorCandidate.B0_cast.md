# 0319 — `GoldenZeroSectorCandidate.B0_cast`

## 宣言種別

これは **`theorem`** である。

0317 `GoldenZeroSectorCandidate.B0` で導入した自然数代表 $B_0$ を、0313 `GoldenZeroSectorCandidate.B_pos` で確立済みの正性を使って元の signed upper inversion factor $B$ と正確に同一視する cast bridge である。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- Cast equation for the positive upper natural representative. -/
theorem B0_cast (p : GoldenZeroSectorCandidate) :
    (p.B0 : ℤ) = zeroSectorB p.r p.s p.d := by
  exact Int.ofNat_natAbs_of_nonneg p.B_pos.le
```

candidate `p` に対し、自然数 `p.B0` を整数へ cast したものが signed factor `zeroSectorB p.r p.s p.d` と一致することを返す。

型としては

```lean
(p.B0 : ℤ) = zeroSectorB p.r p.s p.d
```

であり、左辺は `ℕ → ℤ` coercion、右辺は最初から `ℤ` である。

## 数学的主張

0317 で

```lean
def B0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorB p.r p.s p.d).natAbs
```

と定義されているため、数学的には

$$
B_0=|B|,
$$

ただし

$$
B=\operatorname{zeroSectorB}(r,s,d)=U+W.
$$

0313 `B_pos` により

$$
B>0
$$

が既に証明済みなので $B\ge0$、したがって

$$
|B|=B.
$$

ゆえに

$$
(B_0:\mathbb Z)=B.
$$

本 theorem はこの事実を Lean の `ℕ` / `ℤ` 型境界で明示的な equality として固定する。

## 証明全体での役割

zero-sector inversion では signed integer world で

$$
AB=4Q^5,
$$

$$
B-A=8d^5,
$$

$$
A+B=2U,
$$

$$
0<A<B
$$

まで構築した後、0316 `A0` と 0317 `B0` により

$$
A_0=|A|,\qquad B_0=|B|
$$

という自然数代表へ移る。

0318 `A0_cast` が lower factor について

$$
(A_0:\mathbb Z)=A
$$

を回収し、本 0319 `B0_cast` が upper factor について

$$
(B_0:\mathbb Z)=B
$$

を回収する。この二本が揃うことで、signed world で得た積・差・順序を自然数側へ損失なく輸送できる。

実際、直後の自然数 positivity を経て、後続 `A0_mul_B0` は `A0_cast` と `B0_cast` を使い

$$
A_0B_0=4Q^5
$$

を `ℕ` の等式として取り出す。また `B0_eq_A0_add` では

$$
B_0=A_0+8d^5
$$

という subtraction-free な自然数形へ変換する。

したがって本 theorem は新しい数論的情報を追加するものではなく、 **upper factor の意味と符号を保ったまま自然数 factorization 層へ接続する correctness bridge** である。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate.B0`

```lean
def B0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorB p.r p.s p.d).natAbs
```

左辺 `p.B0` の直接の定義である。

### `GoldenZeroSectorCandidate.B_pos`

0313 で証明済みの

$$
0<B
$$

を供給する。proof term では

```lean
p.B_pos.le
```

として

$$
0\le B
$$

へ弱める。

### `Int.ofNat_natAbs_of_nonneg`

整数 $z$ に対し $0\le z$ なら、その `natAbs` を整数へ戻した値が $z$ 自身になることを与える Mathlib lemma である。本 theorem では $z=\operatorname{zeroSectorB}(p.r,p.s,p.d)$ を代入する。

### `zeroSectorB`

signed upper inversion factor を与える project 側定義である。本 theorem 自体は内部式 `U+W` を展開しないため、具体的多項式構造には依存せず、正性と `natAbs` の性質だけに依存している。

## 証明または構築の流れ

1. ゴールは `(p.B0 : ℤ) = zeroSectorB p.r p.s p.d`。
2. `p.B0` は definitionally `(zeroSectorB p.r p.s p.d).natAbs`。
3. `p.B_pos.le` から `0 ≤ zeroSectorB ...` を得る。
4. `Int.ofNat_natAbs_of_nonneg p.B_pos.le` を適用する。
5. 得られた equality が `B0` の定義展開後のゴールと definitionally 一致するため `exact` で終了する。

## Lean 固有の処理

### `ℕ` / `ℤ` coercion

```lean
(p.B0 : ℤ)
```

と明示することで、自然数 factorization API と signed integer inversion API の型境界を theorem の型に露出させている。

### strict positivity から nonnegativity への弱化

`B_pos : 0 < B` そのものではなく `p.B_pos.le : 0 ≤ B` を用いる。Mathlib lemma が要求する最弱の仮定へ正確に合わせている。

### definitional reduction

proof では `unfold B0` を書かない。Lean は `p.B0` をその定義まで reduction できるため、

```lean
exact Int.ofNat_natAbs_of_nonneg p.B_pos.le
```

だけで expected type と proof term の型が一致する。

### dot notation

candidate-centered API として `p.B0`, `p.B_pos` を使っており、依存元が明瞭である。

## 冗長・重複箇所

0318 `A0_cast` と完全に対称であり、実装 pattern は重複している。

```lean
exact Int.ofNat_natAbs_of_nonneg p.A_pos.le
```

に対して、本 theorem は

```lean
exact Int.ofNat_natAbs_of_nonneg p.B_pos.le
```

だけが異なる。

ただし `A0_cast` / `B0_cast` を別々の named theorem として保持することで lower / upper factor の意味が API 上に残る。generic helper にまとめても proof length はほとんど縮まず、利用側の可読性を落とす可能性があるため、この重複は合理的である。

## 最適化候補

現行 proof は一行であり、実質的には既に最小級である。

説明性を優先するなら未検証候補として

```lean
  simpa [B0] using
    (Int.ofNat_natAbs_of_nonneg p.B_pos.le)
```

のように definition 展開を明示できる。しかし現行 `exact` の方が短く、definitional equality を自然に利用している。

`A0_cast` と共通の generic helper を作る案もあるが、意味のある abstraction gain は小さい。従って現状維持が最も自然と評価する。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem が Mathlib 側で直接必要とする中心要素は

- `Int.ofNat_natAbs_of_nonneg`
- order の `LT.lt.le`
- `ℕ` から `ℤ` への coercion

である。

`GoldenZeroSectorCandidate`, `B0`, `B_pos`, `zeroSectorB` は project upstream declarations である。

この theorem 単体なら `Mathlib` 全体より狭い import で十分である可能性が高いが、最小 Mathlib module と generated standalone 全体の import closure は本実行では Lean build を行わないため確定していない。具体的な import 縮小は **未検証候補** とする。

## Comparator challenge 化の可否

**可能。初級〜中級の Lean bridge theorem challenge に適する。**

比較対象として、現行の一行 `exact`、`simpa [B0] using ...`、先に `unfold B0` する proof、さらに `A0_cast` / `B0_cast` の generic helper 化を置ける。

数学自体は単純だが、definitional equality、coercion、`natAbs`、strict-to-weak order conversion、Mathlib lemma selection を一度に比較できるため、Comparator 教材として価値がある。

## PDF との照合

対象 branch には既存の日英 PDF

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを repository 上で確認した。

ただし GitHub コネクタの通常 text fetch は binary PDF 本文を返さず、公開 raw URL の直接取得も本実行環境では成功しなかったため、具体的ページ・節・式番号との照合はできていない。対応位置は推測しない。

本解説の Lean code、宣言順、`B0` / `B_pos` への依存、後続 `A0_pos` への接続は、最新 branch の `Flt5DkMath/FLT5StandAlone.lean` を正本として確認した。

## 次に読むべき宣言

次の宣言は 0320 `GoldenZeroSectorCandidate.A0_pos`、種別は **`theorem`** である。

```lean
/-- The natural representatives are both positive. -/
theorem A0_pos (p : GoldenZeroSectorCandidate) : 0 < p.A0 := by
  by_contra hpos
  have hzero : p.A0 = 0 := Nat.eq_zero_of_not_pos hpos
  have hcast := p.A0_cast
  rw [hzero] at hcast
  norm_num at hcast
  have hApos := p.A_pos
  omega
```

0319 までで signed factor $B$ と natural representative $B_0$ の同一視が完了する。0320 からは自然数側自身の positivity を明示的な theorem として固定し、続く `B0_pos`、`A0_mul_B0`、`B0_eq_A0_add` へ進む。
