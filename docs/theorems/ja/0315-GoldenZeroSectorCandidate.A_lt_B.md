# 0315 — `GoldenZeroSectorCandidate.A_lt_B`

## 宣言種別

これは **`theorem`** である。

0312–0314 で inversion factors の strict positivity

$$
0 < A,\qquad 0 < B
$$

が確立された。本 theorem は 0310 `GoldenZeroSectorCandidate.factor_difference` の exact difference

$$
B-A=8d^5
$$

と candidate の $d>0$ を用いて、二因子の強制された順序

$$
A<B
$$

を確定する。

ここまでで

$$
0<A<B
$$

が揃い、後続は整数 factor $A,B$ を正の自然数代表 `A0`, `B0` へ移す段階に進む。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- The two factors occur in their forced strict order. -/
theorem A_lt_B (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d < zeroSectorB p.r p.s p.d := by
  have hdiff := p.factor_difference
  have hd : (0 : ℤ) < p.d := by exact_mod_cast p.d_pos
  have hpow : (0 : ℤ) < (p.d : ℤ) ^ 5 := pow_pos hd 5
  linarith
```

結論は `ℤ` 上の strict order である。

$$
A<B.
$$

ここで

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d

def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

である。

## 数学的意味

0310 `factor_difference` により

$$
B-A=8d^5.
$$

candidate は

$$
d>0
$$

を保持するので、整数へ埋め込んでも

$$
0<(d:ℤ).
$$

したがって

$$
0<d^5,
$$

さらに

$$
0<8d^5.
$$

ゆえに

$$
0<B-A,
$$

すなわち

$$
A<B.
$$

この順序は定義

$$
A=U-W,\qquad B=U+W
$$

から見れば $W>0$ の直接的帰結でもある。しかし現行 proof は、すでに API 化された exact identity `factor_difference` を再利用している。

## 証明全体での役割

0309–0311 では inversion factors に関する exact algebraic data

$$
AB=4Q^5,
$$

$$
B-A=8d^5,
$$

$$
A+B=2U
$$

が確立された。

0312–0314 では

$$
W>0,\qquad B>0,\qquad A>0
$$

が証明された。

本 theorem はそこへ

$$
A<B
$$

を加え、signed integer factorization を positive ordered factorization として固定する。

直後には

```lean
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs

def B0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorB p.r p.s p.d).natAbs
```

が導入される。`A_pos`, `B_pos`, `A_lt_B` により、これらは単なる絶対値ではなく、正の ordered natural representatives として扱える。

したがって 0315 は **整数上の inversion factor phase から自然数 factor phase へ移る直前の order gate** である。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate.factor_difference`

0310 で得た

```lean
theorem factor_difference (p : GoldenZeroSectorCandidate) :
    zeroSectorB p.r p.s p.d - zeroSectorA p.r p.s p.d =
      8 * (p.d : ℤ) ^ 5
```

を

```lean
have hdiff := p.factor_difference
```

で取り出す。

### `GoldenZeroSectorCandidate.d_pos`

candidate が保持する自然数上の

$$
0<d
$$

である。proof では整数上の不等式が必要なので、`exact_mod_cast` で

```lean
have hd : (0 : ℤ) < p.d := by exact_mod_cast p.d_pos
```

へ移す。

### `pow_pos`

`hd : 0 < (p.d : ℤ)` から

```lean
have hpow : (0 : ℤ) < (p.d : ℤ) ^ 5 := pow_pos hd 5
```

として $d^5>0$ を得る。

### `linarith`

`hdiff` と `hpow` から線形算術として最終結論 $A<B$ を閉じる。

## 証明または構築の流れ

1. `p.factor_difference` を `hdiff` として取り出し、$B-A=8d^5$ を得る。
2. `p.d_pos : 0 < p.d` を `exact_mod_cast` で `ℤ` 上の `hd : 0 < (p.d : ℤ)` に変換する。
3. `pow_pos hd 5` で $d^5>0$ を得る。
4. `linarith` に `hdiff` と `hpow` を与え、$B-A>0$ から $A<B$ を導く。

## Lean 固有の処理

### `ℕ` から `ℤ` への移送

`p.d` は `ℕ` だが、`zeroSectorA`, `zeroSectorB` と `factor_difference` の等式は `ℤ` 上にある。この型境界を

```lean
exact_mod_cast p.d_pos
```

が埋めている。

この一行は数学的には自明な包含

$$
\mathbb N\hookrightarrow\mathbb Z
$$

に対応するが、Lean では型が異なるため明示的な橋渡しが必要である。

### 非線形部分を先に `pow_pos` で処理

`linarith` 自体は一般の非線形冪の正性を発見するための tactic ではない。そのため

```lean
have hpow : (0 : ℤ) < (p.d : ℤ) ^ 5 := pow_pos hd 5
```

で非線形項を一つの正の量として先に確立し、その後の関係だけを線形算術へ渡している。

これは tactic の責務分離として明瞭である。

## 冗長・重複箇所

数学的には `A=U-W`, `B=U+W`, `W_pos` から

$$
A<B
$$

を直接示すこともできる。

しかし現行 proof は `factor_difference` を再利用するため、factor API の一貫性が高い。0310 で既に差を exact identity として固定している以上、それを利用するのは自然であり、重複とは言い難い。

一方、`hd : 0 < (p.d : ℤ)` と `hpow : 0 < (p.d : ℤ)^5` を個別に局所化しているため、短縮だけを目的にすれば `positivity` や別の order lemma で圧縮できる可能性はある。

## 最適化候補

一つの候補は、`factor_difference` を書き換えた後に `positivity` を利用する形である。概念的には

```lean
have hdiff := p.factor_difference
have : 0 < (8 : ℤ) * (p.d : ℤ) ^ 5 := by
  have hd : (0 : ℤ) < p.d := by exact_mod_cast p.d_pos
  positivity
linarith
```

のように書ける可能性がある。

別案として、定義を展開して `W_pos` から直接

$$
U-W<U+W
$$

を示すことも考えられる。しかしこれは `factor_difference` という既存 API を迂回するため、proof の局所的短さと全体設計の一貫性を比較する必要がある。

また、`hdiff` の型を明示せず `have hdiff := ...` としている現行形は十分読みやすい。過剰な型注釈を追加する利点は小さい。

これらは本実行では Lean build を行わないため **未検証の最適化候補** とする。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem が直接利用する主要機能は次である。

- `ℤ` の線形順序付き環構造
- `exact_mod_cast`
- `pow_pos`
- `linarith`
- project 側の `GoldenZeroSectorCandidate.factor_difference`
- project 側の `GoldenZeroSectorCandidate.d_pos`

本 theorem 自体は `ring`, `omega`, `norm_num`, `positivity` を直接使用しない。

より狭い Mathlib import へ縮小できる可能性はあるが、正確な最小 import 集合は Lean build 禁止条件のため確認していない。

## Comparator challenge 化の可否

**可能。難度は初級〜中級。**

課題の核は

$$
B-A=8d^5,
\qquad d>0
$$

から

$$
A<B
$$

を Lean で示すことである。

Comparator の比較軸としては次が適している。

- 現行の `exact_mod_cast` → `pow_pos` → `linarith`。
- `positivity` を利用して右辺の strict positivity をまとめて処理する方法。
- `factor_difference` を使う方法と、`A`, `B` の定義および `W_pos` を直接使う方法。
- tactic に任せる範囲と、中間事実を明示して監査性を上げる範囲。
- `ℕ` / `ℤ` coercion をどこで処理するか。

特に `linarith` に非線形項をそのまま考えさせず、`pow_pos` で正性を先に抽出する設計は良い比較教材になる。

## PDF との照合

対象 branch には既存の日英 PDF

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを repository 上で確認した。

ただし GitHub コネクタの通常 text fetch は binary PDF 本文を返さないため、本実行では具体的ページ・節・式番号との直接照合はできていない。その位置については推測しない。

本解説の Lean code、宣言順、直接依存、後続宣言との関係は最新 branch の `Flt5DkMath/FLT5StandAlone.lean` を正本として確認した。

## 次に読むべき宣言

次の宣言は 0316 `GoldenZeroSectorCandidate.A0`、種別は **`def`** である。

Lean 正本では

```lean
/-- Natural representative of the positive lower factor. -/
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs
```

と続く。

0314 で $A>0$、0315 で $A<B$ が確立された後、signed integer factor $A$ を

$$
A_0=|A|\in\mathbb N
$$

として自然数側へ移す段階に入る。次の 0317 は対応する `B0` の定義である。