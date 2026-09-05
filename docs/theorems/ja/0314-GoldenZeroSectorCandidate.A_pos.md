# 0314 — `GoldenZeroSectorCandidate.A_pos`

## 宣言種別

これは **`theorem`** である。

0313 `GoldenZeroSectorCandidate.B_pos` で上側 inversion factor

$$
B>0
$$

が確立された。本 theorem は、0308 `factor_product_twenty` の

$$
AB=20s^4
$$

と candidate の $s<0$ を用いて積が厳密に正であることを示し、`B>0` を符号アンカーとして下側 factor

$$
A>0
$$

を確定する。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- The lower inversion factor is strictly positive. -/
theorem A_pos (p : GoldenZeroSectorCandidate) :
    0 < zeroSectorA p.r p.s p.d := by
  have hsne : p.s ≠ 0 := ne_of_lt p.s_neg
  have hprod : 0 <
      zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d := by
    rw [p.factor_product_twenty]
    positivity
  rcases mul_pos_iff.mp hprod with h | h
  · exact h.1
  · exact (not_lt_of_ge p.B_pos.le h.2).elim
```

結論は `ℤ` 上の strict positivity である。

$$
0<A.
$$

`zeroSectorA` と `zeroSectorB` は

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d

def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

である。

## 数学的意味

0308 より

$$
AB=20s^4.
$$

candidate は $s<0$ を持つため $s\ne0$ であり、したがって

$$
s^4>0,
\qquad
20s^4>0.
$$

ゆえに

$$
AB>0.
$$

整数の積が正ならば、二因子は同符号である。すなわち

$$
(A>0\land B>0)
\quad\text{または}\quad
(A<0\land B<0).
$$

しかし 0313 で $B>0$ が既に証明されているので、後者は不可能である。従って

$$
A>0.
$$

## 証明全体での役割

0309–0311 では inversion factors の積・差・和が exact identity として得られ、0312–0314 でその符号を確定している。

本 theorem により

$$
0<A<B
$$

へ進むためのうち $A>0$ が確立される。直後の 0315 `GoldenZeroSectorCandidate.A_lt_B` は 0310 `factor_difference` と $d>0$ から $A<B$ を示す。

したがって 0314 は、整数上の factorization を後続で正の自然数データへ移すための最後の positivity gate である。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate.s_neg`

candidate が保持する

$$
s<0
$$

から

```lean
have hsne : p.s ≠ 0 := ne_of_lt p.s_neg
```

で $s\ne0$ を得る。この事実を `positivity` が $s^4>0$ の証明に利用する。

### `GoldenZeroSectorCandidate.factor_product_twenty`

0308 の

```lean
theorem factor_product_twenty (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d =
      20 * p.s ^ 4
```

を `rw` で積へ代入する。

### `GoldenZeroSectorCandidate.B_pos`

0313 で確立済みの

$$
B>0
$$

を使い、`mul_pos_iff` の「両方負」の分岐を排除する。

### `mul_pos_iff`

正の積から

$$
(A>0\land B>0)\lor(A<0\land B<0)
$$

という二分岐を取り出す。

## 証明または構築の流れ

1. `p.s_neg` から `hsne : p.s ≠ 0` を得る。
2. `p.factor_product_twenty` で $AB$ を $20s^4$ に書き換える。
3. `positivity` により $20s^4>0$、従って $AB>0$ を示す。
4. `mul_pos_iff.mp hprod` で積が正となる二つの符号ケースへ分解する。
5. 正・正分岐では `h.1` がそのまま $A>0$ である。
6. 負・負分岐では `h.2 : B < 0` と `p.B_pos.le : 0 ≤ B` が矛盾するため、その分岐を消去する。

## Lean 固有の処理

`hsne` はその後の proof term に明示的には現れないが、`positivity` が局所仮定として利用できるため必要である。$s^4$ は偶数冪なので $s\ne0$ から strict positivity が導かれる。

```lean
rcases mul_pos_iff.mp hprod with h | h
```

は ordered ring 上の積の符号を二つのケースに展開する Lean 的な段階である。

負・負ケースでは

```lean
(not_lt_of_ge p.B_pos.le h.2).elim
```

として、`B_pos` そのものではなくその弱化 `0 ≤ B` を `p.B_pos.le` で作り、`B<0` と矛盾させている。

## 冗長・重複箇所

proof は短く、論理構造も明瞭である。ただし `mul_pos_iff` により一度「正・正 / 負・負」の両ケースを展開してから後者を排除しているため、数学的には「$AB>0$ かつ $B>0$ なら $A>0$」という専用の order lemma が利用できればさらに直接的に書ける可能性がある。

また `factor_product_twenty` は後に 0309 `factor_product` で $AB=4Q^5$ へ正規化されているが、本 theorem は $s\ne0$ が直ちに strict positivity を与える 0308 の形を選んでいる。この選択は自然であり、冗長とは言い難い。

## 最適化候補

候補は「正の積」と `B_pos` から直接 `A_pos` を得る order lemma を使う形である。例えば Mathlib に適切な除去 lemma があれば、`mul_pos_iff` の case split を隠蔽できる可能性がある。

一方、現行 proof は使用している論理を完全に露出しており、監査性が高い。短さだけを目的に変更する必然性は低い。

`hsne` と `positivity` の代わりに $s<0$ から `pow_pos` 系補題を明示的に組み立てることも可能だが、現行の方が簡潔である可能性が高い。

これらは本実行では Lean build を行わないため **未検証の最適化候補** とする。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用している。

本 theorem が直接使用する主な機能は次である。

- `ℤ` の線形順序付き環構造
- `ne_of_lt`
- `positivity`
- `mul_pos_iff`
- `not_lt_of_ge`
- project 側の `factor_product_twenty`, `B_pos`

本 theorem 自体では `ring`, `linarith`, `omega`, `exact_mod_cast` は直接使用しない。

Mathlib の最小 import へ縮小できる可能性はあるが、正確な最小集合は Lean build 禁止条件のため確認していない。

## Comparator challenge 化の可否

**可能。難度は初級〜中級。**

課題としては

$$
AB>0,
\qquad
B>0
$$

から

$$
A>0
$$

を Lean で示す方法を比較できる。

Comparator の観点は次の通り。

- 現行 `mul_pos_iff` による符号 case split。
- 積の正性と片方の正性から他方の正性を直接与える order lemma の利用。
- `positivity` に任せる範囲と、$s\ne0$・$s^4>0$ を明示する範囲。
- proof の短さと、符号論理の監査可能性の比較。

## PDF との照合

対象 branch には既存の日英 PDF

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを repository 上で確認した。

ただし GitHub コネクタの通常 text fetch は binary PDF 本文を返さないため、本実行では具体的ページ・節・式番号との直接照合はできていない。その位置については推測しない。

本解説の Lean code、宣言順、直接依存、後続宣言との関係は `Flt5DkMath/FLT5StandAlone.lean` を正本として確認した。

## 次に読むべき宣言

次の宣言は 0315 `GoldenZeroSectorCandidate.A_lt_B`、種別は **`theorem`** である。

Lean 正本では

```lean
/-- The two factors occur in their forced strict order. -/
theorem A_lt_B (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d < zeroSectorB p.r p.s p.d := by
  have hdiff := p.factor_difference
  have hd : (0 : ℤ) < p.d := by exact_mod_cast p.d_pos
  have hpow : (0 : ℤ) < (p.d : ℤ) ^ 5 := pow_pos hd 5
  linarith
```

と続く。

0310 の

$$
B-A=8d^5
$$

と $d>0$ から差が正であることを示し、

$$
A<B
$$

を確定する段階へ進む。