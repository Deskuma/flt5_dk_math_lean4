# 0313 — `GoldenZeroSectorCandidate.B_pos`

## 宣言種別

これは **`theorem`** である。

0312 `GoldenZeroSectorCandidate.W_pos` で

$$
W>0
$$

を確立した。0305 `GoldenZeroSectorCandidate.U_nonneg` の

$$
U\ge0
$$

と合わせ、本 theorem は上側 inversion factor

$$
B=U+W
$$

が厳密に正であることを示す。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- The upper inversion factor is strictly positive. -/
theorem B_pos (p : GoldenZeroSectorCandidate) :
    0 < zeroSectorB p.r p.s p.d := by
  unfold zeroSectorB
  linarith [p.U_nonneg, p.W_pos]
```

結論は `ℤ` 上の strict positivity である。

$$
0<B.
$$

`zeroSectorB` は

```lean
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

すなわち

$$
B(r,s,d)=U(r,s)+W(d)
$$

である。

## 数学的意味

既に

$$
U\ge0,
\qquad
W>0
$$

が証明されているので、単調性から直ちに

$$
U+W>0
$$

である。従って

$$
B>0.
$$

これは新しい数論的恒等式ではなく、これまでに構成した inversion coordinates に order information を付加する補題である。

## 証明全体での役割

0309 では

$$
AB=4Q^5,
$$

0310 では

$$
B-A=8d^5,
$$

0311 では

$$
A+B=2U
$$

が得られている。しかし積・差・和だけでは、整数因子 `A`,`B` の符号はまだ自動的には固定されない。

0312 が `W>0` を与え、本 theorem が `B>0` を確立する。直後の 0314 `GoldenZeroSectorCandidate.A_pos` は、積

$$
AB=20s^4>0
$$

と本 theorem の `B>0` を用いて `A>0` を導く。

したがって 0313 は、整数上の inversion factors を後続で自然数として扱うための positivity chain の中間点である。

## 直接依存する定義・補題

### `zeroSectorB`

```lean
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

proof 冒頭の `unfold zeroSectorB` により、目標は `U+W>0` の形へ変わる。

### `GoldenZeroSectorCandidate.U_nonneg`

0305 で証明済みの

```lean
theorem U_nonneg (p : GoldenZeroSectorCandidate) :
    0 ≤ zeroSectorU p.r p.s := by
  unfold zeroSectorU
  positivity
```

であり、

$$
U\ge0
$$

を供給する。

### `GoldenZeroSectorCandidate.W_pos`

0312 で証明済みの

$$
W>0
$$

を供給する。本 theorem の strict positivity を生む側の仮定である。

### `linarith`

`U\ge0` と `W>0` から `U+W>0` を線形算術として閉じる。

## 証明または構築の流れ

1. `unfold zeroSectorB` により目標を

$$
0<U+W
$$

へ展開する。
2. `p.U_nonneg` から

$$
0\le U
$$

を得る。
3. `p.W_pos` から

$$
0<W
$$

を得る。
4. `linarith` が二つの不等式を合成し、`0<U+W` を閉じる。

## Lean 固有の処理

数学的には「非負数と正数の和は正」という一行の order argument である。現行 Lean proof は、その専用 order lemma を直接呼ぶ代わりに `linarith` に線形不等式の合成を任せている。

0312 と異なり、本 theorem 自体には `ℕ`/`ℤ` cast は現れない。`W_pos` 側で `d : ℕ` から `ℤ` への移送が既に完了しているため、ここでは `zeroSectorU ... : ℤ` と `zeroSectorW ... : ℤ` が同一の ordered ring 上に揃っている。

`ring`、`nlinarith`、`omega` は不要である。

## 冗長・重複箇所

proof は

```lean
unfold zeroSectorB
linarith [p.U_nonneg, p.W_pos]
```

の 2 行だけであり、局所的な冗長性はほぼない。

ただし内容は一般的な order lemma

$$
0\le U,\quad 0<W \Longrightarrow 0<U+W
$$

そのものであり、`linarith` は問題の強さに比べれば汎用的で重い tactic である。これは誤りではないが、proof dependency をより明示したい場合には簡約余地がある。

## 最適化候補

より構造的には、例えば次の形が候補になる。

```lean
unfold zeroSectorB
exact add_pos_of_nonneg_of_pos p.U_nonneg p.W_pos
```

あるいは `simpa [zeroSectorB]` を用いて同じ order lemma を適用する形も考えられる。

この形なら `linarith` への依存を外し、「非負 + 正 = 正」という proof の意味が declaration level で明示される。

ただし本実行では Lean build を行わない条件のため、上記置換が現在の Mathlib API 名・引数順でそのまま通るかは **未検証の最適化候補** とする。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用している。

現行 proof が直接必要とする機能は少なくとも次である。

- `ℤ` の線形順序・加法
- `linarith`
- project 側の `zeroSectorB`, `U_nonneg`, `W_pos`

本 theorem 自体では `ring`、`positivity`、`exact_mod_cast` は直接使用しない。

専用 order lemma に置換できれば `linarith` 依存も不要になる可能性が高く、import の縮小にも有利である。ただし正確な最小 import 集合は Lean build 禁止条件のため確認していない。

## Comparator challenge 化の可否

**可能。難度は初級。**

課題としては、既知の

$$
U\ge0,
\qquad
W>0
$$

から

$$
B=U+W>0
$$

を Lean で最も明瞭に示す方法を比較できる。

Comparator の観点は次の通り。

- 現行の `linarith` proof。
- `add_pos_of_nonneg_of_pos` 型の order lemma による直接 proof。
- `simpa [zeroSectorB]` を組み合わせた短縮形。
- tactic の自動化度と、依存関係の可読性・import 範囲の比較。

数学的難度は低いが、Lean proof engineering の比較には適した小さな challenge である。

## PDF との照合

対象 branch には既存の日英 PDF

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを repository 上で確認した。

ただし GitHub コネクタの通常 text fetch は binary PDF 本文を返さないため、本実行では具体的ページ・節・式番号との直接照合はできていない。その位置については推測しない。

本解説の Lean code、宣言順、直接依存、後続宣言との関係は `Flt5DkMath/FLT5StandAlone.lean` を正本として確認した。

## 次に読むべき宣言

次の宣言は 0314 `GoldenZeroSectorCandidate.A_pos`、種別は **`theorem`** である。

Lean 正本では

```lean
/-- The lower inversion factor is strictly positive. -/
theorem A_pos (p : GoldenZeroSectorCandidate) :
    0 < zeroSectorA p.r p.s p.d := by
  have hsne : p.s ≠ 0 := ne_of_lt p.s_neg
  have hprod : 0 <
      zeroSectorA p.r p.s p.d * zeroSectorB p.r p.s p.d := by
    rw [p.factor_product_twenty]
    positivity
  exact (mul_pos_iff.mp hprod).resolve_right (by
    exact not_and_of_not_left _ (not_lt_of_ge (le_of_lt p.B_pos)))
```

と続く。

0313 の

$$
B>0
$$

を符号アンカーとして、正の積 `AB>0` から

$$
A>0
$$

を確定する段階へ進む。