# 0212 — `exists_goldenRat_near_int`

## Lean の型

```lean
/-- Simultaneous nearest-lattice rounding in the golden basis. -/
theorem exists_goldenRat_near_int (x : GoldenRat) :
    ∃ m n : ℤ,
      |x.1 - m| ≤ (1 : ℚ) / 2 ∧
      |x.2 - n| ≤ (1 : ℚ) / 2 := by
  exact ⟨round x.1, round x.2,
    abs_sub_round x.1, abs_sub_round x.2⟩
```

これは `theorem` であり、黄金基底の有理座標 `x = (x.1, x.2)` に対して、それぞれ距離 `1/2` 以下の整数座標 `m,n` を同時に選べることを示す。

## 数学的主張

0209 で

```lean
abbrev GoldenRat := ℚ × ℚ
```

と定義されているので、`x : GoldenRat` は

$$
x=(u,v),\qquad u,v\in\mathbb Q
$$

という黄金基底 `1,φ` 上の有理座標を表す。

本 theorem の主張は

$$
\forall (u,v)\in\mathbb Q^2,\quad
\exists m,n\in\mathbb Z,
\quad |u-m|\le\frac12,
\quad |v-n|\le\frac12
$$

である。

つまり各座標を最近接整数へ丸めることで、丸め誤差

$$
U=u-m,\qquad V=v-n
$$

を fundamental cell

$$
|U|\le\frac12,
\qquad
|V|\le\frac12
$$

へ同時に押し込める。

## 証明全体での役割

`GoldenEuclidean.lean` の目的は、`GoldenInt` を norm-Euclidean domain として構成することである。そのためには、任意の有理 quotient を黄金整数格子へ丸め、remainder の絶対ノルムが divisor より真に小さくなることを示す必要がある。

0209 `GoldenRat` と 0210 `goldenRatNorm` により、有理 quotient とそのノルム形式

$$
Q(u,v)=u^2+uv-v^2
$$

が用意された。0211 `exists_int_near_rat` は一座標について最近接整数を与え、本 theorem はその二座標版として Euclidean proof に必要な square cell を直接構成する。

直後の 0213 `goldenRat_norm_abs_le_five_sixteen` は、この cell 上で

$$
|u^2+uv-v^2|\le\frac{5}{16}
$$

を証明する。さらに `5/16 < 1` から strict contraction が得られ、後続の `golden_remainder_size_lt` において

$$
|N(r)|<|N(y)|
$$

へつながる。

したがって 0212 は、抽象的な quotient を「ノルムが一様に縮む領域」へ移す nearest-lattice normalization の入口である。

## 直接依存する定義・補題

直接依存は次の通りである。

- 0209 `GoldenRat := ℚ × ℚ`
- Mathlib の `round`
- Mathlib の `abs_sub_round`
- 有理数型 `ℚ`
- 整数型 `ℤ`
- 絶対値と順序構造

証明は 0211 `exists_int_near_rat` を直接使用していない。source では `round` と `abs_sub_round` を各座標へ直接二回適用している。

概念的には

$$
(u,v)
\longmapsto
(\operatorname{round}(u),\operatorname{round}(v))
\longmapsto
(U,V)\in[-1/2,1/2]^2
$$

である。

## 証明の流れ

proof は witness と certificate を一度に組み立てる。

```lean
exact ⟨round x.1, round x.2,
  abs_sub_round x.1, abs_sub_round x.2⟩
```

1. `m : ℤ` として `round x.1` を選ぶ。
2. `n : ℤ` として `round x.2` を選ぶ。
3. 第一座標の誤差 bound を `abs_sub_round x.1` で与える。
4. 第二座標の誤差 bound を `abs_sub_round x.2` で与える。
5. 二つの不等式は conjunction としてまとめられ、存在命題が閉じる。

追加の算術、場合分け、`linarith`、`ring` は不要である。

## Lean 固有の処理

結論は

```lean
∃ m n : ℤ,
  |x.1 - m| ≤ (1 : ℚ) / 2 ∧
  |x.2 - n| ≤ (1 : ℚ) / 2
```

という入れ子の existential と conjunction である。

したがって

```lean
⟨round x.1, round x.2,
  abs_sub_round x.1, abs_sub_round x.2⟩
```

という flat-looking な constructor 記法でも、Lean は期待型から

- 第一 existential witness
- 第二 existential witness
- conjunction の左証明
- conjunction の右証明

へ順に対応付ける。

`round x.1` と `round x.2` の型は `ℤ` だが、`x.1 - m` と `x.2 - n` では整数 witness が自動的に `ℚ` へ coercion される。`abs_sub_round` が同じ cast convention を採用しているため、`norm_cast` や `simpa` を挟まず exact に一致する。

## 冗長・重複箇所

0211 `exists_int_near_rat` は既に一変数版を公開しているが、本 theorem はそれを呼ばず、Mathlib の `round` / `abs_sub_round` を直接二回使っている。

このため proof architecture 上は軽い重複がある。

- 0211: 一座標 wrapper
- 0212: 同じ primitive を二座標へ直接適用

0212 を 0211 経由で書くなら、例えば各座標の witness を `rcases` で取り出して結合する設計が可能である。ただし現行 proof は一行で非常に短く、dependency depth も浅い。

また `GoldenRat` 自体が `ℚ × ℚ` の `abbrev` なので、`.1` / `.2` を使う tuple API が繰り返される。将来座標に意味付き field 名が必要なら専用 structure 化も候補になるが、現段階では軽量な pair 表現の利点が大きい。

## 最適化候補

1. **0211 を明示的に再利用する**
   - 一変数→二変数という dependency graph を明確化できる。

2. **現行の直接 witness 構築を維持する**
   - 最短で、Mathlib primitive への依存も明示的。

3. **丸め関数を専用定義として切り出す**
   - 例えば `goldenRatRound : GoldenRat → GoldenInt` を定義し、0212 をその誤差 bound として整理する。
   - 実際の `goldenQuotient` と概念を共有しやすくなる可能性がある。

4. **fundamental-cell predicate を定義する**
   - `|u| ≤ 1/2 ∧ |v| ≤ 1/2` を専用 predicate にすると、0212→0213→strict contraction の API が読みやすくなる可能性がある。

5. **一般 lattice rounding への抽象化を比較する**
   - 本 formalization では二次元黄金格子に特化しているため、一般化コストが利益を上回る可能性が高い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 単独で必要な Mathlib 表面は主に、有理数・整数・最近接整数丸め・絶対値・順序である。

具体的な最小 import 名は今回 Lean build を行わないため未検証である。したがって `Mathlib` 全体からどこまで削減できるかは import 最適化候補としてのみ記録する。

`GoldenEuclidean.lean` 全体では後続に `nlinarith`、`linarith`、`ring`、`field_simp`、cast 処理、Euclidean-domain 構築などが現れるため、module 全体の必要 import は 0212 単独よりかなり広い。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行の `round` / `abs_sub_round` を二座標へ直接適用
- B: 0211 `exists_int_near_rat` を二回再利用
- C: `goldenRatRound` のような専用 rounding function を定義
- D: floor / ceil から手動で二座標 bound を構成

比較軸は、proof 長、dependency graph の明瞭さ、cast burden、Mathlib primitive 依存、後続 Euclidean proof との接続性、API の再利用性である。

特に A と B の比較は、薄い wrapper theorem を dependency graph に明示的に使う価値を測る良い Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

source では 0211 の直後に本 theorem があり、その次に 0213 `goldenRat_norm_abs_le_five_sixteen` が続く。

```lean
/-- Simultaneous nearest-lattice rounding in the golden basis. -/
theorem exists_goldenRat_near_int (x : GoldenRat) :
    ∃ m n : ℤ,
      |x.1 - m| ≤ (1 : ℚ) / 2 ∧
      |x.2 - n| ≤ (1 : ℚ) / 2 := by
  exact ⟨round x.1, round x.2,
    abs_sub_round x.1, abs_sub_round x.2⟩
```

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、本 theorem に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0213 `goldenRat_norm_abs_le_five_sixteen`** である。

```lean
/--
The square fundamental cell is a strict golden-norm contraction cell.
The sharp uniform constant is `5/16`.
-/
theorem goldenRat_norm_abs_le_five_sixteen
    {u v : ℚ}
    (hu : |u| ≤ (1 : ℚ) / 2)
    (hv : |v| ≤ (1 : ℚ) / 2) :
    |u ^ 2 + u * v - v ^ 2| ≤ (5 : ℚ) / 16 := by
  ...
```

0212 が丸め誤差を square cell `[-1/2,1/2]^2` に入れたので、0213 はその cell 全体で黄金ノルム二次形式を `5/16` 以下に抑える。ここが Euclidean contraction の定量的核心になる。