# 0211 — `exists_int_near_rat`

## Lean の型

```lean
/-- Every rational has an integer within one half. -/
theorem exists_int_near_rat (x : ℚ) :
    ∃ n : ℤ, |x - n| ≤ (1 : ℚ) / 2 := by
  exact ⟨round x, abs_sub_round x⟩
```

これは `theorem` であり、任意の有理数 `x` に対して距離 `1/2` 以下の整数 `n` が存在することを示す。

## 数学的主張

主張は最近接整数丸めの基本事実

$$
\forall x\in\mathbb Q,\quad \exists n\in\mathbb Z,\quad |x-n|\le\frac12
$$

である。

証明では整数 witness として Mathlib の `round x` をそのまま選ぶ。すると `abs_sub_round x` が

$$
|x-\operatorname{round}(x)|\le\frac12
$$

を与えるため、存在命題は直ちに閉じる。

この theorem 自体は黄金整数特有ではない。一般の有理数上の丸め補題を `GoldenEuclidean.lean` の局所 API として名前付けし、後続の二座標同時丸めへ接続している。

## 証明全体での役割

0209 `GoldenRat := ℚ × ℚ` と 0210 `goldenRatNorm` で、黄金基底の有理 quotient とその二次ノルム多項式が準備された。本 theorem は、その quotient の各座標を整数格子へ丸めるための一変数版 certificate である。

後続の 0212 `exists_goldenRat_near_int` では、`x.1` と `x.2` の双方について最近接整数を選び、

$$
|x_1-m|\le\frac12,
\qquad
|x_2-n|\le\frac12
$$

を同時に得る。これにより丸め誤差 `(u,v)` は fundamental cell

$$
|u|\le\frac12,
\qquad
|v|\le\frac12
$$

へ入る。

`GoldenEuclidean.lean` の module 方針は、この cell 上で

$$
|u^2+uv-v^2|\le\frac{5}{16}<1
$$

を示し、remainder の絶対ノルムを divisor より真に小さくすることにある。したがって 0211 は単純な rounding lemma だが、norm-Euclidean division の「誤差を bounded cell に入れる」最初の実働部である。

## 直接依存する定義・補題

直接依存は次の通りである。

- 有理数型 `ℚ`
- 整数型 `ℤ`
- 絶対値 `|x|`
- Mathlib の `round x : ℤ`
- Mathlib の `abs_sub_round x`

`GoldenRat` や `goldenRatNorm` は theorem の型には直接現れない。依存順では Euclidean 構築の文脈上 0209–0210 の直後に置かれているが、Lean の直接依存としては一般的な ordered-field rounding API だけで閉じている。

概念的には

$$
x\in\mathbb Q
\longmapsto
\operatorname{round}(x)\in\mathbb Z
\longmapsto
|x-\operatorname{round}(x)|\le\frac12
$$

である。

## 証明の流れ

proof は一行だけである。

```lean
exact ⟨round x, abs_sub_round x⟩
```

1. existential witness `n : ℤ` として `round x` を選ぶ。
2. 残る goal は `|x - round x| ≤ 1/2`。
3. `abs_sub_round x` がその goal と一致するので、そのまま certificate として渡す。

新たな不等式計算や場合分けは一切行わない。Mathlib に既に存在する最近接整数 theorem を局所 theorem として再公開しているだけである。

## Lean 固有の処理

`⟨round x, abs_sub_round x⟩` は existential constructor の省略記法である。期待型

```lean
∃ n : ℤ, |x - n| ≤ (1 : ℚ) / 2
```

から Lean は第一成分 `round x` を witness `n` として解釈し、第二成分に witness 代入後の証明を要求する。

`round x` の返り値は `ℤ` である。一方 `x - n` では `n : ℤ` が有理数へ coercion されるため、差と絶対値は `ℚ` 上で計算される。右辺の `(1 : ℚ) / 2` は型注釈により有理数の `1/2` と固定されている。

この coercion は statement に隠れているが、`abs_sub_round` の型がちょうど同じ cast convention を採用しているため、`simpa` や cast rewrite を挟まず exact に一致する。

## 冗長・重複箇所

論理的には、この theorem は Mathlib の `abs_sub_round` の existential packaging に過ぎないため、独立した数学情報はほぼ増えていない。

後続 0212 `exists_goldenRat_near_int` も source 上では `round x.1` と `round x.2`、`abs_sub_round` を直接使って witness を構成できるため、実装上 0211 を経由せずとも証明できる。この意味では API-level の冗長性がある。

一方、名前付き theorem にする利点もある。

- Euclidean proof の一変数 rounding primitive が明示される。
- Mathlib の具体 lemma 名を downstream から隠せる。
- 将来 rounding policy を変更しても局所 API を保てる。
- Comparator や教科書的解説で一変数→二変数の依存段階を明確にできる。

したがって、実装最小化より proof architecture の可読性を優先した wrapper と見るのが自然である。

## 最適化候補

1. **0212 から本 theorem を明示的に再利用する**
   - 現行 0212 が `abs_sub_round` を直接二回使うなら、`exists_int_near_rat x.1` / `x.2` を呼ぶことで dependency graph がより教科書的になる。

2. **本 theorem を削除し Mathlib lemma を直接使用する**
   - コード量は減るが、Euclidean 丸め API の入口が見えにくくなる。

3. **strict / tie-breaking 版を分離する**
   - 現在は `≤ 1/2` であり、半整数では equality が起こりうる。後続が strict inequality を必要としない限り現行で十分だが、tie-breaking が重要になる場合は専用 theorem を追加できる。

4. **一般化可能性を検討する**
   - `ℚ` 固有ではなく、rounding structure を持つ型への一般化も理論上可能。ただし本 formalization では有理 quotient が目的なので抽象化コストが勝つ可能性が高い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 単独で必要なのは、実質的に有理数・整数の rounding と absolute-value order API である。

具体的には `round` と `abs_sub_round` を提供する Mathlib の rounding 関連 module が中心依存になる。ただし今回 Lean build は行わないため、`import Mathlib` からどの最小 module 群まで削れるかは未検証である。したがって exact な最小 import 名は推測で断定せず、import 最適化候補として残す。

`GoldenEuclidean.lean` 全体では後続に rational/Int cast、不等式、`ring`、Euclidean-domain 構築などがあるため、module 単位の最小 import は本 theorem 単独より広い。

## Comparator challenge 化の可否

適している。小さいが proof/API 設計の差が明確である。

比較候補は次の通り。

- A: 現行 `⟨round x, abs_sub_round x⟩`
- B: floor / ceil を場合分けして距離 `1/2` を手で証明
- C: 0211 を削除し 0212 で `abs_sub_round` を直接二回使用
- D: 0212 が 0211 を二回呼ぶ layered API

比較軸は proof 長、Mathlib 依存、dependency graph の明瞭さ、coercion burden、rounding policy の交換可能性、後続 proof の読みやすさである。

特に C と D の比較は、薄い wrapper theorem が theorem museum / auditability にどれだけ価値を持つかを見る良い課題になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

正本 source では 0210 `goldenRatNorm` の直後に本 theorem があり、その次に 0212 `exists_goldenRat_near_int` が続く。

```lean
/-- Every rational has an integer within one half. -/
theorem exists_int_near_rat (x : ℚ) :
    ∃ n : ℤ, |x - n| ≤ (1 : ℚ) / 2 := by
  exact ⟨round x, abs_sub_round x⟩

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

依存順の次は **0212 `exists_goldenRat_near_int`** である。

```lean
/-- Simultaneous nearest-lattice rounding in the golden basis. -/
theorem exists_goldenRat_near_int (x : GoldenRat) :
    ∃ m n : ℤ,
      |x.1 - m| ≤ (1 : ℚ) / 2 ∧
      |x.2 - n| ≤ (1 : ℚ) / 2 := by
  exact ⟨round x.1, round x.2,
    abs_sub_round x.1, abs_sub_round x.2⟩
```

0211 が一つの有理座標を整数から距離 `1/2` 以内へ丸められることを保証したのに対し、0212 は黄金基底の二座標を同時に丸め、Euclidean contraction に必要な fundamental cell を直接構成する。