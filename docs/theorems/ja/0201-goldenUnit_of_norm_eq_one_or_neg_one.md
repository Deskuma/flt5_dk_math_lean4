# 0201 — `goldenUnit_of_norm_eq_one_or_neg_one`

## Lean の型

```lean
theorem goldenUnit_of_norm_eq_one_or_neg_one {x : GoldenInt}
    (h : goldenNorm x = 1 ∨ goldenNorm x = -1) : GoldenUnit x :=
  h.elim goldenUnit_of_norm_eq_one goldenUnit_of_norm_eq_neg_one
```

これは `theorem` であり、黄金整数 `x` のノルムが `1` または `-1` なら、`x` が `GoldenUnit`、すなわち黄金整数環の単元であることを示す。

## 数学的主張

主張は

$$
N(x)=1\ \lor\ N(x)=-1
\Longrightarrow
GoldenUnit(x)
$$

である。

0199 `goldenUnit_of_norm_eq_one` では

$$
N(x)=1
\Longrightarrow
GoldenUnit(x)
$$

を、共役 `goldenConj x` を逆元として構成することで証明した。

0200 `goldenUnit_of_norm_eq_neg_one` では

$$
N(x)=-1
\Longrightarrow
GoldenUnit(x)
$$

を、符号を補正した `-goldenConj x` を逆元として構成することで証明した。

0201 はこの二つの分岐を論理和消去でまとめるだけであり、新しい代数計算は行わない。

## 証明全体での役割

0199 と 0200 は norm `1` / `-1` の各 branch を具体的に構成した。本 theorem はその二本を一つの公開 API に束ね、以後の proof がノルムの符号ごとの逆元構成を意識せずに

$$
N(x)=\pm1
$$

という条件だけから unit 性へ進めるようにする。

この直後の `goldenNorm_eq_one_or_neg_one_of_unit` は逆向き

$$
GoldenUnit(x)
\Longrightarrow
N(x)=1\ \lor\ N(x)=-1
$$

を証明する。したがって 0201 とその次の theorem が揃うことで、黄金整数における単元判定

$$
GoldenUnit(x)
\iff
N(x)=\pm1
$$

が完成する。

この criterion は `goldenUnit_phi`、`goldenUnit_one`、`goldenUnit_neg`、`goldenUnit_mul`、`goldenUnit_pow`、最終的な `GoldenRelPrime` の議論へ接続する。

## 直接依存する定義・補題

直接依存は極めて明快である。

- 0198 `GoldenUnit`
- 0199 `goldenUnit_of_norm_eq_one`
- 0200 `goldenUnit_of_norm_eq_neg_one`
- `Or.elim`

概念的には

$$
\bigl(N(x)=1\to GoldenUnit(x)\bigr)
+
\bigl(N(x)=-1\to GoldenUnit(x)\bigr)
\Longrightarrow
\bigl(N(x)=1\lor N(x)=-1\bigr)\to GoldenUnit(x).
$$

本 theorem 自身は `goldenConj`、`goldenMul`、`goldenNorm_mul` などを直接触らず、それらの具体的な algebraic work を 0199/0200 に完全に委譲している。

## 証明の流れ

証明は一行である。

```lean
h.elim goldenUnit_of_norm_eq_one goldenUnit_of_norm_eq_neg_one
```

`h` は

```lean
h : goldenNorm x = 1 ∨ goldenNorm x = -1
```

なので、`Or.elim` は次の二つの関数を要求する。

```lean
goldenNorm x = 1  → GoldenUnit x

goldenNorm x = -1 → GoldenUnit x
```

ちょうど 0199 と 0200 がその型を持つため、そのまま渡せば goal `GoldenUnit x` が閉じる。

## Lean 固有の処理

`h.elim` は `Or.elim h` の method-style 表記である。

Lean は期待型 `GoldenUnit x` と仮定 `h` の左右の型から、

```lean
goldenUnit_of_norm_eq_one
```

および

```lean
goldenUnit_of_norm_eq_neg_one
```

を `x` に暗黙に特殊化する。

そのため `cases h with` や branch ごとの `exact` を書く必要がない。

同じ証明を展開すれば概念的には

```lean
by
  rcases h with h1 | hm1
  · exact goldenUnit_of_norm_eq_one h1
  · exact goldenUnit_of_norm_eq_neg_one hm1
```

である。現行形はこの case split を `Or.elim` に圧縮している。

## 冗長・重複箇所

0201 自身には実質的な重複はない。むしろ 0199/0200 の二本に分散していた branch を一つの API に統合するための theorem である。

ただし API 全体として見ると、

- `goldenUnit_of_norm_eq_one`
- `goldenUnit_of_norm_eq_neg_one`
- `goldenUnit_of_norm_eq_one_or_neg_one`

の三本は、用途によってはやや細かく分かれているとも言える。

一方、個別 branch theorem を残す利点も明確である。特定の norm 値が既に分かっている場合、論理和を作る必要なく直接使えるためである。

したがってこれは不要な重複というより、specific theorem と combined theorem を両立させた API layering と見るのが自然である。

## 最適化候補

1. **現行の一行 proof を維持する**
   - すでに最短級であり、改善余地はほとんどない。

2. **`cases` 形式へ展開する**
   - 教育的には branch が見やすいが、コード量は増える。

3. **unit criterion を双方向 theorem としてまとめる**
   - 次の converse と合わせて

```lean
GoldenUnit x ↔ goldenNorm x = 1 ∨ goldenNorm x = -1
```

   を公開すれば downstream の rewrite usability が上がる可能性がある。

4. **Mathlib `IsUnit` へ寄せる**
   - `GoldenUnit` 専用 API を標準 unit API と接続すれば、一般環論 lemma を再利用しやすくなる。

5. **norm を multiplicative map として bundle する**
   - unit と norm `±1` の関係をより抽象的に整理できる可能性がある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が直接必要とする Lean/Mathlib 表面は非常に小さい。

- `Or`
- `Or.elim`
- 0199 / 0200 の theorem
- `GoldenUnit`

`ring`、`norm_num`、`rw` すら本 theorem 自身では使用しない。

したがって宣言単独では極めて軽量だが、同一 `GoldenDivisibility` module の上流 theorem が共役・ノルム・整数算術を利用するため、module 全体の最小 import はそれらに支配される。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

小さいが可能である。比較候補は次の通り。

- A: 現行 `h.elim ... ...`
- B: `rcases h with h | h` による明示 case split
- C: `cases h <;> aesop` 等による自動化
- D: norm-unit equivalence theorem を先に作り、その forward direction を利用
- E: Mathlib `IsUnit` 中心の一般化

比較軸は proof term の小ささ、可読性、branch の明示性、自動化依存、API 再利用性、教育的透明性である。

ただし現行 proof はすでに極めて直接的なので、Comparator challenge としては proof-performance より API design 比較の方が面白い。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

直前の 0200 文書では、本 theorem が次の宣言として明示されており、その Lean 型も確認できる。

対象ブランチには日本語・英語 PDF が存在するが、本 theorem に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0202 `goldenNorm_eq_one_or_neg_one_of_unit`** である。

```lean
theorem goldenNorm_eq_one_or_neg_one_of_unit {x : GoldenInt}
    (h : GoldenUnit x) : goldenNorm x = 1 ∨ goldenNorm x = -1 := by
  rcases h with ⟨y, hxy, _⟩
  have hn : goldenNorm x * goldenNorm y = 1 := by
    rw [← goldenNorm_mul, hxy]
    norm_num [goldenNorm, goldenOne]
  exact Int.eq_one_or_neg_one_of_mul_eq_one hn
```

0201 が norm `±1` から unit への方向を完成させたのに対し、0202 は unit witness からノルム積が `1` になることを導き、整数の積が `1` なら各因子が `±1` であることを使って逆向きを証明する。