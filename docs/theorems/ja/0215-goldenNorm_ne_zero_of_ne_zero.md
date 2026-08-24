# 0215 — `goldenNorm_ne_zero_of_ne_zero`

## Lean の型

```lean
theorem goldenNorm_ne_zero_of_ne_zero {y : GoldenInt} (hy : y ≠ 0) :
    goldenNorm y ≠ 0 := by
  intro hn
  have hm : goldenMul y (goldenConj y) = 0 := by
    rw [golden_mul_conj, hn]
    rfl
  rcases mul_eq_zero.mp hm with hy0 | hc0
  · exact hy hy0
  · apply hy
    rw [← goldenConj_invol y, hc0]
    rfl
```

これは `theorem` であり、非零な黄金整数のノルムが 0 にはならないことを示す。

## 数学的主張

主張は

$$
y\neq0\Longrightarrow N(y)\neq0
$$

である。

黄金整数では 0176 `golden_mul_conj` により

$$
y\overline y=N(y)
$$

が環内部の等式として成立する。仮に $N(y)=0$ なら

$$
y\overline y=0.
$$

`GoldenInt` は 0155 までで整域として登録されているので零積分解から

$$
y=0\quad\text{or}\quad\overline y=0
$$

を得る。前者は仮定 `hy : y ≠ 0` に矛盾し、後者も 0170 `goldenConj_invol` により

$$
y=\overline{\overline y}=0
$$

となって矛盾する。したがって $N(y)\neq0$ である。

## 証明全体での役割

`GoldenEuclidean.lean` では 0209–0214 までに、最近接整数丸めによる quotient error のノルムが厳密に 1 未満になることを確立した。本 theorem はその直後に置かれ、Euclidean division のもう一つの前提である **非零 divisor の norm を分母に使えること** を保証する。

後続の `goldenQuotientCoords` は

```lean
def goldenQuotientCoords (x y : GoldenInt) : GoldenRat :=
  (((goldenQuotientNumerator x y).fst : ℚ) / goldenNorm y,
    ((goldenQuotientNumerator x y).snd : ℚ) / goldenNorm y)
```

と定義される。したがって `y ≠ 0` のとき `goldenNorm y ≠ 0` が必要になる。

さらに下流の `goldenRemainder_norm_rat_identity` でも

```lean
have hn : (goldenNorm y : ℚ) ≠ 0 := by
  exact_mod_cast goldenNorm_ne_zero_of_ne_zero hy
```

として本 theorem が直接利用され、`field_simp` の分母非零条件を供給する。`goldenEuclideanSize_pos_of_ne_zero` でも `Int.natAbs_pos` と組み合わせて Euclidean size の正値性を導くために再利用される。

## 直接依存する定義・補題

直接依存は次の通りである。

- 0176 `golden_mul_conj`
- 0170 `goldenConj_invol`
- `goldenConj`
- `goldenMul`
- `goldenNorm`
- `mul_eq_zero`
- 0153–0155 で整備された `NoZeroDivisors` / `IsDomain GoldenInt`

概念的には

$$
N(y)=0
\Longrightarrow
y\overline y=0
\Longrightarrow
y=0\lor\overline y=0
\Longrightarrow
y=0
$$

という反証法である。

## 証明の流れ

### 1. ノルム 0 を仮定する

```lean
intro hn
```

目標 `goldenNorm y ≠ 0` を否定の形として開き、`hn : goldenNorm y = 0` を仮定する。

### 2. 元と共役の積が 0 であることを得る

```lean
have hm : goldenMul y (goldenConj y) = 0 := by
  rw [golden_mul_conj, hn]
  rfl
```

`golden_mul_conj` により積を `goldenOfInt (goldenNorm y)` に変換し、`hn` で norm を 0 にする。最後は `goldenOfInt 0 = 0` が定義的に成立するため `rfl` で閉じる。

### 3. 零積分解する

```lean
rcases mul_eq_zero.mp hm with hy0 | hc0
```

整域 API により

- `hy0 : y = 0`
- `hc0 : goldenConj y = 0`

の二場合に分ける。

### 4. 両分岐を `hy` で矛盾させる

第一分岐は直接

```lean
exact hy hy0
```

で閉じる。

第二分岐では共役を二回取ると元に戻ることを使い、

```lean
apply hy
rw [← goldenConj_invol y, hc0]
rfl
```

として `y = 0` を導く。

## Lean 固有の処理

`mul_eq_zero.mp hm` は `GoldenInt` に登録済みの zero-divisor-free algebra structure を typeclass inference で利用する。ここで座標を展開して二次形式 $a^2+ab-b^2=0$ を直接解析しているのではない点が重要である。

また第二分岐の

```lean
rw [← goldenConj_invol y, hc0]
```

では involution theorem を逆向きに使って `y` を `goldenConj (goldenConj y)` に置き換え、その内側を `hc0` で 0 にする。`goldenConj 0 = 0` は定義展開で閉じるため最後は `rfl` になる。

この proof は、既に構築済みの環構造・共役 API を再利用する構造的証明であり、`ring` や `norm_num` は不要である。

## 冗長・重複箇所

数学的には「ノルム 0 なら元 0」という性質は、`golden_mul_conj` と整域性からほぼ自動的に従うため、一般 lemma に抽象化できる余地がある。

また第二分岐は `goldenConj_invol` を明示して元へ戻しているが、将来 `goldenConj` を `RingEquiv` として bundle すれば、その injectivity を使って

```lean
goldenConj y = 0 → y = 0
```

をより直接的に処理できる可能性がある。

一方、本 theorem を named API として残す価値は高い。後続では「分母 `goldenNorm y` が非零」という形が直接必要であり、毎回 `y * conj y` の零積議論を展開するより意図が明瞭だからである。

## 最適化候補

1. **共役を `RingEquiv` として bundle する**
   - involution から injectivity を一般 API で得て第二分岐を簡略化できる。

2. **一般 norm-zero helper を作る**
   - `x * conj x = algebraMap (N x)` 型の一般構造があるなら、`N x = 0 ↔ x = 0` を抽象化できる。

3. **逆向き iff を公開する**
   - `goldenNorm y = 0 ↔ y = 0` を theorem 化すると downstream の rewrite usability が上がる可能性がある。

4. **現行 theorem を維持する**
   - Euclidean quotient の分母安全性という consumer-facing API としては非常に明確であり、局所 proof も十分短い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が直接必要とする主な表面は、

- zero-product lemma `mul_eq_zero`
- equality rewriting
- `GoldenInt` の `IsDomain` / `NoZeroDivisors` instance
- 上流の共役・ノルム theorem

である。

`ring`、`nlinarith`、`norm_num`、`round` などは本 theorem 自体では使用しない。ただし同じ `GoldenEuclidean.lean` module ではこれらを広く使用するため、module 単位の最小 import はかなり広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 `golden_mul_conj` + `mul_eq_zero` + involution
- B: 座標を展開し $a^2+ab-b^2=0$ から直接 `a=b=0` を示す
- C: `goldenConj` を `RingEquiv` 化し injectivity を利用する
- D: `goldenNorm y = 0 ↔ y = 0` を先に一般 theorem として作る
- E: `IsDomain` の generic norm-like API へ抽象化する

比較軸は、proof 長、座標依存度、Mathlib algebra API 再利用率、数学的 provenance、下流 quotient proof での使いやすさである。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

source では 0214 `goldenRat_norm_abs_lt_one` の直後に本 theorem が置かれ、その次に `goldenQuotientNumerator` が続く。また下流の `goldenEuclideanSize_pos_of_ne_zero` と `goldenRemainder_norm_rat_identity` が本 theorem を直接使用している。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、本 theorem に対応する具体的ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0216 `goldenQuotientNumerator`** である。

```lean
/-- Numerator coordinates of `x * conjugate(y)`. -/
def goldenQuotientNumerator (x y : GoldenInt) : GoldenInt :=
  goldenMul x (goldenConj y)
```

0215 で非零 divisor の norm が非零であることを保証したので、0216 からは有理 quotient

$$
\frac{x\overline y}{N(y)}
$$

を座標として実装する段階へ進む。まず分子 `x * conjugate(y)` を明示的な `GoldenInt` として名前付けし、その後二座標の展開と `goldenQuotientCoords` へ進む。
