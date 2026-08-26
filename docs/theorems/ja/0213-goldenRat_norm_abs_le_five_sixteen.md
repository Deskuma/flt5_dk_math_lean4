# 0213 — `goldenRat_norm_abs_le_five_sixteen`

## Lean の型

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
  have hu' := abs_le.mp hu
  have hv' := abs_le.mp hv
  have huSq : u ^ 2 ≤ (1 : ℚ) / 4 := by nlinarith
  have hvSq : v ^ 2 ≤ (1 : ℚ) / 4 := by nlinarith
  rw [abs_le]
  constructor
  · have hs := sq_nonneg (u + v / 2)
    nlinarith
  · have hs := sq_nonneg (v - u / 2)
    nlinarith
```

これは `theorem` であり、黄金整数の有理座標で現れる二次形式

$$
Q(u,v)=u^2+uv-v^2
$$

が、最近接整数丸めによって得られる square fundamental cell

$$
|u|\le\frac12,\qquad |v|\le\frac12
$$

の全域で

$$
|Q(u,v)|\le\frac{5}{16}
$$

と一様に抑えられることを示す。

## 数学的主張

0210 `goldenRatNorm` で用意された黄金ノルム二次形式は

$$
Q(u,v)=u^2+uv-v^2
$$

である。本 theorem は、0212 `exists_goldenRat_near_int` が作る丸め誤差セル

$$
(u,v)\in[-1/2,1/2]^2
$$

上での絶対値最大値が `5/16` 以下であることを証明する。

この定数は単なる粗い bound ではなく鋭い。例えば

$$
Q\left(\frac12,\frac14\right)
=\frac14+\frac18-\frac1{16}
=\frac5{16},
$$

また

$$
Q\left(-\frac14,\frac12\right)
=\frac1{16}-\frac18-\frac14
=-\frac5{16}
$$

なので、絶対値 `5/16` は実際に達成される。

したがって square cell 全体に対する最良の一様定数として

$$
\sup_{|u|,|v|\le1/2}|u^2+uv-v^2|=\frac5{16}
$$

と読むことができる。

## 証明全体での役割

`GoldenEuclidean.lean` の目的は `GoldenInt` を norm-Euclidean domain として構築することである。

その流れは次のようになっている。

1. 0209 `GoldenRat` で有理 quotient の二座標空間を用意する。
2. 0210 `goldenRatNorm` で有理座標上のノルム二次形式を定義する。
3. 0211–0212 で各 quotient 座標を最近接整数へ丸め、誤差を `[-1/2,1/2]^2` に入れる。
4. **0213 本 theorem** でそのセル上の norm を `5/16` 以下に抑える。
5. 0214 `goldenRat_norm_abs_lt_one` で `5/16 < 1` を使い strict contraction を得る。
6. 後続の `goldenRemainder_norm_rat_identity` で remainder norm を divisor norm とこの誤差 norm の積へ分解する。
7. `golden_remainder_size_lt` で

$$
|N(r)|<|N(y)|
$$

を得て Euclidean remainder 条件を閉じる。

したがって本 theorem は、最近接格子丸めを **strict Euclidean decrease** へ変換する定量的核心である。

## 直接依存する定義・補題

直接使用する Mathlib 側の主要要素は次の通りである。

- `abs_le.mp`
- `sq_nonneg`
- `nlinarith`
- 有理数 `ℚ` の線形順序体構造
- 絶対値、平方、除算

また数学的・構造的には次に依存する。

- 0210 `goldenRatNorm` と同じ二次形式
- 0212 `exists_goldenRat_near_int` が供給する仮定形 `|u|≤1/2`, `|v|≤1/2`

ただし Lean statement 自体には `goldenRatNorm` という名前は現れず、二次式を直接記述している。また 0212 を theorem 内で呼ぶのではなく、丸め後に得られる二つの bound を仮定 `hu`, `hv` として受け取る局所評価 lemma になっている。

## 証明の流れ

### 1. 絶対値 bound を両側不等式へ分解する

```lean
have hu' := abs_le.mp hu
have hv' := abs_le.mp hv
```

これにより

$$
-\frac12\le u\le\frac12,
\qquad
-\frac12\le v\le\frac12
$$

が得られる。

### 2. 各座標の平方を `1/4` 以下に抑える

```lean
have huSq : u ^ 2 ≤ (1 : ℚ) / 4 := by nlinarith
have hvSq : v ^ 2 ≤ (1 : ℚ) / 4 := by nlinarith
```

前段の両側 bound から

$$
u^2\le\frac14,\qquad v^2\le\frac14
$$

を `nlinarith` で導く。

### 3. 結論の絶対値を二本の不等式へ変換する

```lean
rw [abs_le]
constructor
```

目標

$$
|Q(u,v)|\le\frac5{16}
$$

を

$$
-\frac5{16}\le Q(u,v)
$$

と

$$
Q(u,v)\le\frac5{16}
$$

へ分解する。

### 4. 下側 bound を平方非負性から導く

```lean
have hs := sq_nonneg (u + v / 2)
nlinarith
```

平方非負性

$$
\left(u+\frac v2\right)^2\ge0
$$

を展開すると

$$
u^2+uv+\frac{v^2}{4}\ge0.
$$

これと `v² ≤ 1/4` を組み合わせることで

$$
u^2+uv-v^2\ge-\frac5{16}
$$

が得られる。

### 5. 上側 bound を別の平方非負性から導く

```lean
have hs := sq_nonneg (v - u / 2)
nlinarith
```

今度は

$$
\left(v-\frac u2\right)^2\ge0
$$

すなわち

$$
v^2-uv+\frac{u^2}{4}\ge0
$$

を使い、`u² ≤ 1/4` と合わせて

$$
u^2+uv-v^2\le\frac5{16}
$$

を得る。

この二つの completion-of-squares が `5/16` という鋭い定数を生み出している。

## Lean 固有の処理

`abs_le.mp hu` は `|u| ≤ 1/2` を conjunction

```lean
-(1/2) ≤ u ∧ u ≤ 1/2
```

へ変換する。`hu'`, `hv'` は pair のまま保持されているが、`nlinarith` はその局所仮定を利用して平方 bound を自動導出できる。

`rw [abs_le]` は結論側で逆方向の変換を行い、絶対値不等式を二本の order goal に展開する。

証明後半の `hs` は明示的には展開されていない。`sq_nonneg` が提供する

```lean
0 ≤ (u + v / 2) ^ 2
```

または

```lean
0 ≤ (v - u / 2) ^ 2
```

を `nlinarith` が多項式制約として読み、`huSq` / `hvSq` と組み合わせて最終 bound を閉じる。

したがってこの proof は `ring` で恒等式を手動変形するのではなく、**平方非負性を certificate として与え、残りを nonlinear arithmetic solver に委譲する** 設計である。

## 冗長・重複箇所

最も目立つ API-level の重複は、0210 で

```lean
def goldenRatNorm (x : GoldenRat) : ℚ :=
  x.1 ^ 2 + x.1 * x.2 - x.2 ^ 2
```

と名前を付けた直後であるにもかかわらず、本 theorem の statement が

```lean
|u ^ 2 + u * v - v ^ 2| ≤ ...
```

と二次式を再記述している点である。

これは tactic proof を単純化する利点がある一方、将来 norm polynomial の表現を変更した場合に statement 側との同期が必要になる。

また `huSq` と `hvSq` は対称な二本の proof であり、小さな helper

```lean
|x| ≤ 1/2 → x^2 ≤ 1/4
```

を作れば一つに抽象化できる。ただし現行コードでは二行だけなので、helper 化による API 増加の方が重い可能性がある。

## 最適化候補

1. **statement を `goldenRatNorm` で書く**

```lean
|goldenRatNorm (u, v)| ≤ (5 : ℚ) / 16
```

とすれば 0210 との API 接続が直接見える。

2. **completion-of-squares を named lemma 化する**
   - 下側・上側 bound の由来を数学的 theorem として明示できる。
   - 一方、現行 `sq_nonneg + nlinarith` は短く十分安定している可能性が高い。

3. **square-cell predicate を導入する**
   - `|u|≤1/2 ∧ |v|≤1/2` を一つの named predicate にまとめれば、0212→0213→0214 の interface がより幾何的になる。

4. **鋭さの theorem を別途追加する**
   - 例えば `(1/2,1/4)` で `5/16` を達成することを certificate として持てば、source コメントの “sharp uniform constant” を形式的にも裏付けられる。

5. **一般 quadratic form bound への抽象化は慎重にする**
   - $u^2+uv-v^2$ に特化した平方完成が非常に簡潔なので、一般化すると証明負担が増える可能性が高い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 単独で必要な主要機能は、

- `ℚ`
- absolute value と `abs_le`
- ordered ring / field arithmetic
- `sq_nonneg`
- `nlinarith`

である。

したがって theorem 単独なら `Mathlib` 全体よりかなり小さい import で足りる可能性が高い。ただし `GoldenEuclidean.lean` 全体では `round`、`field_simp`、`ring`、casts、`EuclideanDomain`、well-founded measure なども使うため、module 単位の最小 import は広くなる。

今回は Lean build を行わないため、具体的な最小 import module 名は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

非常に適している。数学的 bound が小さく明瞭で、proof strategy の比較もしやすい。

候補は次の通り。

- A: 現行 `sq_nonneg` + `nlinarith`
- B: 平方完成恒等式を `ring` で明示してから `linarith`
- C: 頂点・境界を場合分けして直接最大値を評価
- D: `goldenRatNorm` statement + 専用 cell predicate
- E: 変数スケール `U=2u`, `V=2v` により `[-1,1]^2` へ正規化して整数係数多項式で評価

比較軸は、proof term の短さ、数学的可読性、solver 依存度、定数 `5/16` の由来の透明性、一般化可能性、upstream definition 変更への耐性である。

特に A と B の比較は、Lean における「証明 certificate をどこまで明示し、どこから arithmetic solver に任せるか」を測る良い Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

正本 source では 0212 の直後に本 theorem があり、続いて 0214 `goldenRat_norm_abs_lt_one` が置かれている。

```lean
/--
The square fundamental cell is a strict golden-norm contraction cell.
The sharp uniform constant is `5/16`.
-/
theorem goldenRat_norm_abs_le_five_sixteen ...
```

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、本 theorem に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0214 `goldenRat_norm_abs_lt_one`** である。

```lean
theorem goldenRat_norm_abs_lt_one
    {u v : ℚ}
    (hu : |u| ≤ (1 : ℚ) / 2)
    (hv : |v| ≤ (1 : ℚ) / 2) :
    |u ^ 2 + u * v - v ^ 2| < 1 := by
  have h := goldenRat_norm_abs_le_five_sixteen hu hv
  norm_num at h ⊢
  linarith
```

0213 が鋭い bound `5/16` を与えたので、0214 は単に

$$
\frac5{16}<1
$$

を使って strict contraction に変換する。後続の `golden_remainder_size_lt` が必要とするのはこの `<1` の形であり、0213 が定量評価、0214 が Euclidean API 向けの定性的 wrapper という役割分担になる。