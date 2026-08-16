# 0135 — `golden_fst_one`

## Lean の型

```lean
@[simp] theorem golden_fst_one : (1 : GoldenInt).fst = 1 := rfl
```

これは `theorem` であり、同時に `@[simp]` 属性を持つ座標射影補題である。

## 数学的主張・宣言の意味

`GoldenInt` は整数対 `⟨a,b⟩` により黄金整数

$$
a+b\varphi
$$

を表す。Lean source では乗法単位元を raw definition として

```lean
def goldenOne : GoldenInt := ⟨1, 0⟩
instance : One GoldenInt := ⟨goldenOne⟩
```

と定義・登録している。したがって標準記法 `(1 : GoldenInt)` の第一座標は整数 `1` であり、本定理は

$$
\operatorname{fst}(1_{\mathbb Z[\varphi]})=1
$$

を Lean の simp API として公開する。

## 証明全体での役割

0133 `golden_fst_zero` と 0134 `golden_snd_zero` で零元の二座標を標準化した後、本定理から単位元 `1` の座標正規化へ移る。

後続の `AddCommGroup GoldenInt`、`AddGroupWithOne GoldenInt`、`CommRing GoldenInt` の構築では、構造法則を座標ごとに落として `simp` や `ring` で処理する。そのとき `(1 : GoldenInt).fst` が自動的に `1` へ簡約されることは、`one_mul`、`mul_one`、cast、norm 計算などの基礎となる。

特に `GoldenInt` の乗法単位元が抽象的に導入された別の値ではなく、明示的座標 `⟨1,0⟩` と定義的に一致していることを、小さな公開補題として固定する役割を持つ。

## 直接依存する定義・補題

直接依存は次の三点である。

- `GoldenInt`
- `goldenOne : GoldenInt := ⟨1, 0⟩`
- `One GoldenInt := ⟨goldenOne⟩`

本定理は 0133 や 0134 を証明上は使用しない。それらとは同じ projection-simp API 群に属する兄弟補題である。

依存関係は概念的に

$$
\texttt{goldenOne}
\longrightarrow
\texttt{One GoldenInt}
\longrightarrow
\texttt{golden_fst_one}
$$

となる。

## 証明・構築の流れ

証明は

```lean
:= rfl
```

だけで終わる。

1. `(1 : GoldenInt)` が `One GoldenInt` instance により `goldenOne` へ展開される。
2. `goldenOne` が `⟨1,0⟩` へ展開される。
3. `.fst` が pair の第一成分 `1` へ計算される。
4. 左辺と右辺が定義的に同一となり、`rfl` が成立する。

したがって、ここでは代数的な推論ではなく definitional equality が証明そのものになっている。

## Lean 固有の処理

`@[simp]` により、この定理は simplifier の rewrite rule として登録される。以後 `simp` は

```lean
(1 : GoldenInt).fst
```

を自動的に

```lean
1
```

へ正規化できる。

重要なのは、定理が `rfl` で閉じる一方で `@[simp]` を付けて明示的 API として公開している点である。Lean は定義展開だけでもこの式を計算できる場合があるが、公開 simp lemma を置くことで、下流証明が `goldenOne` や instance の具体的展開方法へ依存しにくくなる。

つまり definitional transparency を保ちつつ、rewrite interface も安定化している。

## 冗長・重複箇所

数学的には `goldenOne = ⟨1,0⟩` から即座に分かるため、本定理は情報量の少ない補題である。また `rfl` だけで済むため、定義展開を許せば補題なしでも多くの箇所を処理できる。

しかし、0133–0136 のように `fst` / `snd` を対で `@[simp]` 化することには API 上の対称性がある。raw representation を下流から隠し、標準記法に対する安定した simp surface を提供するため、意図的な冗長性と評価できる。

## 最適化候補

候補は三つある。

1. 現行どおり projection lemma を個別に保持し、simp API の明示性を優先する。
2. `goldenOne` や `One GoldenInt` を適切に `[simp]` 展開可能にして個別補題を削減する。
3. `GoldenInt` の extensionality と座標 simp lemma 群をまとめた API 方針を定め、公開 surface を系統化する。

2 は行数を減らせる可能性があるが、内部定義の展開を simplifier に広く許すと simp normal form が実装詳細へ引きずられる危険もある。現行方式は小さな補題を増やす代わりに abstraction boundary を保ちやすい。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を利用している。本定理そのものに高度な Mathlib theorem は不要で、必要なのは `GoldenInt`、`goldenOne`、`One` interface、`@[simp]` / `rfl` を含む Lean の基本機能である。

したがって本定理単独を理由として `Mathlib` 全体を import する必要はないと考えられる。ただし実際の `GoldenOrder` モジュールでは後続の `AddCommGroup`、`CommRing`、整数演算、`ring` tactic 等も使用するため、モジュール単位の最小 import はそれらに支配される。今回は Lean build を行わないため、具体的な最小 import 集合は未検証であり、最適化候補としての推測である。

## Comparator challenge 化の可否

可能だが、小規模な challenge 向きである。

比較対象として、

- 個別の `@[simp] theorem golden_fst_one ... := rfl`
- raw definition 自体の simp 展開に任せる方式
- `GoldenInt` 用の座標 simplification API をまとめて設計する方式

を用意できる。

評価軸は、下流証明で必要な `simp` 指定量、内部定義変更への耐性、simp trace の読みやすさ、`rfl` で閉じる補題数、公開 API の対称性である。純粋な数学 challenge というより、Lean API 設計・simp normal form 設計の Comparator に向く。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `GoldenOrder` generated section である。standalone source の blob SHA は今回 `fab7f3e9cc1d1f2a5ae587ea0261aec194880558` と確認した。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在することも確認した。ただし、この小さな projection theorem に対応する具体的ページ番号は今回特定していないため、ページ・節番号は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
@[simp] theorem golden_snd_one : (1 : GoldenInt).snd = 0 := rfl
```

である。0135 で単位元の第一座標を固定したので、次は第二座標が `0`、すなわち黄金比方向の成分を持たないことを simp API として公開する。