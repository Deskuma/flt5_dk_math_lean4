# 0140 — `golden_snd_neg`

## Lean の型

```lean
@[simp] theorem golden_snd_neg (x : GoldenInt) :
    (-x).snd = -x.snd := rfl
```

これは `theorem` であり、`@[simp]` 属性を持つ否定演算の第二座標射影補題である。

## 数学的主張・宣言の意味

`GoldenInt` は整数対 `⟨a,b⟩` により黄金整数

$$
a+b\varphi
$$

を表す。上流の raw operation `goldenNeg` は

```lean
def goldenNeg (x : GoldenInt) : GoldenInt :=
  ⟨-x.fst, -x.snd⟩
```

と座標ごとの否定として定義され、

```lean
instance : Neg GoldenInt := ⟨goldenNeg⟩
```

によって標準の unary negation `-x` に接続されている。

したがって

$$
-(a+b\varphi)=(-a)+(-b)\varphi
$$

であり、本定理は第二座標について

$$
\operatorname{snd}(-x)=-\operatorname{snd}(x)
$$

を public simp API として公開する。

## 証明全体での役割

0139 `golden_fst_neg` が否定の第一座標を整数否定へ落としたのに対し、本定理は第二座標を担当する。両者が揃うことで、`GoldenInt.ext` で黄金整数の等式を二つの整数座標へ分解した後、`-x` を両座標とも通常の整数否定へ自動正規化できる。

これは直後の subtraction projection 群と合わせて、後続の

```lean
instance goldenAddCommGroup : AddCommGroup GoldenInt := by
  ...
  intros <;> ext <;> simp [add_comm, add_left_comm]
```

という構築を成立させる基礎 API の一部である。特に `neg_add_cancel` のような加法群法則を、黄金整数専用の手作業計算ではなく整数座標上の標準 simp に還元できる。

FLT5 の第五冪分解そのものを述べる定理ではないが、黄金整数環を明示座標から Mathlib の標準環構造へ持ち上げるための infrastructure theorem であり、後段の整除・ノルム・Euclidean-domain 構造へ進むための土台である。

## 直接依存する定義・補題

直接依存するのは次である。

- `GoldenInt`
- `goldenNeg`
- `instance : Neg GoldenInt := ⟨goldenNeg⟩`
- `GoldenInt.snd`
- 整数の標準否定

概念的な依存関係は

$$
\texttt{goldenNeg}\longrightarrow\texttt{Neg GoldenInt}\longrightarrow\texttt{golden\_snd\_neg}
$$

である。0139 `golden_fst_neg` は依存順上の直前宣言であり API として対をなすが、本定理の証明そのものが 0139 を呼び出すわけではない。

## 証明・構築の流れ

証明は `rfl` 一語で閉じる。

1. `-x` は `Neg GoldenInt` instance によって `goldenNeg x` へ定義展開される。
2. `goldenNeg x` の第二座標は定義上 `-x.snd` である。
3. よって `(-x).snd` と右辺 `-x.snd` は reduction 後に同一項となり、反射律で証明できる。

ここでは algebra theorem、rewrite、case split は一切不要であり、raw operation と標準記法の definitional equality そのものが証明になっている。

## Lean 固有の処理

`rfl` で閉じることは、命題的な補題を使って等しいと示しているのではなく、elaboration と reduction の後に両辺が同じ Lean term になることを意味する。

`@[simp]` 属性により simplifier は

```lean
(-x : GoldenInt).snd
```

を

```lean
-x.snd
```

へ自動的に書き換える。

この設計では `goldenNeg` の内部構造を広範囲に unfold する代わりに、利用者が必要とする座標射影だけを安定した normal form に変換する。`GoldenInt.ext` と `simp` を組み合わせる proof style に対して、内部表現を露出しすぎず十分な計算能力を与えている。

## 冗長・重複箇所

0139 `golden_fst_neg` とは `fst` と `snd` の違いしかなく、ほぼ完全に対称な宣言である。これは API-level の意図的な重複である。

また `goldenNeg` を直接 unfold すれば本定理と同じ計算結果を得られるため、raw definition と projection theorem の間にも意味上の重なりがある。ただし dedicated `@[simp]` theorem を置くことで、simplifier に内部定義全体を展開させず、必要な射影だけを正規化できるという利点がある。

## 最適化候補

候補は三系統ある。

1. 現行どおり `fst` / `snd` の dedicated `@[simp]` theorem を保持する。
2. `goldenNeg` 自体を simp 展開対象にし、個別 projection theorem を削減する。
3. `GoldenInt` を積型または一般 quadratic algebra の既存構造へ寄せ、汎用的な negation projection lemma を再利用する。

宣言数だけを減らすなら 2 や 3 が有利になり得る。しかし現行方式は simp の展開範囲を局所化し、proof trace と downstream normal form を予測しやすくする。監査可能性を重視する FLT5 formalization では、この明示的 API は十分合理的である。

## 必要 Mathlib import と import 最適化候補

standalone source は全体として `import Mathlib` を使用している。本定理単独では `GoldenInt`、`Neg` instance、structure projection、`@[simp]`、`rfl`、整数の否定しか直接使用せず、高度な Mathlib theorem は要求しない。

したがって本定理だけのために `Mathlib` 全体を import する必要はないと考えられる。実際の modular source の最小 import は `GoldenOrder` の上流定義、整数型、typeclass infrastructure、後続の環構造構築が要求する import に支配される。

今回は Lean build を行わないため、具体的な最小 import 集合は未検証である。この部分は確認済み事実ではなく import 最適化候補としての推測である。

## Comparator challenge 化の可否

適している。たとえば次の三方式を比較できる。

- 現行の dedicated `@[simp]` projection theorem 群
- `goldenNeg` の直接 unfold のみに依存する方式
- product / quadratic-algebra の汎用 simp API を再利用する方式

比較軸は、downstream proof の行数、`simp` の安定性、展開される term の大きさ、simp trace の可読性、`ext` 証明の自動化率、API の発見可能性、内部表現変更への耐性である。

数学的には自明な補題だが、Lean library design における「定義的計算をどこまで public simp API として固定するか」を比較する小さく明瞭な Comparator challenge になる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `GoldenOrder.lean` generated section である。source では

```lean
@[simp] theorem golden_fst_neg (x : GoldenInt) : (-x).fst = -x.fst := rfl
@[simp] theorem golden_snd_neg (x : GoldenInt) : (-x).snd = -x.snd := rfl
@[simp] theorem golden_fst_sub (x y : GoldenInt) :
    (x - y).fst = x.fst - y.fst := rfl
```

という順に並んでいる。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、本定理のような小さな definitional projection lemma に対応する具体的ページ・節番号は今回特定していないため、ページ対応は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
@[simp] theorem golden_fst_sub (x y : GoldenInt) :
    (x - y).fst = x.fst - y.fst := rfl
```

である。0140 までで negation の両座標 projection API が完成した。次の 0141 から subtraction に進み、`goldenSub x y = goldenAdd x (goldenNeg y)` として構築された減算を標準記法 `x - y` の各座標へ定義的に落とす。