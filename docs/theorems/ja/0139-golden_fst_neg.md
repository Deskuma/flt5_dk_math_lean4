# 0139 — `golden_fst_neg`

## Lean の型

```lean
@[simp] theorem golden_fst_neg (x : GoldenInt) :
    (-x).fst = -x.fst := rfl
```

これは `theorem` であり、`@[simp]` 属性を持つ否定演算の第一座標射影補題である。

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

と座標ごとの否定として定義され、`Neg GoldenInt` instance に登録されている。

したがって

$$
-(a+b\varphi)=(-a)+(-b)\varphi
$$

であり、本定理は第一座標について

$$
\operatorname{fst}(-x)=-\operatorname{fst}(x)
$$

を標準の unary negation 記法 `-x` に対する public simp API として公開する。

## 証明全体での役割

0137 `golden_fst_add` と 0138 `golden_snd_add` によって加法の両座標 projection API が揃った後、本定理から否定演算の座標正規化へ進む。

0139 `golden_fst_neg` と次の 0140 `golden_snd_neg` が揃うと、`GoldenInt.ext` で分解された等式中の `-x` を両座標とも整数上の通常の否定へ自動的に落とせる。これは後続の `goldenAddCommGroup` 構築で、`neg_add_cancel` を含む加法群法則を `ext <;> simp` により整数演算へ還元する基盤となる。

FLT5 の数論的核心そのものではないが、黄金整数環の explicit coordinate implementation を Lean の標準加法群 API へ接続するための重要な infrastructure theorem である。

## 直接依存する定義・補題

直接依存するのは次である。

- `GoldenInt`
- `goldenNeg`
- `instance : Neg GoldenInt := ⟨goldenNeg⟩`
- `GoldenInt.fst`
- 整数の標準否定

概念的な依存関係は

$$
\texttt{goldenNeg}\longrightarrow\texttt{Neg GoldenInt}\longrightarrow\texttt{golden\_fst\_neg}
$$

である。0138 `golden_snd_add` は依存順上の直前宣言だが、本定理の論理的直接依存ではない。

## 証明・構築の流れ

証明は `rfl` 一語で閉じる。

1. `-x` が `Neg GoldenInt` instance により `goldenNeg x` へ定義展開される。
2. `goldenNeg x` の第一座標は定義上 `-x.fst` である。
3. よって `(-x).fst` と右辺 `-x.fst` は同一の項まで計算され、反射律で証明できる。

ここでは theorem-level の代数推論や rewrite は不要であり、raw operation と標準 typeclass notation の definitional equality 自体が証明になっている。

## Lean 固有の処理

`rfl` が成立することは、この等式が proposition-level の補題を経由せず、reduction 後に構文的に一致する定義的等価性であることを示す。

`@[simp]` 属性により simplifier は

```lean
(-x : GoldenInt).fst
```

を自動的に

```lean
-x.fst
```

へ正規化する。

この方向づけにより、抽象的な `GoldenInt` 上の否定を内部表現そのものまで展開せず、公開座標 API の範囲で整数算術へ落とせる。後続の `ext <;> simp` 型証明にとって、これは proof surface を小さく保つ重要な設計である。

## 冗長・重複箇所

次の 0140 `golden_snd_neg` とは、第一座標と第二座標の違いだけを持つほぼ対称な定理であり、API-level の意図的な重複がある。

また `goldenNeg` を直接 unfold すれば本定理を使わず同じ計算を行えるため、意味上は raw definition と projection theorem に重なりがある。しかし dedicated `@[simp]` theorem を置くことで、内部実装の unfold を simplifier に広く許可せず、必要な projection だけを安定した normal form へ変換できる。

## 最適化候補

候補は三系統ある。

1. 現行どおり `fst` / `snd` の dedicated `@[simp]` theorem を保持する。
2. `goldenNeg` 自体を simp 展開対象にし、projection theorem を削減する。
3. `GoldenInt` を積型または一般 quadratic algebra の既存構造へ寄せ、汎用的な negation projection lemma を再利用する。

現行方式は宣言数が増える一方、内部表現の展開範囲を局所化できる。長い downstream proof では simp の予測可能性と監査性に有利である可能性が高い。

## 必要 Mathlib import と import 最適化候補

standalone source は `import Mathlib` を使用している。本定理単独では `GoldenInt`、`Neg` instance、structure projection、`@[simp]`、`rfl`、整数の否定が直接必要であり、高度な Mathlib theorem は使用しない。

したがって本定理だけのために `Mathlib` 全体を import する必要はないと考えられる。ただし実際の最小 import は `GoldenOrder` 上流定義と後続 instance 構築の依存関係に支配される。今回は Lean build を行わないため、具体的な最小 import 集合は未検証であり、この点は最適化候補としての推測である。

## Comparator challenge 化の可否

適している。たとえば次を比較できる。

- 現行の dedicated `@[simp]` projection theorem
- `goldenNeg` の unfold のみに依存する方式
- 積型または quadratic algebra の汎用 simp API を再利用する方式

比較軸は downstream proof の行数、`simp` の安定性、展開量、simp trace の可読性、`ext` 証明の自動化率、API の発見可能性である。

この定理は数学的には非常に単純だが、Lean library design における「内部定義をどこまで展開し、どこから public simp theorem に切り替えるか」を測る小さく明確な Comparator challenge になる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `GoldenOrder.lean` generated section である。そこでは `golden_snd_add` の直後に本定理が置かれ、その次に `golden_snd_neg`、さらに subtraction projection 群へ続く。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本定理のような小さな definitional projection lemma に対応する具体的ページ・節番号は今回特定していないため、ページ対応は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
@[simp] theorem golden_snd_neg (x : GoldenInt) :
    (-x).snd = -x.snd := rfl
```

である。0139 で否定の第一座標 projection API が公開されたので、次の 0140 で第二座標も揃え、`GoldenInt` 上の negation を両座標とも整数否定へ正規化できるようにする。