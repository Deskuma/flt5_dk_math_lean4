# 0138 — `golden_snd_add`

## Lean の型

```lean
@[simp] theorem golden_snd_add (x y : GoldenInt) :
    (x + y).snd = x.snd + y.snd := rfl
```

これは `theorem` であり、`@[simp]` 属性を持つ加法の第二座標射影補題である。

## 数学的主張・宣言の意味

`GoldenInt` は整数対 `⟨a,b⟩` により黄金整数 $a+b\varphi$ を表す。上流の `goldenAdd` は

```lean
def goldenAdd (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst + y.fst, x.snd + y.snd⟩
```

と座標ごとの加法として定義され、`Add GoldenInt` instance に登録されている。したがって

$$
(a+b\varphi)+(c+d\varphi)=(a+c)+(b+d)\varphi
$$

であり、本定理は第二座標について

$$
\operatorname{snd}(x+y)=\operatorname{snd}(x)+\operatorname{snd}(y)
$$

を標準 `+` 記法の API として公開する。

## 証明全体での役割

0137 `golden_fst_add` と対になり、`GoldenInt` 上の加法を二つの整数座標へ完全に分解する `@[simp]` interface を完成させる。

この二本が揃うことで、後続の `GoldenInt.ext` を使う等式証明では、`x + y` を含むゴールを第一・第二座標とも整数加法へ自動的に還元できる。実際、直後に構築される `goldenAddCommGroup` では `ext <;> simp` を核として加法群法則を整数上の標準事実へ落としている。

本定理は FLT5 の数論的核心そのものではないが、黄金整数環の代数構造を小さな座標証明へ分解するための基盤 API である。

## 直接依存する定義・補題

直接依存するのは次である。

- `GoldenInt`
- `goldenAdd`
- `instance : Add GoldenInt := ⟨goldenAdd⟩`
- `GoldenInt.snd`
- 整数の標準加法

概念的な依存関係は

$$
\texttt{goldenAdd}\longrightarrow\texttt{Add GoldenInt}\longrightarrow\texttt{golden\_snd\_add}
$$

である。0137 `golden_fst_add` とは論理的依存ではなく、同じ raw definition のもう一方の射影を公開する対称な sibling theorem である。

## 証明・構築の流れ

証明は `rfl` 一語で閉じる。

1. `x + y` が `Add GoldenInt` instance により `goldenAdd x y` へ定義展開される。
2. `goldenAdd` の第二座標は定義上 `x.snd + y.snd` である。
3. よって `(x + y).snd` と右辺は同一の項まで計算され、反射律で証明できる。

ここでは theorem-level の代数推論は行われず、raw operation と標準 typeclass notation の definitional equality がそのまま証明になっている。

## Lean 固有の処理

`rfl` が成立することは、この等式が別の補題による書き換えではなく定義的等価性であることを示す。

さらに `@[simp]` により、simplifier は

```lean
(x + y : GoldenInt).snd
```

を自動的に

```lean
x.snd + y.snd
```

へ正規化する。

0137 と合わせれば `GoldenInt.ext` の二つの座標ゴールがとも整数演算へ落ちるため、後続の algebra instance 証明で `ext <;> simp` という短い証明スタイルが可能になる。

## 冗長・重複箇所

0137 `golden_fst_add` と本定理はほぼ同型であり、第一・第二座標の違いだけを持つ。これは意図的な API-level duplication である。

一つの generic projection theorem へ抽象化する余地はあるが、`fst` と `snd` を個別 `@[simp]` rule として持つ方が simp の方向と normal form が明示的で、利用側も theorem 名を直接発見しやすい。

## 最適化候補

候補は三系統ある。

1. 現行どおり `fst` / `snd` の dedicated `@[simp]` theorem を保持する。
2. `goldenAdd` 自体を simp 展開させ、個別 projection theorem を減らす。
3. `GoldenInt` を積型や一般 quadratic algebra の既存構造へ寄せ、汎用 projection lemma を再利用する。

現行方式は宣言数が増える代わりに内部表現の展開を局所化できる。長い FLT5 downstream proof では、この明示的 simp surface の方が監査性と proof stability に有利である可能性が高い。

## 必要 Mathlib import と import 最適化候補

standalone source は `import Mathlib` を使用している。本定理単独では `GoldenInt`、`Add` instance、structure projection、`@[simp]`、`rfl`、整数加法だけが直接必要で、高度な Mathlib theorem は使用しない。

したがって本定理のためだけに `Mathlib` 全体を import する必要はないと考えられる。ただし実際の最小 import は `GoldenOrder` 上流定義の依存関係に支配される。今回は Lean build を行わないため、具体的な最小 import 集合は未検証であり、この点は最適化候補としての推測である。

## Comparator challenge 化の可否

適している。たとえば次を比較できる。

- 現行の dedicated `@[simp]` projection theorem
- `goldenAdd` の unfold のみに依存する方式
- 積型または quadratic algebra の汎用 simp API を再利用する方式

比較軸は downstream proof の行数、`simp` の安定性、展開量、simp trace の可読性、`ext` 証明の自動化率、API の発見可能性である。数学的には単純だが、representation と public simp API の境界設計を測る Comparator challenge として有用である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `GoldenOrder.lean` generated section である。そこでは `golden_fst_add` の直後に本定理が置かれ、その後 `golden_fst_neg`、`golden_snd_neg` へ続く。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本定理のような小さな definitional projection lemma に対応する具体的ページ・節番号は今回特定していないため、ページ対応は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
@[simp] theorem golden_fst_neg (x : GoldenInt) :
    (-x).fst = -x.fst := rfl
```

である。加法の両座標 projection API が揃ったので、次の 0139 からは否定演算の座標正規化へ進む。