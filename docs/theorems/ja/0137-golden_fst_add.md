# 0137 — `golden_fst_add`

## Lean の型

```lean
@[simp] theorem golden_fst_add (x y : GoldenInt) :
    (x + y).fst = x.fst + y.fst := rfl
```

これは `theorem` であり、同時に `@[simp]` 属性を持つ加法の第一座標射影補題である。

## 数学的主張・宣言の意味

`GoldenInt` は整数対 `⟨a,b⟩` により黄金整数

$$
a+b\varphi
$$

を表す。上流の raw operation `goldenAdd` は座標ごとの加法を実装し、`Add GoldenInt` instance に登録されている。したがって

$$
(a+b\varphi)+(c+d\varphi)=(a+c)+(b+d)\varphi
$$

であり、本定理はその第一座標だけを取り出した

$$
\operatorname{fst}(x+y)=\operatorname{fst}(x)+\operatorname{fst}(y)
$$

を Lean の標準 `+` 記法について公開する。

## 証明全体での役割

0133–0136 では `0` と `1` の座標を `@[simp]` API として公開した。本定理 0137 からは、標準二項演算を座標演算へ落とす projection API に進む。

第一座標について `x + y` を整数加法へ正規化できるため、後続の `GoldenInt.ext` を用いた等式証明では、加法構造の第一成分を自動的に整数環の問題へ還元できる。直後の `golden_snd_add` と対になり、さらに `golden_fst_neg`、`golden_fst_sub`、`golden_fst_mul` などへ続く座標 simp infrastructure の基礎となる。

この infrastructure は後続の `AddCommGroup GoldenInt` と `CommRing GoldenInt` の構築で重要である。source ではこれらの instance 証明が `ext <;> simp` と整数環上の標準正規化へ落ちるよう設計されている。

## 直接依存する定義・補題

直接依存は次の要素である。

- `GoldenInt`
- raw operation `goldenAdd`
- `instance : Add GoldenInt := ⟨goldenAdd⟩`
- `GoldenInt.fst` の第一座標射影
- 整数の標準加法

依存関係は概念的に

$$
\texttt{goldenAdd}
\longrightarrow
\texttt{Add GoldenInt}
\longrightarrow
\texttt{golden\_fst\_add}
$$

となる。本定理は上流の代数補題を使わず、定義展開だけで成立する。

## 証明・構築の流れ

証明は

```lean
:= rfl
```

だけで閉じる。

Lean は `x + y` を `Add GoldenInt` instance によって `goldenAdd x y` へ展開する。`goldenAdd` の第一座標は定義上 `x.fst + y.fst` なので、左辺 `(x + y).fst` は右辺と同一項まで計算される。

したがって本証明の本質は theorem-level の推論ではなく、raw coordinate operation と標準 typeclass interface が definitional equality を保つ形で接続されていることにある。

## Lean 固有の処理

`rfl` が成立することは、`(x + y).fst = x.fst + y.fst` が別の補題から導かれる propositional equality ではなく、定義的等価性であることを示す。

さらに `@[simp]` により、今後 `simp` は

```lean
(x + y : GoldenInt).fst
```

を自動的に

```lean
x.fst + y.fst
```

へ正規化できる。

これは `GoldenInt.ext` と組み合わせた座標別証明で特に有効である。抽象的な `GoldenInt` 上の加法等式を、第一座標では整数加法の等式へ直接落とせる。

## 冗長・重複箇所

直後の `golden_snd_add` と本定理は同じ `goldenAdd` の二つの座標射影を別々に公開するため、構造的には対になった重複である。

しかしこれは意図的な API-level duplication である。各射影を独立した simp rule として持つことで、不要な structure 展開を避け、downstream proof の正規形を予測しやすくしている。

また `goldenAdd` 自体がすでに座標加法を一度だけ定義しているため、本定理は数学的な実装を再記述せず、その definitional interface を公開するだけである。

## 最適化候補

候補は次の三系統である。

1. 現行のように `fst` / `snd` projection theorem を個別 `@[simp]` として保持する。
2. `goldenAdd` 全体の展開を simp に許し、専用 projection theorem を削減する。
3. `GoldenInt` を既存の積型や quadratic algebra infrastructure に寄せ、汎用 projection simp lemma を再利用する。

現行方式は宣言数が増える一方で、simp surface が局所的かつ明示的である。特に FLT5 の長い downstream proof では、内部表現を無制限に展開するよりも、公開 projection API を固定する方が監査性と安定性に優れる可能性が高い。

## 必要 Mathlib import と import 最適化候補

standalone source は全体として `import Mathlib` を利用している。本定理単独が必要とするのは `GoldenInt`、`Add` instance、構造射影、`@[simp]`、`rfl` と整数加法であり、高度な Mathlib theorem は直接使用しない。

したがって本定理単独のために `Mathlib` 全体を import する必要はないと考えられる。実際の最小 import は `GoldenInt` と `goldenAdd` を含む上流モジュールの依存関係に支配される。今回は Lean build を行わないため、具体的な最小 import 集合は未検証であり、この点は最適化候補としての推測である。

## Comparator challenge 化の可否

適している。例えば次の方式を比較できる。

- 現行の dedicated `@[simp]` projection theorem
- `goldenAdd` の定義展開だけに依存する方式
- 一般的な product / quadratic algebra の加法 simp API を再利用する方式

比較軸は、downstream proof の行数、`simp` の安定性、定義展開量、simp trace の読みやすさ、`ext` 証明での自動化率、API の発見可能性である。

数学的難度は低いが、「raw representation をどこまで public simp API として露出するか」を評価する Lean ライブラリ設計の Comparator challenge として有用である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `GoldenOrder` generated section と、直前までの theorem-museum 文書である。対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` も存在する。

ただし本定理のような定義的 projection lemma に対応する PDF の具体的ページ・節番号は今回直接特定していないため、その対応位置は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
@[simp] theorem golden_snd_add (x y : GoldenInt) :
    (x + y).snd = x.snd + y.snd := rfl
```

である。本定理が加法の第一座標を標準整数加法へ落としたのに対し、次の 0138 は第二座標について同じ definitional interface を公開する。