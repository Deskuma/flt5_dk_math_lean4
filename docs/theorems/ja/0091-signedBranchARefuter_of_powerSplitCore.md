# 0091 — `signedBranchARefuter_of_powerSplitCore`

## Lean の型

```lean
theorem signedBranchARefuter_of_powerSplitCore
    (hCore : SignedFiveAdicPowerSplitCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedFiveAdicPowerSplit_of_normalForm hNF)
```

本定理は、0090 `SignedFiveAdicPowerSplitCore` で表した「任意の exact power split を矛盾へ送る反証器」を、0057 `SignedBranchARefuter` が要求する signed Branch-A normal form 全体の反証器へ持ち上げる adapter theorem である。

## 数学的主張

0090 の core contract は

$$
\forall u,v,w,\quad
\mathrm{SignedFiveAdicPowerSplit}(u,v,w)\Longrightarrow\bot
$$

である。一方 `SignedBranchARefuter` は概念的に

$$
\forall u,v,w,\quad
\mathrm{SignedBranchANormalForm}(u,v,w)\Longrightarrow\bot
$$

という反証器である。

0089 `signedFiveAdicPowerSplit_of_normalForm` により

$$
\mathrm{SignedBranchANormalForm}(u,v,w)
\longrightarrow
\mathrm{SignedFiveAdicPowerSplit}(u,v,w)
$$

が既に構成されているので、両者を合成すれば

$$
\mathrm{SignedFiveAdicPowerSplitCore}
\longrightarrow
\mathrm{SignedBranchARefuter}
$$

を得る。本定理が行っている数学は、この関数合成そのものである。

## 証明全体での役割

five-adic power-split 層で証明された contradiction core を、より上流の signed Branch-A routing 層へ戻す closure adapter である。

証明全体の流れを層で書けば、

$$
\mathrm{SignedBranchANormalForm}
\xrightarrow{\;0089\;}
\mathrm{SignedFiveAdicPowerSplit}
\xrightarrow{\;hCore\;}
\bot
$$

となる。

重要なのは、後続の Branch-B closure が power split の内部構造を知る必要がなくなる点である。`hCore` がどのように `SignedFiveAdicPowerSplit` を矛盾させるかは完全に抽象化され、本定理は normal form を split に変換して適用するだけでよい。

直後の `branchB_false_of_powerSplitCore` は本定理を `branchB_false_of_signedBranchARefuter` へ渡し、routed Branch-B candidate を閉じる。そのため本定理は exact power-split contradiction と Branch-B closure の間の中間橋である。

## 直接依存する定義・補題

直接依存は次の三つである。

1. `SignedFiveAdicPowerSplitCore`（0090）
2. `SignedBranchARefuter`（0057）
3. `signedFiveAdicPowerSplit_of_normalForm`（0089）

この theorem 自身は `SignedFiveAdicPowerSplit` のフィールド、gcd、mod $25$、`padicValNat`、第五冪分解などを直接参照しない。それらは 0089 までの構築層と `hCore` の実装側へ封じ込められている。

## 証明の流れ

証明は二段で終わる。

1. `intro u v w hNF` により `SignedBranchARefuter` の暗黙の三つの自然数 index と normal-form witness を受け取る。
2. `signedFiveAdicPowerSplit_of_normalForm hNF` で exact power split を選び、その値を `hCore` に渡して `False` を得る。

コード上の核心は一行である。

```lean
exact hCore (signedFiveAdicPowerSplit_of_normalForm hNF)
```

つまり proof term としては、normal-form-to-split map と split refuter の単純な合成である。

## Lean 固有の処理

### 1. `SignedBranchARefuter` の展開を Lean に任せる

`SignedBranchARefuter` は反証器の関数型を表す project-local API であり、`intro u v w hNF` がその引数構造に従って展開される。本 theorem は型名を保ったまま証明しているため、上流 API の意味が宣言名として残る。

### 2. implicit index の推論

`hNF` の型から `u v w` が決まるため、

```lean
signedFiveAdicPowerSplit_of_normalForm hNF
```

でも、

```lean
hCore (...)
```

でも三つの index を明示する必要がない。indexed family 同士の接続を elaborator が処理している。

### 3. `noncomputable` 値を theorem 内で使う

0089 `signedFiveAdicPowerSplit_of_normalForm` は 0088 の `Classical.choice` に由来して `noncomputable def` である。しかし本宣言は theorem であり、proof-only な `False` の導出にその選択値を利用するだけなので、本 theorem 自身に `noncomputable` 修飾は不要である。

### 4. tactic は `intro` と `exact` のみ

数式正規化、算術 tactic、rewrite は一切ない。依存 API の型が十分に整っているため、Lean の型検査がほぼそのまま proof composition を表現している。

## 冗長・重複箇所

コードとしての冗長性はほぼない。ただし architecture 上は「adapter を名前付き theorem として置くか、call site で直接合成するか」という重複がある。

直後の theorem は理論上、

```lean
branchB_false_of_signedBranchARefuter
  (fun u v w hNF => hCore (signedFiveAdicPowerSplit_of_normalForm hNF))
  ...
```

のように本 theorem を介さず書ける可能性がある。

しかし `signedBranchARefuter_of_powerSplitCore` を独立宣言することで、

$$
\text{power-split core} \Rightarrow \text{signed Branch-A refuter}
$$

という proof graph の辺が名前として残る。定理博物館の観点でも、この一行は「どの抽象層からどの抽象層へ戻るか」を明示するため、単なる冗長コードとは言いにくい。

## 最適化候補

### 候補 A — 現行の名前付き adapter を維持する

最も可読性が高い。後続 theorem は power-split construction の詳細を完全に忘れ、`SignedBranchARefuter` を受け取る既存 API を再利用できる。

### 候補 B — point-free / term-style 化

関数合成に近い定理なので、型 alias の展開状況によってはより短い term-style で書ける可能性がある。ただし implicit indexed arguments があるため、現行の `intro` / `exact` の方が型エラーの位置は明瞭である。

### 候補 C — generic lifting combinator

一般に

$$
A\to B,\qquad (B\to\bot)
\Longrightarrow
(A\to\bot)
$$

という contravariant な refuter lifting である。generic helper を作ることは可能だが、本 theorem は indexed project-local types を結ぶ意味のある proof edge なので、抽象化しすぎると FLT5 の proof graph が見えにくくなる可能性がある。

### 候補 D — constructive split provider への変更

0088–0089 の `Classical.choice` を constructive な直接 constructor に置き換えられるなら、この theorem の論理形は変わらない。ただし proof-only theorem なので、ここでの実益は小さい。これは 0087–0089 側の設計問題であり、本 theorem 固有の最適化ではない。

## 必要 Mathlib import と import 最適化候補

対象ブランチの generated standalone artifact は `import Mathlib` を用いている。

本 theorem 自身が直接使う tactic は `intro` と `exact` だけで、Mathlib の算術 theorem、`ring`、`omega`、`norm_num`、`ZMod` などを直接必要としない。必要なのは project-local な

- `SignedBranchARefuter`
- `SignedFiveAdicPowerSplitCore`
- `signedFiveAdicPowerSplit_of_normalForm`

が利用可能であることである。

standalone manifest では本 theorem は `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` の終端部に属する。同 module 前半は gcd、coprimality、自然数除算、prime、冪、`ring`、`omega`、`norm_num` 等を用いるため、module 全体の最小 import はそれらを含めて決める必要がある。

import 最適化を行うなら、まず `SignedFiveAdicPowerSplit.lean` が直接 import する project module を維持しつつ、umbrella `Mathlib` の使用箇所を theorem / tactic 単位で洗い出すのが安全である。本タスクでは Lean build を行わないため、最小 import 集合は推測で断定しない。

## Comparator challenge 化の可否

適している。ただし数学的難問ではなく API / proof-composition challenge 向きである。

比較候補は次の通り。

1. 現行の `intro` + `exact`。
2. 明示的な `fun` による term proof。
3. generic refuter-lifting combinator を使う方式。
4. 本 theorem を削除し、`branchB_false_of_powerSplitCore` 内で inline composition する方式。
5. constructive split provider に差し替えた場合の同一 interface 維持。

評価軸は、コード長だけではなく、proof graph の可視性、型エラーの局所性、domain terminology の保持、再利用性、依存方向の明確さである。

現行実装は最短級でありながら、`SignedFiveAdicPowerSplitCore → SignedBranchARefuter` という重要な層移動を宣言名として保存している。そのため Comparator では「一行 adapter を残す設計上の価値」が主題になる。

## PDF・ソース根拠について

形式的な最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` である。source 上で本 theorem は `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` の終端部にあり、0090 `SignedFiveAdicPowerSplitCore` の直後、`branchB_false_of_powerSplitCore` の直前に置かれている。

既存の日本語・英語 PDF は叙述的背景資料として扱う。本回は GitHub code search が upstream 502 を返し、この一行 adapter と一対一対応する PDF の具体的ページ・節番号を確定できなかった。そのため PDF 固有の定理番号・ページ番号・記述を推測で補っていない。

## 次に読むべき定理

source 上で直後に置かれる theorem は

```lean
theorem branchB_false_of_powerSplitCore
    (hCore : SignedFiveAdicPowerSplitCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_powerSplitCore hCore) hPack hBranch
```

である。

本号で power-split core を `SignedBranchARefuter` へ持ち上げたので、次号は既存の `branchB_false_of_signedBranchARefuter` にその refuter を渡し、

$$
\mathrm{SignedFiveAdicPowerSplitCore}
\Longrightarrow
\text{every routed Branch-B pack is contradictory}
$$

という closure を完成させる。これは `SignedFiveAdicPowerSplit.lean` の最後の theorem であり、その直後から `SquareGoldenBridge.lean` が始まる。