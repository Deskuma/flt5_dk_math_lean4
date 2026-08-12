# 0114 — `signedSquareGoldenExceptionalPacket_of_normalForm`

## Lean の型

```lean
noncomputable def signedSquareGoldenExceptionalPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedSquareGoldenExceptionalPacket u v w :=
  signedSquareGoldenExceptionalPacket_of_powerSplit
    (signedFiveAdicPowerSplit_of_normalForm hNF)
```

本宣言は theorem ではなく `noncomputable def` である。`SignedBranchANormalForm` を入口として、既存の変換

```lean
signedFiveAdicPowerSplit_of_normalForm
```

で exact five-adic power split を得て、それを 0113

```lean
signedSquareGoldenExceptionalPacket_of_powerSplit
```

へ渡すことで、signed square-golden exceptional packet を直接返す。

## 数学的主張

入力は signed Branch-A normal form

```lean
hNF : SignedBranchANormalForm u v w
```

である。既に上流で確立された変換を合成すると、そこから整数座標 $M,N,\delta$、five-adic power witnesses $a,b$、difference / sum の provenance を含む packet を選び出せる。

したがって下流では `hNF` から直接、packet に保存された

$$
\operatorname{GoldenNorm}(M,N)=5b^5,
$$

$$
M-2N=5^8a^{10},
$$

$$
M^2-4N^2=\delta^2,
$$

$$
(2M+N)^2-5N^2=20b^5
$$

という共通 invariant 群へアクセスできる。

この宣言自身がこれらの等式を再証明するわけではない。数学的内容は上流の `signedFiveAdicPowerSplit_of_normalForm` と `signedSquareGoldenExceptionalPacket_of_powerSplit` に封じ込められている。

## 証明全体での役割

本宣言は signed normal form 層と square-golden exceptional 層の間の **composition adapter** である。

変換パイプラインは

```text
SignedBranchANormalForm
  → SignedFiveAdicPowerSplit
  → SignedSquareGoldenExceptionalPacket
```

となる。

0113 は power split を直接入力とする API だった。本宣言は一段上流の `SignedBranchANormalForm` から呼べる convenience constructor を与える。これにより後続の contradiction core は five-adic 中間 packet を意識せず、signed normal form から square-golden packet へ直接移れる。

実際、後続の `signedBranchARefuter_of_squareGoldenExceptionalCore` は

```lean
exact hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)
```

と書ける。この一行が、本宣言の architecture 上の目的を最も明瞭に示している。

## 直接依存する定義・補題

### `SignedBranchANormalForm`

入力型。signed Branch-A の orientation と normal-form data を保持する。

### `signedFiveAdicPowerSplit_of_normalForm`

```lean
noncomputable def signedFiveAdicPowerSplit_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedFiveAdicPowerSplit u v w :=
  signedFiveAdicPowerSplit_of_packet (signedFiveAdicPacket_of_normalForm hNF)
```

normal form から exact five-adic power split を選ぶ上流 adapter である。

### `signedSquareGoldenExceptionalPacket_of_powerSplit`

0113。power split から square-golden exceptional packet を選ぶ公開 constructor である。

### `SignedSquareGoldenExceptionalPacket`

出力型。five-adic split、signed provenance、golden norm、tenth boundary、square discriminant、five-discriminant relation を一つに束ねる。

## 証明・定義の流れ

本体は関数合成そのものである。

1. `hNF : SignedBranchANormalForm u v w` を受け取る。
2. `signedFiveAdicPowerSplit_of_normalForm hNF` により `SignedFiveAdicPowerSplit u v w` を得る。
3. その値を `signedSquareGoldenExceptionalPacket_of_powerSplit` に渡す。
4. `SignedSquareGoldenExceptionalPacket u v w` を返す。

新しい case split、算術正規化、cast、witness 構築は存在しない。

## Lean 固有の処理

### `noncomputable def`

0113 と同様に、下流で返される packet は上流で `Classical.choice` を用いて選択されている。そのため、この合成 adapter も `noncomputable` である。

ただし本宣言の本体には `Classical.choice` は直接現れない。noncomputability は依存する constructor から伝播している。

### implicit parameters

`{u v w : ℕ}` は implicit であり、`hNF` の型から Lean が推論する。中間値にも型注釈を付ける必要はない。

### tactic-free definition

`:=` 以下が単純な式なので `by` proof block はない。Lean の elaborator が二つの関数の codomain / domain を照合するだけで定義が成立する。

## 冗長・重複箇所

本宣言は意図的な API-level redundancy を持つ。

理論上は利用側が毎回

```lean
signedSquareGoldenExceptionalPacket_of_powerSplit
  (signedFiveAdicPowerSplit_of_normalForm hNF)
```

と書けばよく、この名前付き wrapper は不要である。

しかし後続 theorem から five-adic 中間層を隠し、proof architecture の境界を明示するため、この重複は有益である。特に `signedBranchARefuter_of_squareGoldenExceptionalCore` の proof を一行に保てる利点が大きい。

## 最適化候補

### 1. 関数合成として一般化する

同型の adapter が多数現れるなら、generic な composition helper を導入できる。ただし現状の一行定義に対して抽象化しすぎると、かえって proof graph の可読性を損なう可能性がある。

### 2. computable constructor への移行

上流の packet 構築を `Classical.choice` なしで直接定義できる設計へ変更できれば、本宣言の `noncomputable` も除去できる可能性がある。ただしこれは本宣言単体の最適化ではなく、0112–0113 の witness construction 全体の redesign になる。

### 3. adapter 命名規則の統一

`..._of_normalForm`、`..._of_powerSplit` の naming pattern は明瞭であり維持価値が高い。今後も source type を suffix に明示する方が依存グラフを追いやすい。

## 必要 Mathlib import と import 最適化候補

対象 standalone source は現在 `import Mathlib` を使用している。

本宣言そのものは tactic、ring theory、number theory lemma を直接使用せず、必要なのは既存の project declarations と Lean の通常の関数適用だけである。`noncomputable` の原因も本体の直接的な Mathlib API 利用ではなく、上流 constructor にある。

したがって modular source の import 最適化では、`Mathlib` 全体を本宣言のためだけに必要とする理由はない。実際の最小 import は `SignedBranchANormalForm`、`signedFiveAdicPowerSplit_of_normalForm`、`SignedSquareGoldenExceptionalPacket`、`signedSquareGoldenExceptionalPacket_of_powerSplit` を提供する project module の依存関係で決まる。

推測では、将来 module を分割する場合、この adapter 専用ファイルは対応する project modules の import のみで足りる可能性が高い。ただし今回は Lean build を行っていないため、最小 import 集合は未検証である。

## Comparator challenge 化の可否

**可能。特に API design challenge として適している。**

比較対象としては次が考えられる。

- 名前付き `..._of_normalForm` wrapper を置く現行設計
- 利用側で二関数を直接合成する設計
- generic composition helper を導入する設計
- `Classical.choice` を避けた computable constructor に再設計する案

評価軸は proof length よりも、依存境界の可視性、discoverability、エラー局所性、refactor 耐性、下流 theorem の読みやすさになる。

## 既存 PDF との対応

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。

今回の宣言内容についてはリポジトリ内の Lean source を形式的根拠とした。GitHub connector から PDF 本文の対応ページを直接照合できていないため、具体的なページ番号や節番号は推測で補っていない。

## 次に読むべき定理

直後の未解説宣言は

```lean
abbrev SignedSquareGoldenExceptionalCore : Prop :=
  ∀ {u v w : ℕ}, SignedSquareGoldenExceptionalPacket u v w → False
```

である。

ここで square-golden exceptional packet は「構築される対象」から「受け取れば矛盾を返す対象」へ役割を反転する。0114 が normal form から packet を直接供給できるようにしたため、その次に universal contradiction receiver を読むのが依存順として自然である。
