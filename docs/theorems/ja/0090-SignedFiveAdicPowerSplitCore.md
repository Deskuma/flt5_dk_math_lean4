# 0090 — `SignedFiveAdicPowerSplitCore`

## Lean の型

```lean
abbrev SignedFiveAdicPowerSplitCore : Prop :=
  ∀ {u v w : ℕ}, SignedFiveAdicPowerSplit u v w → False
```

本宣言は theorem ではなく `abbrev` による命題の別名である。任意の `u v w : ℕ` と、それらに対応する exact power-split packet

```lean
SignedFiveAdicPowerSplit u v w
```

を受け取れば `False` を返せる、という contradiction receiver の型を一行で定義している。

## 数学的主張

数学的には、0083 で定義された exact five-adic power split が一つも存在しないことを示す「反証器」の仕様である。

すなわち

$$
\forall u,v,w,\quad
\mathrm{SignedFiveAdicPowerSplit}(u,v,w)\Longrightarrow\bot
$$

を表す。

`SignedFiveAdicPowerSplit u v w` は、five-adic packet に対して正の互いに素な自然数 $a,b$ を保持し、

$$
carrier=5^4a^5,
$$

$$
residual=5b^5,
$$

$$
distinguished=5ab,
$$

$$
0<a,\qquad 0<b,\qquad \gcd(a,b)=1
$$

という exact fifth-power split を備える。したがって本 core は、これらの条件を同時に満たす split data を後続の算術・代数で矛盾へ送るための受信口である。

重要なのは、本宣言自身はまだ矛盾を証明していないことである。後続が実装すべき「任意の exact split を `False` へ送る関数」の型だけを固定している。

## 証明全体での役割

0087–0089 までで、signed normal form から exact power split までの構成経路が完成した。

概念的には

$$
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedFiveAdicPacket}
\longrightarrow
\mathrm{SignedFiveAdicPowerSplit}
$$

である。

本号は、その構成された exact split を「消費して矛盾を出す側」の API 境界を定める。

直後の theorem

```lean
theorem signedBranchARefuter_of_powerSplitCore
    (hCore : SignedFiveAdicPowerSplitCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedFiveAdicPowerSplit_of_normalForm hNF)
```

は 0089 `signedFiveAdicPowerSplit_of_normalForm` で split を作り、それを `hCore` に渡すだけで signed Branch-A 全体の refuter を得る。

さらにその次の `branchB_false_of_powerSplitCore` は既存の `branchB_false_of_signedBranchARefuter` を経由して routed Branch-B candidate 全体を閉じる。

したがって本宣言は、five-adic power decomposition を構築する前半と、その decomposition を黄金比・二次形式側などで矛盾させる後半を分離する proof architecture 上の境界である。

## 直接依存する定義・補題

直接依存は一つだけである。

- `SignedFiveAdicPowerSplit`（0083）

本宣言の型本体は `SignedFiveAdicPacket`、`SignedBranchANormalForm`、`GN5`、`SumGN5`、`padicValNat`、mod $25$、gcd 補題などを直接参照しない。それらは 0083 の record とその構築過程へ既に封じ込められている。

間接的には 0087–0089 を通して five-adic packet の構成、gcd exactness、fifth-power factor split などに繋がるが、本 core の interface は exact split のみを要求する。

## 証明の流れ

この宣言自体には proof script はない。`abbrev` による型定義なので、要求される処理は三段だけである。

1. 任意の `{u v w : ℕ}` を暗黙引数として受け取る。
2. `SignedFiveAdicPowerSplit u v w` を受け取る。
3. `False` を返すことを要求する。

つまり、後続の contradiction argument が満たすべき関数型を先に固定している。

この形にしておくことで、後続の theorem は contradiction の内部証明を知らずに

```lean
hCore split
```

と適用できる。

## Lean 固有の処理

### `abbrev` の reducibility

`abbrev` は reducible な略記である。そのため Lean は必要に応じて

```lean
SignedFiveAdicPowerSplitCore
```

を

```lean
∀ {u v w : ℕ}, SignedFiveAdicPowerSplit u v w → False
```

へ展開できる。

後続で adapter theorem をほとんど必要とせず、`hCore split` のように通常の関数としてそのまま適用できるのが利点である。

### implicit parameters

`{u v w : ℕ}` は暗黙引数なので、`split : SignedFiveAdicPowerSplit u v w` の型から通常は Lean が index を推論する。

直後の

```lean
hCore (signedFiveAdicPowerSplit_of_normalForm hNF)
```

でも `u v w` を明示していない。

### `Prop` と proof-only API

本 core は計算用データを生成せず、返り値は常に `False` である。したがって proof-only contract として `Prop` に置かれている。

0088–0089 は `Classical.choice` のため `noncomputable` であるが、本 core 自体は choice を実行しないので `noncomputable` 宣言ではない。

## 冗長・重複箇所

局所的なコード量としては一行であり、冗長性はほぼない。

ただし構造上、0078 `SignedFiveAdicCore` と非常によく似ている。

0078 は

```lean
abbrev SignedFiveAdicCore : Prop :=
  ∀ {u v w : ℕ}, SignedFiveAdicPacket u v w → False
```

であり、本号は domain を

```lean
SignedFiveAdicPacket
```

から

```lean
SignedFiveAdicPowerSplit
```

へ一段強めただけである。

これは「重複」ではあるが、proof graph のどの層で contradiction を仮定するかを名前で分離している。five-adic packet だけで矛盾させる route と、exact fifth-power split まで進んでから矛盾させる route を別々の core contract として表現できるため、意味上の重複には設計上の価値がある。

## 最適化候補

### 候補 A — 現行の domain-specific core を維持する

最も読みやすい。`SignedFiveAdicPowerSplitCore` という名前だけで「exact split 層が残された算術核心である」と分かる。

### 候補 B — generic refuter alias を導入する

例えば

```lean
abbrev Refuter (α : Sort _) : Prop := α → False
```

のような一般化は可能である。ただし indexed family

```lean
∀ {u v w}, SignedFiveAdicPowerSplit u v w → False
```

まで含めて一般化すると抽象化が重くなり、FLT5 proof graph の可読性を落とす可能性がある。

### 候補 C — 0078 と共通化する

`SignedFiveAdicCore` と `SignedFiveAdicPowerSplitCore` は同じ receiver pattern なので、共通 constructor / adapter framework を作る余地はある。

一方で、両者は contradiction を受ける数学的情報量が異なる。packet core は five-adic data のみ、power-split core は exact fifth-power decomposition まで利用可能である。domain-specific 名を残す方が proof architecture を追いやすい可能性が高い。

### 候補 D — より薄い contradiction kernel を受け取る

後続の黄金比・二次形式側が `SignedFiveAdicPowerSplit` の一部フィールドしか使わないことが判明すれば、core が受け取る型をより薄い record に縮約できる可能性がある。

これは後続 theorem を読み終えてから判断すべき最適化候補であり、現時点では推測である。

## 必要 Mathlib import と import 最適化候補

対象ブランチの generated standalone artifact は `import Mathlib` で構築されている。

本宣言そのものは Mathlib の算術 theorem や tactic を直接使用しない。Lean の基本論理と project-local な `SignedFiveAdicPowerSplit` の型があれば定義できるため、本一行のためだけに umbrella `Mathlib` 全体を必要とするわけではない。

manifest 上ではこの領域は `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` に属する。module 単位では、その前半で gcd、coprimality、prime、自然数除算、冪、`ring`、`omega`、`norm_num` などを利用しているため、実際の最小 import は module 全体で決める必要がある。

import 最適化候補は、分割元 module の使用 theorem / tactic を列挙し、umbrella `Mathlib` をより狭い import 群へ段階的に置換することである。本タスクでは Lean build を行わないため、具体的な最小 import 集合は推測で断定しない。

## Comparator challenge 化の可否

適している。ただし数論計算より proof architecture / API design の challenge 向きである。

比較候補は次の通り。

1. 現行の domain-specific `SignedFiveAdicPowerSplitCore`。
2. 生の関数型を各 theorem の引数へ直接書く方式。
3. generic `Refuter` / indexed refuter abstraction を導入する方式。
4. 0078 `SignedFiveAdicCore` と共通 framework に統合する方式。
5. full `SignedFiveAdicPowerSplit` ではなく最小 contradiction kernel を渡す方式。

評価軸は、proof graph の可視性、後続 theorem の簡潔さ、型エラーの局所性、依存境界、抽象化コストである。

現行方式はコード重複をわずかに許しながら、数学的な層境界を宣言名として残す設計であり、Comparator では「genericity と domain readability のどちらを優先するか」が主題になる。

## PDF・ソース根拠について

形式的な最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` である。source 上で本宣言は `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` 部分に属し、0089 `signedFiveAdicPowerSplit_of_normalForm` の直後、`signedBranchARefuter_of_powerSplitCore` の直前に置かれている。

既存の日本語・英語 PDF は叙述的背景資料として扱う。今回 GitHub code search は upstream 502 となり、この一行の `abbrev` と一対一対応する PDF の具体的ページ・節番号を確認できなかった。そのため PDF 固有の定理番号、ページ番号、文章は推測で補っていない。

## 次に読むべき定理

source 上で直後に置かれる theorem は

```lean
theorem signedBranchARefuter_of_powerSplitCore
    (hCore : SignedFiveAdicPowerSplitCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedFiveAdicPowerSplit_of_normalForm hNF)
```

である。

本号が exact power-split contradiction receiver の型を固定し、次号は 0089 の normal-form-to-split adapter を使ってその core を `SignedBranchARefuter` へ持ち上げる。

すなわち次号では

$$
\mathrm{SignedFiveAdicPowerSplitCore}
\Longrightarrow
\mathrm{SignedBranchARefuter}
$$

という closure adapter を読む。ここで exact split 層の矛盾が signed Branch-A 全体へ伝播する。