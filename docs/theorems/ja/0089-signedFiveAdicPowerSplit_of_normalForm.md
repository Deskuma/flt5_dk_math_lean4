# 0089 — `signedFiveAdicPowerSplit_of_normalForm`

## Lean の型

```lean
noncomputable def signedFiveAdicPowerSplit_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedFiveAdicPowerSplit u v w :=
  signedFiveAdicPowerSplit_of_packet (signedFiveAdicPacket_of_normalForm hNF)
```

本宣言は theorem ではなく `noncomputable def` である。`SignedBranchANormalForm u v w` から signed five-adic packet を作り、その packet から exact power split を選ぶ二つの既存 adapter を合成する。

## 数学的主張

入力は signed Branch-A normal form である。そこから既に構成済みの five-adic packet を経由して、正の互いに素な自然数 $a,b$ と exact power split data を得る。

すなわち返り値 `s : SignedFiveAdicPowerSplit u v w` は少なくとも

$$
s.fiveAdic : \mathrm{SignedFiveAdicPacket}(u,v,w),
$$

$$
s.fiveAdic.carrier = 5^4 s.a^5,
$$

$$
s.fiveAdic.residual = 5 s.b^5,
$$

$$
s.fiveAdic.distinguished = 5 s.a s.b,
$$

$$
0<s.a,\qquad 0<s.b,\qquad \gcd(s.a,s.b)=1
$$

を保持する。

本宣言自身がこれらの算術事実を再証明するわけではない。数学的には

$$
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedFiveAdicPacket}
\longrightarrow
\mathrm{SignedFiveAdicPowerSplit}
$$

という既存構成の合成である。

## 証明全体での役割

この宣言は signed normal form を exact power-split 層へ直接接続する公開入口である。

前段では 0053 `SignedBranchANormalForm` が orientation を保った正規形を与え、0077 `signedFiveAdicPacket_of_normalForm` がそこから carrier / residual / distinguished と five-adic 条件を備えた packet を構成する。0087–0088 ではその packet から exact fifth-power split を存在・選択した。

本宣言はそれらを一段にまとめるため、後続コードは中間 packet を明示的に保持せず、

```lean
signedFiveAdicPowerSplit_of_normalForm hNF
```

だけで exact split に到達できる。

この API 境界の直後には `SignedFiveAdicPowerSplitCore` が置かれる。したがって proof architecture 上は、normal form から「最終的に矛盾させるべき exact split packet」までを接続する最後の adapter である。

## 直接依存する定義・補題

直接依存は次の四つである。

- `SignedBranchANormalForm`
- `SignedFiveAdicPowerSplit`
- `signedFiveAdicPacket_of_normalForm`（0077）
- `signedFiveAdicPowerSplit_of_packet`（0088）

間接的には 0088 を通して 0087 の constructor existence、0082 の gcd exactness、0027 `fifth_power_factor_split`、mod $25$ と coprimality の各補題へ依存する。ただし本宣言の proof term にはそれらは現れない。

## 証明の流れ

証明は関数合成一段で完了する。

### 1. normal form から packet を作る

```lean
signedFiveAdicPacket_of_normalForm hNF
```

により

```lean
SignedFiveAdicPacket u v w
```

を得る。

### 2. packet から power split を選ぶ

その値を

```lean
signedFiveAdicPowerSplit_of_packet
```

へ渡して

```lean
SignedFiveAdicPowerSplit u v w
```

を得る。

Lean term 全体は

```lean
signedFiveAdicPowerSplit_of_packet
  (signedFiveAdicPacket_of_normalForm hNF)
```

であり、case split、rewrite、算術 tactic は不要である。

## Lean 固有の処理

本宣言で重要なのは、implicit parameters `{u v w : ℕ}` が二つの adapter を通してそのまま推論される点である。

`hNF` の型から `u v w` が決まり、

```lean
signedFiveAdicPacket_of_normalForm hNF
```

の返り値の index も同じ `u v w` になる。そのため次の `signedFiveAdicPowerSplit_of_packet` も追加の型注釈なしに同じ index を推論できる。

また本宣言は `noncomputable` である。理由は 0088 が `Classical.choice` によって `Nonempty (SignedFiveAdicPowerSplit u v w)` から witness を選んでいるためであり、本宣言自身が新たな classical reasoning を行っているわけではない。noncomputability が adapter chain を通して伝播しているだけである。

## 冗長・重複箇所

本体は一行なので局所的な冗長性はない。

ただし、数学的には完全な composition wrapper であり、call site で毎回

```lean
signedFiveAdicPowerSplit_of_packet
  (signedFiveAdicPacket_of_normalForm hNF)
```

と書けば本宣言を削除することはできる。

それでも名前付き wrapper を置く意義はある。後続の `signedBranchARefuter_of_powerSplitCore` では、この一語の API によって「normal form から exact split へ移る」という proof architecture が明示される。したがってコード削減より意味上の boundary naming を優先した宣言と評価できる。

## 最適化候補

### 候補 A — 現行 wrapper を維持する

最も自然である。宣言名が層間変換をそのまま表しており、後続 theorem の可読性が高い。

### 候補 B — function composition style に寄せる

概念上は二つの関数の合成なので、局所的には point-free に近い helper を考えることもできる。しかし dependent index を含む Lean コードでは現在の明示的適用の方が型推論とエラーメッセージが読みやすい。

### 候補 C — constructive chain へ統合する

もし 0087–0088 を constructive constructor に再設計できれば、本宣言も `noncomputable` ではない `def` にできる可能性がある。ただし本層は proof-only API であり、計算可能性を得る実利は小さい。

### 候補 D — adapter 命名規則の統一

この周辺には `..._of_normalForm`、`..._of_packet`、`..._of_powerSplitCore` が連続する。層間変換を示す `_of_` 命名は既に整っているため、この規則を他の bridge module にも揃えると proof graph を名前だけで追いやすくなる。

## 必要 Mathlib import と import 最適化候補

対象ブランチの generated standalone artifact は `import Mathlib` で構築されている。

本宣言だけを見ると Mathlib の tactic や算術 theorem を直接使わず、必要なのは二つの project-local declaration の型検査だけである。したがって本宣言単体のために `import Mathlib` 全体を要求する理由はない。

ただし実際の `SignedFiveAdicPowerSplit.lean` module は直前の 0087 を含み、自然数 gcd、coprimality、素数、冪、除算、`ring`、`omega`、`norm_num` などを使用する。module 単位の最小 import はそれらを含めて決定すべきである。

import 最適化候補は、umbrella `Mathlib` を機械的に狭めるのではなく、分割元 module の使用定理・tactic を列挙し、Lean build で段階的に検証することである。本タスクでは Lean build は行わないため、具体的な最小 import 集合は推測で断定しない。

## Comparator challenge 化の可否

可能であるが、数論 challenge ではなく API / proof architecture challenge 向きである。

比較候補は次の通り。

1. 現行の名前付き composition wrapper。
2. call site で二つの adapter を毎回直接合成する方式。
3. packet 層と power-split 層を一つの constructor に統合する方式。
4. constructive constructor 化して `noncomputable` を除く方式。

評価軸は、proof graph の可視性、downstream の簡潔さ、依存境界、エラーメッセージの局所性、classical dependency の見え方である。

現行方式は一行 wrapper ではあるが、proof architecture の層を名前で固定する効果が大きく、Comparator では「冗長 alias か、有益な semantic adapter か」が焦点になる。

## PDF・ソース根拠について

形式的な根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` である。generated manifest では本宣言が `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` 部分に属し、0088 `signedFiveAdicPowerSplit_of_packet` の直後、`SignedFiveAdicPowerSplitCore` の直前に置かれることを確認した。

既存の日英 PDF は叙述的背景資料として扱う。今回 GitHub code search は 502 upstream error となり、本 adapter と一対一対応する PDF の具体的ページ・節番号を確認できなかった。そのため PDF 固有の定理番号・ページ番号・文章は推測で補っていない。

## 次に読むべき定理

source 上で直後に置かれる宣言は

```lean
abbrev SignedFiveAdicPowerSplitCore : Prop :=
  ∀ {u v w : ℕ}, SignedFiveAdicPowerSplit u v w → False
```

である。

これは exact power split packet をすべて矛盾へ送る receiver contract である。次号では

$$
\forall u,v,w,\quad
\mathrm{SignedFiveAdicPowerSplit}(u,v,w)\to\bot
$$

という「残された算術核心」のインターフェースを切り出す。さらにその次の `signedBranchARefuter_of_powerSplitCore` が、本号の adapter を使ってこの core contract を signed Branch-A 全体の refuter へ持ち上げる。