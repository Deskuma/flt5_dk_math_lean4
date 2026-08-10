# 0092 — `branchB_false_of_powerSplitCore`

## Lean の型

```lean
theorem branchB_false_of_powerSplitCore
    (hCore : SignedFiveAdicPowerSplitCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_powerSplitCore hCore) hPack hBranch
```

本定理は `SignedFiveAdicPowerSplit.lean` の終端定理である。0090 `SignedFiveAdicPowerSplitCore` に与えられた exact power-split 層の反証器を、0091 `signedBranchARefuter_of_powerSplitCore` で signed Branch-A refuter に持ち上げ、0058 `branchB_false_of_signedBranchARefuter` に渡すことで routed Branch-B candidate を閉じる。

## 数学的主張

仮定は三つである。

1. 任意の `SignedFiveAdicPowerSplit u v w` は矛盾する。
2. `CounterexamplePack x y z`、すなわち正の原始的 FLT5 候補がある。
3. Branch-B 条件として $5\nmid z-y$ が成り立つ。

このとき結論は `False` である。

概念的には、既存の routing を通して

$$
\mathrm{CounterexamplePack}(x,y,z)
\land 5\nmid(z-y)
\longrightarrow
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedFiveAdicPowerSplit}
\longrightarrow
\bot
$$

という合成を閉じている。

したがって本定理は新しい算術補題ではなく、power-split contradiction core を Branch-B 全体の refutation に昇格させる closure theorem である。

## 証明全体での役割

FLT5 の Branch-B route では、上流で `CounterexamplePack` と $5\nmid z-y$ から signed normal form を作り、さらに five-adic packet、exact power split へと情報を強化してきた。

本定理はその流れを逆方向の abstraction boundary から閉じる。

$$
\mathrm{SignedFiveAdicPowerSplitCore}
\xrightarrow{\;0091\;}
\mathrm{SignedBranchARefuter}
\xrightarrow{\;0058\;}
\text{Branch-B contradiction}
$$

これにより、後続で `SignedFiveAdicPowerSplitCore` の具体的実装が得られれば、Branch-B の routed candidate を再び詳細展開する必要がない。

また source 上では本定理の直後に `SignedFiveAdicPowerSplit.lean` が終了し、次の module `SquareGoldenBridge.lean` が始まる。その意味で本定理は five-adic exact power-split 層の公開 closure API の終点である。

## 直接依存する定義・補題

直接依存は次の通り。

1. `SignedFiveAdicPowerSplitCore`（0090）
2. `signedBranchARefuter_of_powerSplitCore`（0091）
3. `branchB_false_of_signedBranchARefuter`（0058）
4. `CounterexamplePack`（0002）
5. Branch-B 条件 `¬ 5 ∣ z - y`

本定理自身は `SignedFiveAdicPowerSplit` の内部フィールド、gcd、mod $25$、第五冪分解、`padicValNat` などを直接参照しない。それらは 0090 までの power-split construction と `hCore` の実装側へ封じ込められている。

## 証明の流れ

証明は一つの `exact` で終わる。

```lean
exact branchB_false_of_signedBranchARefuter
  (signedBranchARefuter_of_powerSplitCore hCore) hPack hBranch
```

展開すると二段である。

1. `signedBranchARefuter_of_powerSplitCore hCore` により、exact power split を矛盾させる core から `SignedBranchARefuter` を得る。
2. その refuter と `hPack`、`hBranch` を `branchB_false_of_signedBranchARefuter` に渡して `False` を得る。

数学的には完全な関数合成であり、本 theorem 自体に新しい case split や数式変形はない。

## Lean 固有の処理

### 1. 高水準 API だけで閉じる

証明本文には `rw`、`simp`、`ring`、`omega`、`norm_num` が現れない。必要な算術はすべて依存 theorem の型へ押し込まれている。

### 2. implicit 引数の推論

`{x y z : ℕ}` は `hPack` と `hBranch` から推論される。0091 側でも signed normal-form index は witness の型から推論されるため、本定理は index を再指定しない。

### 3. proposition-valued refuter の合成

`SignedFiveAdicPowerSplitCore` と `SignedBranchARefuter` はどちらも最終的に `False` を返す proposition-valued function contract である。Lean の型検査は、この contravariant な refuter lifting と Branch-B closure の接続を直接検証する。

### 4. `noncomputable` の伝播は不要

0091 の内部で用いる `signedFiveAdicPowerSplit_of_normalForm` は classical choice に由来する `noncomputable def` だが、本 theorem は proof-only な `False` の導出であり、宣言自身に `noncomputable` は不要である。

## 冗長・重複箇所

コード量だけを見れば、本 theorem は 0091 と 0058 の合成を名前付きで保存しているだけなので inline 化できる。

例えば理論上は `branchB_false_of_signedBranchARefuter` の call site へ 0091 の内容を埋め込める。しかし、そうすると

$$
\mathrm{SignedFiveAdicPowerSplitCore}
\Longrightarrow
\text{Branch-B contradiction}
$$

という proof graph の重要な辺が宣言名として失われる。

本 theorem は module 終端の closure API であり、重複というより layer boundary を明示するための意図的な adapter と評価するのがよい。

## 最適化候補

### 候補 A — 現行の closure theorem を維持

最も domain terminology を保ちやすい。後続 module は Branch-B routing の内部を知る必要がない。

### 候補 B — 0091 を inline 化

```lean
exact branchB_false_of_signedBranchARefuter
  (fun u v w hNF => hCore (signedFiveAdicPowerSplit_of_normalForm hNF))
  hPack hBranch
```

のような形へ縮められる可能性がある。ただし proof graph の可読性は低下する。

### 候補 C — generic closure combinator

一般に

$$
(A\to B)\to(B\to\bot)\to(A\to\bot)
$$

という refuter lifting を generic helper として表すことはできる。しかし FLT5 の各層名が消えるため、監査性との交換条件になる。

### 候補 D — module-level façade を明示

`SignedFiveAdicPowerSplit.lean` の最終 API として本 theorem を export point と位置づけ、内部 constructor 群を private / scoped に寄せる設計も考えられる。これは数学最適化ではなく module architecture 最適化である。

## 必要 Mathlib import と import 最適化候補

対象ブランチの generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用している。

本 theorem 自体は `exact` と project-local declarations の合成だけであり、Mathlib の個別算術 theorem や tactic を直接呼ばない。したがって theorem 単体の観点では umbrella `Mathlib` は過大である。

一方、実際の `SignedFiveAdicPowerSplit.lean` module 前半では自然数の divisibility、coprimality、prime、冪、除算、`ring`、`omega`、`norm_num` 等が使われる。このため module 全体の最小 import は前半の必要性に支配される。

今回、分割元 source file の独立 import header はリポジトリ内で直接取得できず、standalone artifact のみ確認できた。また Lean build は指示により実行していない。したがって最小 Mathlib import の具体的 module 名は推測で断定しない。

import 最適化を行うなら、generated standalone の `import Mathlib` を根拠にせず、元 module の direct imports と tactic 使用箇所を列挙し、別作業で build 検証するのが安全である。

## Comparator challenge 化の可否

適している。ただし challenge の中心は数論ではなく proof architecture である。

比較候補は次の通り。

1. 現行の 0091 + 0058 を名前付きで合成する方式。
2. 0091 を inline 化する方式。
3. generic refuter-lifting helper を使う方式。
4. Branch-B closure と power-split closure を一つの theorem に統合する方式。
5. module façade として本 theorem を維持し、内部 helper の visibility を狭める方式。

評価軸はコード長、domain terminology、依存方向の可視性、型エラーの局所性、再利用性、proof graph の監査容易性である。

現行実装は一行だが、module 終端で `SignedFiveAdicPowerSplitCore → Branch-B contradiction` を明示するため、設計上の価値は高い。

## PDF・ソース根拠について

形式的な最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` である。source 上で本 theorem は `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` の最後の theorem として置かれ、その直後で module が終了することを確認した。

既存の日本語・英語 PDF は叙述的背景資料として扱う。今回も GitHub code search は upstream 502 を返し、この closure theorem と一対一対応する PDF の具体的ページ・節番号を確定できなかった。そのため PDF 固有の番号・引用は推測で補っていない。

なお分割元の `Flt5DkMath/DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` という想定パスは対象ブランチ上で 404 となり、確認できた一次資料は generated standalone artifact である。この点も推測と事実を分離して扱う。

## 次に読むべき宣言

source 上で次に始まる module は `DkMath/FLT/Five/SquareGoldenBridge.lean` であり、その最初の宣言は

```lean
def GoldenNorm (m n : ℤ) : ℤ :=
  m ^ 2 + m * n - n ^ 2
```

である。

これは五次円分因子を黄金比の二次形式へ写す次の層の入口である。続く `GN5_eq_square_cross_form`、`square_cross_coordinate_change`、`GN5_eq_goldenNorm_squareLink` により、`GN5` が

$$
\mathrm{GoldenNorm}(m,n)=m^2+mn-n^2
$$

として再表現される。

したがって 0092 で five-adic exact power-split module を閉じ、0093 から square / golden norm bridge の新しい章へ入る。