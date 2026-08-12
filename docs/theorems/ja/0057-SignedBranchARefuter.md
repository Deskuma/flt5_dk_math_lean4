# 0057 — `SignedBranchARefuter`

## Lean の型

```lean
abbrev SignedBranchARefuter : Prop :=
  ∀ {u v w : ℕ}, SignedBranchANormalForm u v w → False
```

`SignedBranchARefuter` は定理ではなく `Prop` の省略名 (`abbrev`) であり、任意の自然数三つ組 `u v w` について `SignedBranchANormalForm u v w` が与えられれば `False` を導ける、という共通反駁器の契約を表す。

## 数学的主張

前号までで構成された signed Branch A 正規形は、正の原始的な Fermat 5 候補と、五進的に例外となる二つの向きのいずれかを一つに束ねていた。本宣言は、そのどちらの向きであっても最終的には矛盾へ到達できる、という後段降下の要求仕様を一つの命題にまとめる。

概念的には

$$
\forall u,v,w\in\mathbb N,
\quad
\operatorname{SignedBranchANormalForm}(u,v,w)
\Longrightarrow \bot
$$

である。

ここではまだ矛盾の具体的な理由を与えない。five-adic valuation、power split、square-golden、golden-order など後続の各層が、この契約を実装する。

## 証明全体での役割

`SignedBranchARefuter` は前段の routing と後段の descent を分離するインターフェースである。

前段は `signedBranchA_normalForm_of_branchB` によって Branch B 候補を

```text
SignedBranchANormalForm y x z
        ∨
SignedBranchANormalForm x y z
```

へ送る。後段は座標の由来や分岐履歴を知らず、正規形だけを受け取って `False` を返せばよい。

このため証明全体は

```text
Branch B candidate
      ↓ routing
SignedBranchANormalForm
      ↓ SignedBranchARefuter
     False
```

という明確な二段構成になる。

## 直接依存する定義・補題

直接の型依存は次の一つである。

- `SignedBranchANormalForm u v w`

この構造体は `CounterexamplePack u v w` と `SignedBranchAOrientation u v w` を保持する。

本宣言自身は `signedBranchA_normalForm_of_branchB` を型の中では参照しないが、直後の `branchB_false_of_signedBranchARefuter` が両者を合成するため、説明上は前号 0056 が直前の producer である。

## 証明の流れ

本宣言は `abbrev` なので証明項を持たない。意味を展開すると、利用側では次の形になる。

```lean
intro u v w hNF
-- goal: False
-- hNF : SignedBranchANormalForm u v w
...
```

すなわち、実装者は任意の `u v w` と正規形 `hNF` を受け取り、そこから矛盾を構成する。

後続ソースでは実際に、より深い core からこの契約を構成する補題が繰り返し現れる。例えば five-adic 層では概念的に

```lean
intro u v w hNF
exact hCore (signedFiveAdicPacket_of_normalForm hNF)
```

という形で、正規形をより精密な packet へ変換し、その packet を排除する core に渡す。

## Lean 固有の処理

### `abbrev ... : Prop`

`abbrev` は定義を軽量な別名として与える。ここでは新しい inductive/structure を作るのではなく、全称量化された関数型

```lean
∀ {u v w : ℕ}, SignedBranchANormalForm u v w → False
```

に名前を付けている。

### 暗黙引数 `{u v w : ℕ}`

三変数は暗黙引数なので、通常の利用時は `hRefuter hNF` のように正規形から Lean が `u v w` を推論できる。

### `→ False` と否定

Lean では `¬ P` は `P → False` の略である。したがって本契約は概念的には

```lean
∀ {u v w : ℕ}, ¬ SignedBranchANormalForm u v w
```

と同値である。ただし現在の関数型表現は、`hRefuter hNF` と直接適用できるため consumer 側で扱いやすい。

## 冗長・重複箇所

本宣言は非常に小さく、実装上の冗長性はほぼない。

ただし論理的には次の書き方も可能である。

```lean
abbrev SignedBranchARefuter : Prop :=
  ∀ {u v w : ℕ}, ¬ SignedBranchANormalForm u v w
```

これは定義展開後に同じ型となるため、現行表現との数学的差はない。

また、後続には `SignedFiveAdicCore`、`SignedFiveAdicPowerSplitCore` など「任意 packet を False に送る」同型の契約が多数現れる。この反復は設計上意図的であり、各層の境界を明示する利点がある一方、共通の generic refuter 型を導入する余地はある。

## 最適化候補

### 1. generic refuter の抽象化

例えば

```lean
abbrev Refuter (P : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ {u v w : ℕ}, P u v w → False
```

を置けば、

```lean
abbrev SignedBranchARefuter := Refuter SignedBranchANormalForm
```

とできる。

ただし、この抽象化はコード量を減らす一方で、各 proof layer の固有名が持つ説明力を弱める可能性がある。博物館の観点では現行の明示的命名は十分合理的である。

### 2. `¬` 表記への変更

`→ False` を `¬` に変えると否定命題であることは視覚的に明確になる。しかし後続で refuter を関数として適用するコードには差がないため、好みの範囲である。

## 必要な Mathlib import

対象ブランチの生成済み `Flt5DkMath/FLT5StandAlone.lean` は全体として

```lean
import Mathlib
```

を使用している。

一方、`SignedBranchARefuter` 自身は Mathlib の特別な定理や tactic を直接使用せず、必要なのは `ℕ`、`Prop`、`False` と、プロジェクト内の `SignedBranchANormalForm` だけである。

元の分割モジュール `DkMath/FLT/Five/SignedBranchA.lean` の正確な import 行は生成 artifact からは確認できないため、以下は **推測** である。最小化するなら Mathlib 全体ではなく、`SignedBranchANormalForm` を提供するプロジェクト内モジュールと、その依存があれば十分である可能性が高い。

### import 最適化候補

本宣言単体を理由に追加の Mathlib import は不要と考えられる。最適化は `SignedBranchA.lean` 全体の tactic・算術依存を調べて決めるべきであり、本 `abbrev` だけを基準に import を削るのは適切ではない。

## Comparator challenge 化の可否

**可。ただし難度は低い。**

課題としては、次の仕様を与えて最小の Lean 宣言を作らせる形式が適している。

> `SignedBranchANormalForm u v w` を任意の三つ組について排除する proposition-level contract を定義せよ。consumer からは関数適用で使えること。

比較ポイントは、

- `abbrev` / `def` の選択
- `→ False` / `¬` の選択
- 暗黙引数の利用
- 不要な structure を導入しないこと

である。

数学的証明課題というより、Lean API 設計の Comparator challenge に向いている。

## 根拠と推測

`SignedBranchARefuter` の宣言本体、直後に `branchB_false_of_signedBranchARefuter` が続くこと、および後続に `signedBranchARefuter_of_fiveAdicCore` など複数の実装 bridge が存在することは、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` で確認した。

分割元 `SignedBranchA.lean` の正確な import 行については standalone artifact では復元できないため、最小 import に関する記述は推測として明示した。

## 次に読むべき定理

次は

```lean
DkMath.FLT.Five.branchB_false_of_signedBranchARefuter
```

を読む。

これは前号 0056 の routing theorem と本号の refuter 契約を初めて直接合成し、任意の Branch B 候補から `False` を得る小さな closure theorem である。ここで「入口側の分岐処理」と「後段の共通降下」が完全に接続される。
