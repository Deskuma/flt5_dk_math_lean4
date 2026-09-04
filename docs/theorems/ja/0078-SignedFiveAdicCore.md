# 0078 — `SignedFiveAdicCore`

## Lean の型

```lean
abbrev SignedFiveAdicCore : Prop :=
  ∀ {u v w : ℕ}, SignedFiveAdicPacket u v w → False
```

この宣言は theorem ではなく `abbrev` による命題の別名である。任意の `u v w : ℕ` と、それらに対応する `SignedFiveAdicPacket u v w` を受け取れば `False` を返せる、という contradiction receiver の型を一行で定義している。

## 数学的主張

数学的内容は、0075 で定義された exact five-adic packet が実在しない、という反証器の仕様である。

`SignedFiveAdicPacket u v w` は、ある signed Branch-A normal form から作られた carrier / residual / distinguished の因数分解と five-adic 情報を保持する。したがって `SignedFiveAdicCore` は概念的には

$$
\forall u,v,w,\quad
\mathrm{SignedFiveAdicPacket}(u,v,w)\Longrightarrow\bot
$$

を表す。

本宣言自身はまだ矛盾を証明していない。後段が実装すべき「任意の packet を矛盾へ送る関数」の型を定めているだけである。

## 証明全体での役割

0076–0077 が normal form から packet を構築する側の API を整え、本号はその packet を消費する側の API を定める。

直後の

```lean
theorem signedBranchARefuter_of_fiveAdicCore
    (hCore : SignedFiveAdicCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedFiveAdicPacket_of_normalForm hNF)
```

では、0077 の chosen packet を `hCore` に渡すだけで `SignedBranchARefuter` が得られる。これにより packet construction と contradiction argument が明確に分離される。

さらにその次の `branchB_false_of_fiveAdicCore` は、既存の `branchB_false_of_signedBranchARefuter` を経由して Branch B 全体を閉じる。したがって本宣言は five-adic contradiction の受信口であり、Branch B closure への共通インターフェースである。

## 直接依存する定義・補題

直接依存は一つだけである。

- `SignedFiveAdicPacket`

`SignedFiveAdicCore` の定義本体は `SignedBranchANormalForm`、`padicValNat`、`GN5`、`ZMod 25` などを直接参照しない。そうした算術情報は packet のフィールドへ既に封じ込められている。

これは 0075 で作った record abstraction が実際に効いている箇所である。

## 証明の流れ

この宣言自体に proof script はない。`abbrev` による型定義なので、流れは次の一段だけである。

1. 任意の `u v w : ℕ` を暗黙引数として受け取る。
2. `SignedFiveAdicPacket u v w` を受け取る。
3. 結果として `False` を返すことを要求する。

すなわち、実装者が後で埋めるべき core の関数型を先に固定している。

## Lean 固有の処理

### `abbrev` の意味

`abbrev` は reducible な略記であり、Lean は必要に応じて

```lean
SignedFiveAdicCore
```

を

```lean
∀ {u v w : ℕ}, SignedFiveAdicPacket u v w → False
```

へ展開できる。

したがって、通常の `def` に比べて型同値の adapter をほとんど要求せず、後段 theorem では `hCore packet` のように関数としてそのまま使える。

### `Prop` に置く意味

戻り値は `False` であり、この core は証明オブジェクトである。計算データを生成する interface ではないため `Prop` として定義される。

### 暗黙引数

`{u v w : ℕ}` は implicit なので、packet の型から通常は Lean が推論できる。直後の theorem でも

```lean
hCore (signedFiveAdicPacket_of_normalForm hNF)
```

だけでよく、`u v w` を明示する必要がない。

## 冗長・重複箇所

本宣言自身に冗長性はほぼない。一行の type alias であり、むしろ後続 API の重複を減らす役割を持つ。

ただし設計上は、

```lean
abbrev SignedFiveAdicCore : Prop :=
  ∀ {u v w : ℕ}, SignedFiveAdicPacket u v w → False
```

という名前付き alias を置かず、各 theorem の引数へこの関数型を直接書くことも可能である。その場合は宣言数は減るが、proof architecture 上の「five-adic contradiction core」という境界名が失われる。

したがって現行の一行 alias は、コード量より概念境界を優先した妥当な冗長性と評価できる。

## 最適化候補

最適化候補は主として API 設計である。

第一に、将来 packet が複数種類へ分岐するなら、`SignedFiveAdicCore` を generic receiver として抽象化する案がある。例えば

```lean
abbrev Refuter (α : Sort _) : Prop := α → False
```

のような一般 alias を置けるが、本リポジトリでは domain-specific な名前の方が証明経路を追いやすい可能性が高い。

第二に、後段で常に `SignedFiveAdicPacket` から同じ少数フィールドしか使わないことが確認できれば、core が受け取る interface を packet 全体ではなく薄い contradiction kernel に縮約できる可能性がある。ただしこれは後続証明を読んでから判断すべきであり、現時点では推測である。

第三に、`abbrev` と `def` の比較も可能だが、ここでは reducible alias として自然であり、積極的に変更する理由は今のところ弱い。

いずれも Lean ビルド未実施の設計案である。

## 必要 Mathlib import と import 最適化候補

対象 standalone artifact は `import Mathlib` を使用している。本宣言そのものは Mathlib の特別な算術 API を直接使用せず、必要なのは Lean の基本論理とローカル定義 `SignedFiveAdicPacket` だけである。

manifest 上ではこの領域は `DkMath/FLT/Five/SignedFiveAdic.lean` に属する。したがって実際の最小 import は、`SignedFiveAdicPacket` を提供するローカルモジュールを import すれば足りる可能性が高い。

ただし対象ブランチでは生成 standalone を最終根拠として確認しており、分割元モジュールの実 import graph を今回再検証していない。よって正確な最小 Mathlib import は未確認である。

## 既存 PDF との関係

今回の最終根拠は対象ブランチの Lean source である。既存の日本語・英語 PDF にこの一行の `abbrev` と一対一対応する具体的ページは今回特定できていないため、PDF 固有の説明やページ番号は推測で補っていない。

## Comparator challenge 化の可否

**適している。** ただし theorem proving より proof architecture / API design 比較向きである。

比較候補は、

- 現行の domain-specific `SignedFiveAdicCore`
- 生の関数型を各 theorem に直接書く方式
- generic `Refuter α := α → False`
- packet 全体ではなく最小 contradiction kernel を受け取る方式

である。

評価軸は、依存の見通し、error message の読みやすさ、後段 theorem の簡潔さ、再利用性、過剰抽象化の有無である。

## 次に読むべき定理

次は

```lean
theorem signedBranchARefuter_of_fiveAdicCore
    (hCore : SignedFiveAdicCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedFiveAdicPacket_of_normalForm hNF)
```

である。

0078 が contradiction receiver の型を定め、次号は 0077 の normal-form-to-packet adapter と組み合わせて `SignedBranchARefuter` を実際に構成する。ここで packet 層の five-adic core が signed Branch-A 全体の refuter へ昇格する。