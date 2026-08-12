# 0116 — `signedBranchARefuter_of_squareGoldenExceptionalCore`

## Lean の型

```lean
/-- A refuter for every exceptional square-golden packet closes both signed orientations. -/
theorem signedBranchARefuter_of_squareGoldenExceptionalCore
    (hCore : SignedSquareGoldenExceptionalCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)
```

本定理は `SignedSquareGoldenExceptionalCore` から `SignedBranchARefuter` を構成する adapter theorem である。

## 数学的主張

`SignedSquareGoldenExceptionalCore` は、任意の $u,v,w$ に対して

$$
\operatorname{SignedSquareGoldenExceptionalPacket}(u,v,w)\to\bot
$$

を与える contradiction receiver である。

一方 `SignedBranchARefuter` は、任意の $u,v,w$ に対して

$$
\operatorname{SignedBranchANormalForm}(u,v,w)\to\bot
$$

を要求する。

0114 `signedSquareGoldenExceptionalPacket_of_normalForm` が

$$
\operatorname{SignedBranchANormalForm}(u,v,w)
\longrightarrow
\operatorname{SignedSquareGoldenExceptionalPacket}(u,v,w)
$$

を与えるため、本定理はこの変換を `hCore` の前に合成して

$$
\operatorname{SignedBranchANormalForm}(u,v,w)
\longrightarrow
\operatorname{SignedSquareGoldenExceptionalPacket}(u,v,w)
\longrightarrow
\bot
$$

を得る。

数学的には、新しい代数恒等式や divisibility fact を証明しているのではなく、すでに確立した「正規形から packet を作る写像」と「packet は矛盾するという core」を接続している。

## 証明全体での役割

この theorem は signed Branch-A 層と square-golden exceptional 層の **境界 adapter** である。

0111–0114 では square-golden exceptional packet を構築する producer 側を整え、0115 ではその packet を受け取れば `False` を返す receiver contract を定義した。0116 は両者を接続し、下流の contradiction を上流の `SignedBranchANormalForm` 全体へ引き戻す。

```text
SignedBranchANormalForm
  → SignedSquareGoldenExceptionalPacket
  → False
```

これにより、以後の Branch-B 閉包 theorem は square-golden packet の内部構造を再び展開する必要がなく、`SignedBranchARefuter` という既存 API を通して contradiction を受け取れる。

## 直接依存する定義・補題

### `SignedSquareGoldenExceptionalCore`

0115 で解説した contradiction receiver。

```lean
abbrev SignedSquareGoldenExceptionalCore : Prop :=
  ∀ {u v w : ℕ}, SignedSquareGoldenExceptionalPacket u v w → False
```

### `SignedBranchARefuter`

signed Branch-A normal form を排除する既存 contract。

```lean
abbrev SignedBranchARefuter : Prop :=
  ∀ {u v w : ℕ}, SignedBranchANormalForm u v w → False
```

### `signedSquareGoldenExceptionalPacket_of_normalForm`

0114 で解説した producer。

```lean
noncomputable def signedSquareGoldenExceptionalPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedSquareGoldenExceptionalPacket u v w :=
  signedSquareGoldenExceptionalPacket_of_powerSplit
    (signedFiveAdicPowerSplit_of_normalForm hNF)
```

この三者だけで本 theorem の論理構造は閉じている。

## 証明の流れ

証明は二段階だけである。

1. `intro u v w hNF` によって `SignedBranchARefuter` の全称量化された indices と normal-form 仮定を導入する。
2. `signedSquareGoldenExceptionalPacket_of_normalForm hNF` で packet を構築し、それを `hCore` に渡して `False` を得る。

```lean
exact hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)
```

この一行が theorem 全体の数学的内容をほぼ完全に表している。

## Lean 固有の処理

### 期待型による `intro`

goal は `SignedBranchARefuter` という `abbrev` だが、Lean はその本体

```lean
∀ {u v w : ℕ}, SignedBranchANormalForm u v w → False
```

まで展開して `intro u v w hNF` を受理する。

### implicit indices の推論

`hCore` も producer も `{u v w : ℕ}` を implicit parameters として持つ。`hNF` の型から indices が推論されるため、

```lean
signedSquareGoldenExceptionalPacket_of_normalForm hNF
```

および

```lean
hCore (...)
```

の双方で explicit named arguments は不要である。

### `noncomputable` の伝播について

利用している `signedSquareGoldenExceptionalPacket_of_normalForm` は `noncomputable def` だが、本 theorem 自身は proposition を証明する theorem なので `noncomputable` を付ける必要はない。classical choice を含む object construction は producer 側に隔離され、本 theorem ではその結果を proof term として利用しているだけである。

### tactic-free に近い構造

`intro` を除けば本体は単一の `exact` であり、`rw`、`simp`、`ring`、`omega`、cast 処理などは一切ない。すべての代数的・five-adic・signed orientation 処理が上流 declarations に隠蔽されていることの表れである。

## 冗長・重複箇所

この theorem の形は以前の producer/consumer bridge と同型である。

概念的には

```lean
(A → B) → (B → False) → (A → False)
```

という否定の前合成にすぎない。

その意味では generic helper に抽象化できる重複がある。しかし、`signedBranchARefuter_of_squareGoldenExceptionalCore` という名前自体が proof graph の層間遷移を記録しているため、architecture documentation としては有益な重複である。

また `by intro ...; exact ...` はラムダ式

```lean
fun hNF => hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)
```

に近い構造であり、さらに短く書く余地はある。ただし現行形は indices と normal form の導入を明示するため読みやすい。

## 最適化候補

### 1. 直接ラムダ式化

概念的には次のような point-free / lambda 寄りの形へ圧縮可能である。

```lean
by
  intro u v w hNF
  exact hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)
```

現行ですでに十分短いため、実質的な改善幅は小さい。

### 2. generic refuter transport

indexed propositions / packet families に対して

```lean
(A i → B i) → (B i → False) → (A i → False)
```

を輸送する generic helper を導入すれば同型 theorem を共通化できる。

ただし theorem 名から proof layer が明示される利点を失うため、ライブラリ全体で同型 adapter が大量に現れる場合に限って検討するのがよい。

### 3. producer と core の API 安定性維持

最も価値の高い最適化は行数削減よりも、producer が `SignedSquareGoldenExceptionalPacket` を返し、core が同じ packet を受け取る interface を維持することである。この一致により adapter が一行で閉じている。

## 必要 Mathlib import と import 最適化候補

対象 standalone source は

```lean
import Mathlib
```

を使用している。

本 theorem 自身が直接利用する Mathlib 機能はほぼなく、必要なのは Lean の関数適用、全称量化、`False`、`intro` / `exact` と project declarations だけである。`ring`、`omega`、整数演算 API、divisibility API などは直接使わない。

したがって modular source では、本 theorem のためだけに `Mathlib` 全体を import する必要はない。実際の import requirement は `SignedSquareGoldenExceptionalCore`、`SignedBranchARefuter`、`signedSquareGoldenExceptionalPacket_of_normalForm` を提供する modules の transitive closure に従う。

この repository の standalone artifact では source modules が結合され `import Mathlib` に集約されているため、最小 import 集合はここからは確定できない。Lean build を行っていないため、具体的な import 削減案は未検証である。

## Comparator challenge 化の可否

**可能。特に proof composition / API design 比較に向く。**

比較案としては次が考えられる。

- 現行の `intro` + `exact`
- ラムダ式による直接 composition
- generic refuter transport helper を使う版
- producer を展開して `SignedFiveAdicPowerSplit` から直接 packet を作る版
- `SignedBranchARefuter` を `abbrev` のまま使う版と展開型を直接書く版

評価軸は、コード行数だけでなく、依存の局所性、エラーメッセージ、proof graph の可読性、上流実装変更への耐性である。

特に producer を展開する版は短期的には依存を減らさず、むしろ 0112–0114 の abstraction boundary を破るため、現行 theorem の方が architecture 上は優れている可能性が高い。

## 既存 PDF との対応

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。

本記事の形式的根拠は、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` generated section である。

今回 GitHub connector から PDF 本文の該当ページを直接照合していないため、PDF 上の具体的な節番号・ページ番号は推測で補っていない。

## 次に読むべき定理

直後の未解説 theorem は

```lean
/-- The same square-golden core consequently closes every routed Branch-B pack. -/
theorem branchB_false_of_squareGoldenExceptionalCore
    (hCore : SignedSquareGoldenExceptionalCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_squareGoldenExceptionalCore hCore) hPack hBranch
```

である。

0116 が `SignedSquareGoldenExceptionalCore` を `SignedBranchARefuter` へ transport し、次 theorem は既存の `branchB_false_of_signedBranchARefuter` に渡して Branch-B candidate 全体を閉じる。依存順ではこれを 0117 として読むのが自然である。
