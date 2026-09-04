# 0236 — `signedGoldenRamifierStrippedPacket_of_normalForm`

## Lean の型

```lean
/-- Chosen ramifier-stripped packet directly from a signed normal form. -/
noncomputable def signedGoldenRamifierStrippedPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedGoldenRamifierStrippedPacket u v w :=
  signedGoldenRamifierStrippedPacket_of_powerSplit
    (signedFiveAdicPowerSplit_of_normalForm hNF)
```

これは `theorem` ではなく `noncomputable def` である。signed Branch-A normal form `hNF` から、five-adic power split を経由して、ramifier-stripped packet を一つ選び出す合成 API を与える。

## 数学的主張・宣言の意味

この宣言は新しい等式や整除性を証明するものではない。既に構築済みの二つの変換

$$
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedFiveAdicPowerSplit}
$$

と

$$
\mathrm{SignedFiveAdicPowerSplit}
\longrightarrow
\mathrm{SignedGoldenRamifierStrippedPacket}
$$

を合成し、normal-form 層から stripped-packet 層へ直接移る経路を公開する。

得られる packet は、下流から見ると概念的に

$$
\alpha=\tau\beta,
$$

$$
N(\beta)=b^5,
$$

$$
5\nmid N(\beta),
$$

$$
\tau\nmid\beta
$$

という「可視 ramifier $\tau$ を一度除去した状態」を保持する。したがって本宣言は、signed normal form を黄金整数環の stripped state へ直接送る representation bridge である。

## 証明全体での役割

0233 では exceptional packet から stripped packet の存在を構成し、0234 で `Classical.choice` により具体的 packet object を選んだ。0235 は exact five-adic power split からその object へ直接到達する bridge を追加した。

0236 はさらに一段上の `SignedBranchANormalForm` から stripped packet へ直結する。

これにより下流の反証 core は、five-adic split や exceptional packet の中間表現を自分で組み立てる必要がない。実際、直後の `signedBranchARefuter_of_goldenRamifierStrippedCore` では、normal form `hNF` に対して本定義をそのまま適用し、stripped core へ packet を渡している。

したがって本宣言は、局所的な algebra theorem というより、FLT5 signed Branch-A pipeline の adapter / facade として重要である。

## 直接依存する定義・補題

直接依存は二つである。

- `signedFiveAdicPowerSplit_of_normalForm`
- 0235 `signedGoldenRamifierStrippedPacket_of_powerSplit`

型としては次にも依存する。

- `SignedBranchANormalForm`
- `SignedFiveAdicPowerSplit`
- `SignedGoldenRamifierStrippedPacket`

概念的な依存グラフは

$$
\texttt{SignedBranchANormalForm}
\xrightarrow{\texttt{signedFiveAdicPowerSplit_of_normalForm}}
\texttt{SignedFiveAdicPowerSplit}
\xrightarrow{\texttt{signedGoldenRamifierStrippedPacket_of_powerSplit}}
\texttt{SignedGoldenRamifierStrippedPacket}
$$

である。

## 構築の流れ

実装は関数合成そのものである。

```lean
signedGoldenRamifierStrippedPacket_of_powerSplit
  (signedFiveAdicPowerSplit_of_normalForm hNF)
```

1. `hNF` から signed five-adic power split を構成する。
2. その split を 0235 に渡す。
3. ramifier-stripped packet を返す。

証明 tactic、座標計算、`ring`、`omega`、`norm_num` は存在しない。数学的な重い作業はすべて上流 API に委譲されている。

## Lean 固有の処理

`noncomputable def` である理由は、0235 の先で 0234 `signedGoldenRamifierStrippedPacket_of_exceptional` が `Classical.choice` を使って packet を選んでいるためである。本定義自身は choice を直接呼ばないが、依存先が noncomputable なので結果として noncomputable になる。

Lean 上ではこの種の宣言を置くことで、下流 proof は

```lean
signedGoldenRamifierStrippedPacket_of_normalForm hNF
```

と一行で packet を取得できる。中間型に対する type annotation や local `let` を持たずに済むため、representation change の影響範囲を狭める facade として機能する。

## 冗長・重複箇所

論理的には完全に合成なので、下流で毎回

```lean
signedGoldenRamifierStrippedPacket_of_powerSplit
  (signedFiveAdicPowerSplit_of_normalForm hNF)
```

と書けば本宣言は不要である。

しかし専用名を持たせる利点は大きい。

- normal-form consumer が中間 representation を知らずに済む。
- pipeline の意味が theorem / def 名として可視化される。
- 中間変換の実装が変更されても downstream API を維持しやすい。
- refuter や closure theorem の proof term が短くなる。

したがってこれは情報論的には冗長だが、API 設計上は有用な冗長性である。

## 最適化候補

1. **現行 facade を維持する**
   - downstream の依存を最小化でき、最も読みやすい。

2. **0235 と 0236 を削除して explicit composition に統一する**
   - 宣言数は減るが、中間 representation が下流へ漏れる。

3. **変換 pipeline を structure / namespace API として統一する**
   - `of_normalForm`, `of_powerSplit`, `of_exceptional` の命名規則を揃えれば、変換 graph がさらに追いやすくなる。

4. **choice 境界を一箇所に集約する**
   - packet 構築を explicit witness data へ寄せられるなら `noncomputable` propagation を減らせる可能性がある。

現状では本宣言は一行で十分に明瞭であり、局所的な短縮余地はほぼない。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本宣言自体は tactic も一般 Mathlib theorem も直接使用しない。

直接必要なのは上流の FLT5 型・変換 API であり、Mathlib 側の依存はそれらの module が要求するものに支配される。

したがって本宣言単独だけを見れば非常に軽量だが、`SignedGoldenRamifierStripped.lean` 全体の最小 import は five-adic arithmetic、GoldenInt、norm、divisibility などの上流依存まで含めて測る必要がある。今回は Lean build を行わないため、厳密な最小 import 集合は未検証である。

## Comparator challenge 化の可否

適している。ただし theorem proving というより API architecture の比較課題である。

比較候補は次の通り。

- A: 現行の named facade
- B: downstream で explicit composition
- C: generic conversion pipeline / typeclass 化
- D: packet constructor を computable witness まで含めて再設計

比較軸は、downstream proof の長さ、中間 representation への coupling、refactor 耐性、`noncomputable` propagation、API discoverability である。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` generated section である。

source 上では 0235 `signedGoldenRamifierStrippedPacket_of_powerSplit` の直後に本宣言があり、その直後に `SignedGoldenRamifierStrippedCore` が置かれている。

対象ブランチには日本語・英語 PDF も存在するが、本 `noncomputable def` に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0237 `SignedGoldenRamifierStrippedCore`** である。

```lean
/-- Receiver contract for contradictions stated after the visible ramifier is removed. -/
abbrev SignedGoldenRamifierStrippedCore : Prop :=
  ∀ {u v w : ℕ}, SignedGoldenRamifierStrippedPacket u v w → False
```

0236 までで normal form から stripped packet へ直接到達できるようになった。0237 は、その stripped packet を受け取れば矛盾を返す、という downstream contradiction contract を型として定義する段階に入る。
