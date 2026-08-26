# 0235 — `signedGoldenRamifierStrippedPacket_of_powerSplit`

## Lean の型

```lean
/-- Chosen ramifier-stripped packet from the exact five-adic power split. -/
noncomputable def signedGoldenRamifierStrippedPacket_of_powerSplit
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    SignedGoldenRamifierStrippedPacket u v w :=
  signedGoldenRamifierStrippedPacket_of_exceptional
    (signedSquareGoldenExceptionalPacket_of_powerSplit s)
```

これは `theorem` ではなく `noncomputable def` であり、exact five-adic power split `s` から、square-golden exceptional packet を経由して ramifier-stripped packet を一つ得るための合成 API である。

## 数学的主張・宣言の意味

`SignedFiveAdicPowerSplit u v w` は、signed five-adic packet から唯一の共通因子 `5` を整理した後の exact power split を保持する。特にその内部には概念的に

$$
\mathrm{carrier}=5^4a^5,
$$

$$
\mathrm{residual}=5b^5,
$$

$$
\mathrm{distinguished}=5ab
$$

という fifth-power 分解と、`a,b` の正値性・互いに素性が保存されている。

本定義は、この `s` をまず

```lean
signedSquareGoldenExceptionalPacket_of_powerSplit s
```

によって square-golden exceptional packet へ持ち上げ、さらに 0234

```lean
signedGoldenRamifierStrippedPacket_of_exceptional
```

へ渡す。

したがって構造の流れは

$$
\mathrm{SignedFiveAdicPowerSplit}
\longrightarrow
\mathrm{SignedSquareGoldenExceptionalPacket}
\longrightarrow
\mathrm{SignedGoldenRamifierStrippedPacket}
$$

である。

得られる stripped packet は、可視 ramifier

$$
\tau=2+\varphi
$$

を一度取り除いた

$$
\alpha=\tau\beta
$$

を保持し、さらに

$$
N(\beta)=b^5,
$$

$$
\beta_{\mathrm{snd}}=-5^7a^{10},
$$

$$
5\nmid b,
$$

$$
5\nmid N(\beta),
$$

$$
\tau\nmid\beta
$$

という certificate を downstream に公開する。

本宣言自身はこれらを再証明せず、既に構築済みの二つの変換を合成しているだけである。

## 証明全体での役割

0231–0234 では、square-golden exceptional packet から ramifier-stripped packet を作る層が完成した。一方、そのさらに上流では `SignedFiveAdicPowerSplit` が five-adic normalization の主要な出力である。

0235 はその二層を直接つなぐ convenience bridge である。

これにより downstream は

```lean
signedSquareGoldenExceptionalPacket_of_powerSplit s
```

を自分で明示的に作ってから 0234 に渡す必要がなく、

```lean
signedGoldenRamifierStrippedPacket_of_powerSplit s
```

だけで stripping 後の packet を取得できる。

数学的な新情報はないが、証明塔の層構造としては重要である。five-adic exact split を入力とする consumer が、途中の square-coordinate representation を意識せずに golden-order の stripped state へ進めるからである。

さらに次の 0236 は signed normal form から本 0235 を経由して stripped packet を直接得る。したがって 0235 は

$$
\text{power split 層}
\longrightarrow
\text{ramifier-stripped 層}
$$

の公開変換 API であり、0236 はその一段上の normal-form 層からの入口になる。

## 直接依存する定義・補題

直接依存は次の通りである。

- `SignedFiveAdicPowerSplit`
- `SignedSquareGoldenExceptionalPacket`
- `SignedGoldenRamifierStrippedPacket`
- `signedSquareGoldenExceptionalPacket_of_powerSplit`
- 0234 `signedGoldenRamifierStrippedPacket_of_exceptional`

本宣言の本体には tactic proof は存在しない。

概念的には単純な関数合成

$$
P(s)
=
R(E(s))
$$

であり、ここで

- $E$ は `signedSquareGoldenExceptionalPacket_of_powerSplit`
- $R$ は `signedGoldenRamifierStrippedPacket_of_exceptional`

である。

重い算術、five-adic valuation、黄金ノルム、ramifier stripping の証明はすべて上流で完了している。

## 構築の流れ

定義は二段の関数適用だけである。

```lean
signedGoldenRamifierStrippedPacket_of_exceptional
  (signedSquareGoldenExceptionalPacket_of_powerSplit s)
```

1. `s : SignedFiveAdicPowerSplit u v w` を受け取る。
2. `signedSquareGoldenExceptionalPacket_of_powerSplit s` により、`SignedSquareGoldenExceptionalPacket u v w` を得る。
3. その packet を 0234 に渡す。
4. `SignedGoldenRamifierStrippedPacket u v w` を返す。

中間 object は式の中に埋め込まれており、`let` や局所 proof は不要である。

## Lean 固有の処理

宣言には `noncomputable` が付いている。

本体には `Classical.choice` が直接書かれていないが、呼び出している二つの上流変換は classical choice を含む `noncomputable def` である。そのため、この合成関数も計算可能な executable witness extractor としてではなく、証明用 data API として扱われる。

重要なのは、`noncomputable` は「証明が曖昧」という意味ではないことである。戻り値の型 `SignedGoldenRamifierStrippedPacket` が要求する全 certificate は Lean の kernel によって検査されている。ただし存在証明からどの inhabitant を選ぶかを計算手続きとして指定してはいない。

また型変数 `{u v w : ℕ}` は implicit であり、入力 `s` の型から推論される。そのため consumer 側では通常、`u v w` を明示する必要はない。

## 冗長・重複箇所

本定義は数学的には完全な wrapper である。次の式を downstream に直接書いても同じ object が得られる。

```lean
signedGoldenRamifierStrippedPacket_of_exceptional
  (signedSquareGoldenExceptionalPacket_of_powerSplit s)
```

したがって論理的な表現力は増えていない。

しかし API 上の重複には明確な意味がある。

- intermediate representation を consumer から隠せる。
- proof tower の各層に直接入口を用意できる。
- downstream が module 内部の変換順序へ依存しすぎない。
- theorem 名から「power split から stripped packet へ進む」意図が読み取れる。
- 将来 intermediate square-golden representation が変更されても、公開関数の表面を保てる可能性がある。

このため、コード行数だけを削減する目的で wrapper を消すと、層間 API の可読性を損なう可能性がある。

## 最適化候補

1. **現行の staged wrapper を維持する**
   - 最も読みやすく、証明塔の各 abstraction boundary が明確である。

2. **0236 へ直接 inline する**
   - 次の normal-form bridge からこの一行を消せるが、power-split 層から直接 stripped packet を得る公開 API が失われる。

3. **generic composition helper を使う**
   - 技術的には関数合成として書けるが、この程度の domain-specific 変換では theorem 名による意味付けの方が価値が高い。

4. **choice を避けた explicit constructor chain にする**
   - 上流の `Nonempty + Classical.choice` 設計全体を explicit data construction に変えれば computable 化できる可能性がある。ただし局所的な 0235 だけを変更しても効果はない。

5. **変換 graph を API として整理する**
   - `normalForm → fiveAdic → powerSplit → squareGolden → stripped` の各 canonical conversion を同じ naming convention で統一すると、長い proof tower の追跡性がさらに上がる。

現行定義は一行であり、局所的な proof 最適化余地はほとんどない。最適化の焦点は API topology の整理である。

## 必要 Mathlib import と import 最適化候補

本宣言自身は tactic を使わず、直接必要なのは上流型・変換定義と `noncomputable` declaration machinery だけである。

実質的な依存は project 内の次の層にある。

- signed five-adic power split
- signed square-golden exceptional packet
- ramifier-stripped packet

本宣言単独のために `Mathlib` 全体を import する必要はないと考えられる。

ただし同じ `SignedGoldenRamifierStripped.lean` module 内では、上流の packet construction が `nlinarith`、`omega`、`ring`、`norm_num`、整数整除、素数、cast などを利用する。そのため実際の最小 import 集合は module 全体で検証する必要がある。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。ただし数学 theorem の強さではなく API architecture の比較になる。

比較候補は次の通り。

- A: 現行の staged named wrapper
- B: downstream で二変換を毎回 inline
- C: explicit constructor を使った computable chain
- D: generic composition helper / canonical conversion framework

比較軸は、

- downstream code の長さ
- abstraction boundary の明瞭さ
- intermediate representation への結合度
- refactoring 耐性
- `noncomputable` dependency の範囲
- source を依存順に読んだときの追跡しやすさ

である。

特に A と B は、Lean の長い形式化で一行 wrapper が「不要な冗長性」なのか「有用な semantic API」なのかを測る小さな Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` generated section である。

正本 source では 0234 の直後に本宣言があり、その次に `signedGoldenRamifierStrippedPacket_of_normalForm` が続く。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、この一行の API bridge に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0236 `signedGoldenRamifierStrippedPacket_of_normalForm`** である。

```lean
/-- Chosen ramifier-stripped packet directly from a signed normal form. -/
noncomputable def signedGoldenRamifierStrippedPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedGoldenRamifierStrippedPacket u v w :=
  signedGoldenRamifierStrippedPacket_of_powerSplit
    (signedFiveAdicPowerSplit_of_normalForm hNF)
```

0235 が exact power split から stripped packet への入口を与えたので、0236 はさらに一段上の signed normal form から power split を構成し、そのまま 0235 へ流す。これで signed routing から ramifier stripping までの canonical conversion chain が完成する。