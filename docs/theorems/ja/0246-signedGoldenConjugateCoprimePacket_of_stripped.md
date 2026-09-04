# 0246 — `signedGoldenConjugateCoprimePacket_of_stripped`

## Lean の型

```lean
/-- Construct the conjugate-coprime packet without any choice. -/
def signedGoldenConjugateCoprimePacket_of_stripped
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    SignedGoldenConjugateCoprimePacket u v w :=
  ⟨p, p.beta_relPrime_conj⟩
```

これは `theorem` ではなく `def` である。0231 で構築された `SignedGoldenRamifierStrippedPacket` に、0244 で証明済みの `beta` とその共役の相対素性を付加し、0245 `SignedGoldenConjugateCoprimePacket` の値を構成する。

## 数学的主張・宣言の意味

入力 `p` は、可視 ramifier `tau` を一度取り除いた黄金整数 `beta` を保持し、概念的には

$$
\alpha=\tau\beta,
$$

$$
N(\beta)=b^5,
$$

$$
5\nmid N(\beta),
\qquad
\tau\nmid\beta
$$

といった certificate を持つ stripped state である。

0244 ではさらに

$$
\operatorname{GoldenRelPrime}(\beta,\overline{\beta})
$$

すなわち `beta` と `goldenConj beta` の任意の共通因子が `GoldenUnit` であることが証明された。

本定義は、その既知の事実を

```lean
SignedGoldenConjugateCoprimePacket
```

の `relPrime` field に収納する。したがって新しい数論的主張を導くのではなく、

$$
\text{ramifier-stripped state}
\longrightarrow
\text{conjugate-coprime certified state}
$$

という証明状態の昇格を型として実現する canonical producer である。

## 証明全体での役割

FLT5 の exceptional branch では、`beta` のノルムが第五冪

$$
N(\beta)=b^5
$$

であるだけでは、`beta` 自身が unit を除いて第五冪であることは直ちには従わない。そこで `beta` とその共役が相対素であることを確立し、Euclidean-domain / gcd / factor-splitting の一般論を適用できる状態へ進める必要がある。

0241–0244 はこのための arithmetic block である。

- 0241: `beta - conj beta` を `sqrtFive` 方向へ分離する。
- 0242: その差のノルムを `-5 * snd^2` と計算する。
- 0243: stripped packet 固有の値を代入し、exact five-adic mass を得る。
- 0244: 共通因子のノルムを二つの互いに素な整数量へ拘束し、共通因子が unit であることを示す。
- 0245: stripped packet と relative-primality certificate を一つの structure に束ねる。
- 0246 本定義: 任意の stripped packet を、その certified structure へ標準的に昇格させる。

このため downstream の fifth-power extraction 側は、0244 の長い整数整除論証を再実行せず、`SignedGoldenConjugateCoprimePacket` を入力として「相対素性はすでに確立済み」という前提から開始できる。

## 直接依存する定義・補題

直接依存は次の三つである。

- 0231 `SignedGoldenRamifierStrippedPacket`
- 0244 `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj`
- 0245 `SignedGoldenConjugateCoprimePacket`

0245 の structure は概念的に

```lean
structure SignedGoldenConjugateCoprimePacket (u v w : ℕ) : Type where
  stripped : SignedGoldenRamifierStrippedPacket u v w
  relPrime : GoldenRelPrime stripped.beta (goldenConj stripped.beta)
```

である。

したがって本定義の構築は

$$
p
\mapsto
\bigl(p,\;p.\mathrm{beta\_relPrime\_conj}\bigr)
$$

という二成分だけで完了する。

`GoldenRelPrime`、`GoldenUnit`、`goldenConj`、`beta` のノルム等は target structure や 0244 の内部に現れるが、本定義自身はそれらを再証明・再計算しない。

## 構築の流れ

本体は一行だけである。

```lean
⟨p, p.beta_relPrime_conj⟩
```

1. 第一 field `stripped` に入力 `p` をそのまま置く。
2. 第二 field `relPrime` には 0244 の theorem を dot notation で適用した `p.beta_relPrime_conj` を置く。
3. これで `SignedGoldenConjugateCoprimePacket u v w` の全 field が埋まる。

数学的には証明内容の追加はなく、「既に証明された invariant を data に添付する」工程である。

## Lean 固有の処理

### 1. dependent field の構築

`SignedGoldenConjugateCoprimePacket` の第二 field は

```lean
relPrime : GoldenRelPrime stripped.beta (goldenConj stripped.beta)
```

と第一 field `stripped` に依存している。

constructor literal

```lean
⟨p, p.beta_relPrime_conj⟩
```

では Lean が第一 field を `p` と確定した後、第二 field の期待型を

```lean
GoldenRelPrime p.beta (goldenConj p.beta)
```

へ具体化する。その型に 0244 の theorem がそのまま一致する。

### 2. dot notation

```lean
p.beta_relPrime_conj
```

は namespaced theorem

```lean
SignedGoldenRamifierStrippedPacket.beta_relPrime_conj p
```

の dot notation である。structure field ではないが、第一引数の型から namespace theorem を method のように記述できる。

### 3. choice を使わない `def`

コメントに `without any choice` とある通り、本定義は 0234 のような `Classical.choice` を使わない。入力 packet `p` が既に具体的に与えられており、0244 の proof term も決定済みなので、通常の computable `def` として構成できる。

これは 0234 や 0236 の `noncomputable` boundary とは性格が異なる重要な点である。

## 冗長・重複箇所

論理的には 0244 により **すべての** `SignedGoldenRamifierStrippedPacket` が conjugate-coprime であることが分かっている。そのため 0245 の structure に `relPrime` field を追加しても、元の `p` から常に再構成できるという意味では新しい情報量は増えていない。

したがって downstream が必要なとき毎回

```lean
p.beta_relPrime_conj
```

を使えば、本定義も 0245 の packet layer も理論上は省略可能である。

しかし証明設計上は次の価値がある。

- proof phase を型名で明示できる。
- downstream が 0244 の theorem 名を知る必要がない。
- 「stripped まで済んだ状態」と「conjugate coprime まで済んだ状態」を API 上で区別できる。
- fifth-power factor extraction の入力 contract を狭く明確にできる。
- 将来、相対素性の証明方法が変更されても packet consumer を保ちやすい。

ゆえに数学情報としては冗長でも、proof-state architecture と監査性のための意図的な冗長性と評価できる。

## 最適化候補

1. **named-field constructor にする**

```lean
{ stripped := p
  relPrime := p.beta_relPrime_conj }
```

一行 constructor より field の意味が可視化される。field が増えた場合にも頑健である。

2. **0245 の certified packet を廃止する**

すべての stripped packet について 0244 が自動的に使えるため、downstream が `SignedGoldenRamifierStrippedPacket` を直接受け取る設計も可能である。API 層は減るが phase boundary は弱くなる。

3. **Subtype として表す**

概念的には

```lean
{ p : SignedGoldenRamifierStrippedPacket u v w //
  GoldenRelPrime p.beta (goldenConj p.beta) }
```

のような subtype でも certified state を表せる。ただし named fields を持つ structure の方が downstream の可読性は高い可能性がある。

4. **smart constructor を現行どおり維持する**

0245 を型定義、0246 を canonical producer と分離する現行方式は、construction policy を一箇所に固定できる点でよく整理されている。局所的な短縮の優先度は低い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本定義自身は tactic を一切使わず、必要なのは既存の project-local declarations と Lean の structure construction だけである。

直接の表面依存は実質的に、

- `SignedGoldenRamifierStrippedPacket`
- `SignedGoldenConjugateCoprimePacket`
- `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj`

である。

したがって本宣言単独のために `Mathlib` 全体を import する必要はない可能性が高い。ただし `SignedGoldenConjugateCoprime.lean` module 全体では整数整除、ノルム、共役、相対素性の証明で多くの Mathlib API を使用するため、実際の最小 import は module 単位で測る必要がある。

今回は Lean build を行わないため、最小 import 集合は未検証であり、最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。数学 theorem そのものではなく、proof-state packaging の設計比較として明瞭である。

比較候補は次の通り。

- A: 現行 `structure` + canonical producer `def`
- B: stripped packet を直接使い、0244 theorem を on-demand で呼ぶ
- C: subtype に relative-primality proof を保持する
- D: named-field smart constructor を使う現行 structure

比較軸は、

- downstream proof の行数
- invariant が型に現れる明瞭さ
- elaboration の単純さ
- theorem 名への結合度
- refactor 耐性
- packet / wrapper 層のコード量
- proof auditing のしやすさ

である。

特に A と B の比較は、「論理的には導出可能な certificate をあえて型に保持する価値」を測るよい Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` generated section である。

source では 0245 の structure の直後に、本宣言が次の形で置かれている。

```lean
/-- Construct the conjugate-coprime packet without any choice. -/
def signedGoldenConjugateCoprimePacket_of_stripped
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    SignedGoldenConjugateCoprimePacket u v w :=
  ⟨p, p.beta_relPrime_conj⟩
```

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし、この一行の architectural constructor に対応する具体的ページ・節番号は今回特定していないため推測しない。数学的根拠の中心は Lean source と、その上流 0244 の相対素性 theorem である。

## 次に読むべき宣言

依存順の次は **0247 `signedGoldenConjugateCoprimePacket_of_normalForm`** である。

```lean
/-- Chosen conjugate-coprime packet directly from a signed normal form. -/
noncomputable def signedGoldenConjugateCoprimePacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedGoldenConjugateCoprimePacket u v w :=
  signedGoldenConjugateCoprimePacket_of_stripped
    (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

0246 が stripped packet から certified conjugate-coprime packet への canonical producer を与えたので、0247 はさらに上流の `SignedBranchANormalForm` から stripped packet 生成と 0246 を合成し、中間状態を意識せず certified state まで進める facade になる。