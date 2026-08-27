# 0247 — `signedGoldenConjugateCoprimePacket_of_normalForm`

## Lean の型

```lean
/-- Chosen conjugate-coprime packet directly from a signed normal form. -/
noncomputable def signedGoldenConjugateCoprimePacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedGoldenConjugateCoprimePacket u v w :=
  signedGoldenConjugateCoprimePacket_of_stripped
    (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

これは `theorem` ではなく `noncomputable def` である。入力された `SignedBranchANormalForm` から ramifier-stripped packet を構成し、さらに 0246 の canonical producer を通して conjugate-coprime certificate 付き packet を返す facade である。

## 数学的主張・宣言の意味

この宣言自身は新しい数論的命題を証明しない。既に構築済みの二つの変換

$$
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedGoldenRamifierStrippedPacket}
$$

と

$$
\mathrm{SignedGoldenRamifierStrippedPacket}
\longrightarrow
\mathrm{SignedGoldenConjugateCoprimePacket}
$$

を合成して、

$$
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedGoldenConjugateCoprimePacket}
$$

という直接入口を与える。

返される packet は stripped state の `beta` を保持し、その `beta` について

$$
\alpha=\tau\beta,
$$

$$
N(\beta)=b^5,
$$

$$
5\nmid N(\beta),
\qquad
\tau\nmid\beta,
$$

さらに

$$
\operatorname{GoldenRelPrime}(\beta,\overline{\beta})
$$

という certificate を持つ。したがって normal form から downstream の fifth-power factor extraction が必要とする certified state までを、一つの関数呼び出しで到達可能にする宣言である。

## 証明全体での役割

FLT5 exceptional branch の signed pipeline では、normal form から段階的に five-adic split、黄金整数への移送、ramifier `tau` の除去、共役との相対素性証明へ進む。

0236 ではすでに

```lean
signedGoldenRamifierStrippedPacket_of_normalForm
```

によって normal form から stripped packet へ直接進める facade が用意された。0244 で `beta` とその共役の相対素性が証明され、0245 でその証明を保持する `SignedGoldenConjugateCoprimePacket` が定義され、0246 が任意の stripped packet をその certified packet へ昇格させた。

0247 はそれらを合成し、上流 consumer が中間 packet を手動で扱わずに済むようにする。

概念的には

$$
\text{normal form}
\longrightarrow
\text{ramifier stripped}
\longrightarrow
\text{conjugate coprime certified}
$$

という proof-state pipeline の facade である。

この層があることで downstream の fifth-power decomposition や contradiction core は、normal form から開始する場合でも、途中の構築順序や theorem 名を意識せず certified packet を得られる。

## 直接依存する定義・補題

直接依存は次の通りである。

- `SignedBranchANormalForm`
- 0236 `signedGoldenRamifierStrippedPacket_of_normalForm`
- 0245 `SignedGoldenConjugateCoprimePacket`
- 0246 `signedGoldenConjugateCoprimePacket_of_stripped`

本体は実質的に

```lean
signedGoldenConjugateCoprimePacket_of_stripped
  (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

という関数合成だけである。

0244 `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj` は 0246 の内部で certificate を供給するため、0247 からは間接依存となる。

## 構築の流れ

構築は二段階である。

1. `hNF : SignedBranchANormalForm u v w` を

```lean
signedGoldenRamifierStrippedPacket_of_normalForm hNF
```

へ渡し、`SignedGoldenRamifierStrippedPacket u v w` を得る。

2. その stripped packet を

```lean
signedGoldenConjugateCoprimePacket_of_stripped
```

へ渡し、`SignedGoldenConjugateCoprimePacket u v w` を得る。

数論計算、rewrite、tactic proof は一切ない。上流で既に証明済みの構築を関数合成しているだけである。

## Lean 固有の処理

### 1. `noncomputable def`

0246 自体は choice を必要としない通常の `def` だったが、本宣言は `noncomputable def` である。理由は第一段階の

```lean
signedGoldenRamifierStrippedPacket_of_normalForm
```

が、その内部で `Classical.choice` に由来する stripped packet を利用するためである。

つまり noncomputability は 0247 で新たに発生したのではなく、上流の packet 選択境界から伝播している。

### 2. 暗黙引数の推論

`u v w` は implicit arguments である。`hNF` の型から Lean がそれらを推論し、二つの producer の型パラメータを自動的に一致させる。

### 3. theorem proof ではなく値の定義

返り値は `Prop` ではなく `SignedGoldenConjugateCoprimePacket u v w : Type` の inhabitant である。したがって `by` proof ではなく、既存関数の合成式そのものを定義本体として書いている。

## 冗長・重複箇所

論理的には本宣言は完全に composition wrapper であり、consumer は毎回

```lean
signedGoldenConjugateCoprimePacket_of_stripped
  (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

と直接書けば同じ結果を得られる。

その意味では情報量の追加はない。しかし facade としては次の利点がある。

- normal-form consumer から中間 stripped packet を隠せる。
- proof pipeline の intended path が theorem 名に残る。
- downstream が 0236 と 0246 の両方を知る必要がない。
- 将来中間 representation が変更されても、normal-form 入口を安定させやすい。
- higher-level contradiction core の依存を狭く保てる。

したがって API-level redundancy としては妥当である。

## 最適化候補

1. **現行 facade を維持する**
   - 最も読みやすく、consumer-facing API として安定している。

2. **関数合成 helper を共通化する**
   - この種の `*_of_normalForm` bridge が多数あるなら、変換 pipeline を namespace / helper で整理する余地がある。

3. **choice 境界をより上流へ集約する**
   - `noncomputable` が複数 facade に伝播している場合、canonical packet constructor を一箇所に集約すると noncomputability の由来が追いやすくなる。

4. **中間 packet facade を削減する**
   - API 層を減らすなら 0236 と 0246 の直接合成を consumer 側へ任せられる。ただし監査性と phase boundary は弱くなる。

現状の一行定義はすでに局所最適に近く、主な最適化対象は proof architecture の整理である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本宣言自身は Mathlib tactic や一般 theorem を直接利用せず、project-local declarations の関数合成だけである。

直接必要なのは実質的に、

- `SignedBranchANormalForm`
- `SignedGoldenRamifierStrippedPacket`
- `SignedGoldenConjugateCoprimePacket`
- 上記二つの producer definitions

である。

ただしそれらの upstream module は整数整除、黄金整数ノルム、Euclidean-domain、相対素性など広い Mathlib API に依存するため、module 全体の最小 import は本宣言単独では判断できない。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。ただし theorem proving の比較ではなく API / pipeline design の比較になる。

比較候補は次の通り。

- A: 現行の named facade
- B: consumer 側で 0236 と 0246 を直接合成
- C: normal-form から certified packet までを一つの大きな constructor で構築
- D: conversion pipeline を generic helper / composition layer として整理

比較軸は、

- consumer code の短さ
- 中間 representation への結合度
- noncomputable boundary の見通し
- refactor 耐性
- theorem / definition discovery のしやすさ
- proof-state phase が型名に現れる明瞭さ

である。

特に A と B の比較は、小さな facade が長い形式化でどれだけ認知負荷を下げるかを見るよい Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` generated section である。

正本 source では 0246 の直後に本宣言が次の形で置かれている。

```lean
/-- Chosen conjugate-coprime packet directly from a signed normal form. -/
noncomputable def signedGoldenConjugateCoprimePacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedGoldenConjugateCoprimePacket u v w :=
  signedGoldenConjugateCoprimePacket_of_stripped
    (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし、この architectural facade に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0248 `SignedGoldenConjugateCoprimeCore`** である。

```lean
/-- Receiver contract for contradictions on packets carrying certified conjugate
relative primality. -/
abbrev SignedGoldenConjugateCoprimeCore : Prop :=
  ∀ {u v w : ℕ}, SignedGoldenConjugateCoprimePacket u v w → False
```

0247 までで normal form から conjugate-coprime certified packet までの producer 側が完成する。0248 では、その packet を受け取って `False` を返す contradiction receiver contract を型として切り出し、producer pipeline と contradiction core を接続する段階へ進む。