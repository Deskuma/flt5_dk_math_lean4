# 0249 — `signedBranchARefuter_of_goldenConjugateCoprimeCore`

## Lean の型

```lean
theorem signedBranchARefuter_of_goldenConjugateCoprimeCore
    (hCore : SignedGoldenConjugateCoprimeCore) : SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedGoldenConjugateCoprimePacket_of_normalForm hNF)
```

これは `theorem` であり、0248 `SignedGoldenConjugateCoprimeCore` として与えられた contradiction receiver を、signed Branch-A normal form 全体を否定する `SignedBranchARefuter` へ持ち上げる。

## 数学的主張

0248 の core は、任意の `u v w : ℕ` に対して

$$
\mathrm{SignedGoldenConjugateCoprimePacket}(u,v,w)
\to \bot
$$

を与える。

一方、0247 `signedGoldenConjugateCoprimePacket_of_normalForm` は signed Branch-A normal form からその certified packet を構成する。

したがって本 theorem は、この二つを単純に合成して

$$
\mathrm{SignedBranchANormalForm}(u,v,w)
\to \bot
$$

を得る。

数論的には新しい恒等式や整除計算を証明していない。0241–0247 までで構築済みの conjugate-coprime certified state を、Branch-A の refutation interface へ接続する routing theorem である。

## 証明全体での役割

この theorem は proof pipeline の重要な phase boundary である。

上流では、signed normal form から

$$
\mathrm{SignedGoldenRamifierStrippedPacket}
$$

を構成し、`beta` と `goldenConj beta` の relative primality を証明し、0245 で

$$
\mathrm{SignedGoldenConjugateCoprimePacket}
$$

へ certificate を package した。0247 は normal form からこの packet を直接生成する facade であり、0248 はその packet から `False` を返す receiver contract である。

0249 はこの producer と receiver を結合して、上位層が要求する `SignedBranchARefuter` を得る。

したがって役割は

$$
\text{normal form producer}
+\text{conjugate-coprime contradiction core}
\longrightarrow
\text{Branch-A refuter}
$$

という interface composition にある。

直後の 0250 `branchB_false_of_goldenConjugateCoprimeCore` は、本 theorem で得た `SignedBranchARefuter` を既存の Branch-B routing theorem に渡して、元の counterexample packet まで矛盾を押し戻す。

## 直接依存する定義・補題

直接依存は次の二つである。

- 0248 `SignedGoldenConjugateCoprimeCore`
- 0247 `signedGoldenConjugateCoprimePacket_of_normalForm`

また結論の型として上流で定義済みの

- `SignedBranchARefuter`
- `SignedBranchANormalForm`

に依存する。

概念的には

$$
\mathrm{SignedBranchANormalForm}
\xrightarrow{\text{0247}}
\mathrm{SignedGoldenConjugateCoprimePacket}
\xrightarrow{\text{0248}}
\bot
$$

という二段 composition だけである。

## 証明の流れ

proof は三行で閉じる。

```lean
by
  intro u v w hNF
  exact hCore (signedGoldenConjugateCoprimePacket_of_normalForm hNF)
```

1. `SignedBranchARefuter` の関数型を展開し、`u v w` と `hNF` を受け取る。
2. `signedGoldenConjugateCoprimePacket_of_normalForm hNF` で certified packet を生成する。
3. その packet を `hCore` に渡して `False` を得る。

rewrite、算術 tactic、existential witness construction は一切ない。

## Lean 固有の処理

### `intro` による `abbrev` 展開

`SignedBranchARefuter` は proposition-level の関数型として使われるため、`intro u v w hNF` だけで必要な引数へ展開される。明示的な `unfold` は不要である。

### 暗黙 index の推論

`hCore` の型は

```lean
∀ {u v w : ℕ}, SignedGoldenConjugateCoprimePacket u v w → False
```

であり、`u v w` は暗黙引数である。0247 が返す packet の型から Lean が index を推論するため、

```lean
hCore (signedGoldenConjugateCoprimePacket_of_normalForm hNF)
```

と直接適用できる。

### `exact` による pure composition

この proof は tactic automation ではなく、型が一致する項をそのまま渡す proof term に近い。形式的には function composition の elaboration である。

## 冗長・重複箇所

0238 `signedBranchARefuter_of_goldenRamifierStrippedCore` と構造がほぼ同じである。

0238 は

$$
\mathrm{SignedGoldenRamifierStrippedCore}
\to \mathrm{SignedBranchARefuter},
$$

0249 は

$$
\mathrm{SignedGoldenConjugateCoprimeCore}
\to \mathrm{SignedBranchARefuter}
$$

を与える。違いは producer が生成する packet refinement level だけである。

論理的には generic lifting helper を作ることも可能だが、phase-specific theorem 名には証明の到達地点を可視化する価値がある。大規模 formalization の監査性を優先するなら、現行の薄い重複は意図的 API redundancy と考えられる。

## 最適化候補

1. **現行 theorem を維持する**
   - proof state の phase が theorem 名に表れ、追跡しやすい。

2. **generic refuter lift helper を導入する**
   - `producer : A → B` と `core : B → False` から `A → False` を返す generic helper へ抽象化できる。
   - ただし一行 proof の抽象化なので、かえって theorem discovery が弱くなる可能性がある。

3. **point-free 形式との比較**
   - `fun ... => hCore (...)` のような項形式へ短縮できる。
   - 現行 `intro` 形式のほうが index と normal-form hypothesis が読みやすい。

4. **core / producer naming convention の統一**
   - stripped、conjugate-coprime、fifth-power など phase が増えるなら、`*_of_*Core` と `*_Packet_of_*` の命名規則をさらに厳密化できる。

局所的にはすでにほぼ最小であり、最適化対象は proof length より architecture である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用しているが、本 theorem 自身は Mathlib の tactic や高度な theorem を直接使用しない。

必要なのは実質的に project-local な

- `SignedGoldenConjugateCoprimeCore`
- `SignedBranchARefuter`
- `signedGoldenConjugateCoprimePacket_of_normalForm`

だけである。

したがって declaration 単独の Mathlib surface は極小である。ただし module 全体では `GoldenRelPrime`、ノルム、整除、Euclidean-domain など広い依存を持つため、実際の import 最適化は module 単位で測る必要がある。

今回は Lean build を行わないため、正確な最小 import 集合は未検証である。

## Comparator challenge 化の可否

可能である。ただし tactic 性能ではなく API architecture の比較が中心になる。

候補は次の通り。

- A: 現行の phase-specific theorem
- B: generic refuter-lift helper を使う
- C: point-free / term-style で直接定義する
- D: 0248 の core alias を使わず長い関数型を theorem signature に直接書く

比較軸は、proof term の短さ、elaboration の単純さ、phase boundary の可視性、theorem discovery、refactor 耐性、consumer code の読みやすさである。

A と B の比較は、とくに「一行 bridge を抽象化する価値があるか」を測る小さな Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` generated section である。

正本 source では 0248 の直後に本 theorem があり、その直後に

```lean
theorem branchB_false_of_goldenConjugateCoprimeCore
    (hCore : SignedGoldenConjugateCoprimeCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_goldenConjugateCoprimeCore hCore) hPack hBranch
```

が続く。

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし、本 theorem に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0250 `branchB_false_of_goldenConjugateCoprimeCore`** である。

```lean
theorem branchB_false_of_goldenConjugateCoprimeCore
    (hCore : SignedGoldenConjugateCoprimeCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_goldenConjugateCoprimeCore hCore) hPack hBranch
```

0249 が conjugate-coprime core を signed Branch-A refuter へ持ち上げ、0250 はその refuter を既存の Branch-B routing theorem に渡して、元の counterexample packet まで contradiction を伝播させる。