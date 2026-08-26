# 0238 — `signedBranchARefuter_of_goldenRamifierStrippedCore`

## Lean の型

```lean
/-- A refuter for all stripped packets closes both signed orientations. -/
theorem signedBranchARefuter_of_goldenRamifierStrippedCore
    (hCore : SignedGoldenRamifierStrippedCore) : SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

これは `theorem` である。0237 `SignedGoldenRamifierStrippedCore` として与えられた「ramifier を除去済みの packet はすべて矛盾する」という局所的な contradiction contract を、より上流の `SignedBranchARefuter` へ持ち上げる。

## 数学的主張

0237 は概念的に

$$
\forall u,v,w,\quad
\mathrm{SignedGoldenRamifierStrippedPacket}(u,v,w)
\longrightarrow \bot
$$

という命題である。一方 `SignedBranchARefuter` は

$$
\forall u,v,w,\quad
\mathrm{SignedBranchANormalForm}(u,v,w)
\longrightarrow \bot
$$

という receiver contract である。

本 theorem は、既に構築済みの写像

$$
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedGoldenRamifierStrippedPacket}
$$

を間に挟むことで、stripped packet に対する矛盾を signed Branch-A normal form 全体の矛盾へ輸送する。

したがって新しい数論等式を証明する theorem ではない。数学的内容は

$$
hNF
\longmapsto
\mathrm{signedGoldenRamifierStrippedPacket\_of\_normalForm}(hNF)
\longmapsto
\bot
$$

という contradiction pipeline の合成そのものである。

## 証明全体での役割

`SignedGoldenRamifierStripped.lean` では、exceptional five-adic packet から黄金整数

$$
\alpha=M+N\varphi
$$

を取り出し、可視な ramifier

$$
\tau=2+\varphi
$$

を一度除去して

$$
\alpha=\tau\beta
$$

とする。stripped packet はさらに

$$
N(\beta)=b^5,
$$

$$
5\nmid N(\beta),
$$

$$
\tau\nmid\beta
$$

などの certificate を保持する。

0237 は「この stripped state が来れば最終的に矛盾を返せる」という残りの算術 core を抽象化した。0238 はその core を上流の signed Branch-A normal form に戻すための adapter である。

この bridge があることで、後続の証明は stripped packet の構築手順を再展開せず、`SignedBranchARefuter` という既存の高位 API を利用できる。直後の 0239 はこの theorem をさらに `branchB_false_of_signedBranchARefuter` へ渡し、routed Branch-B candidate 全体を閉じる。

概念的な階層は

$$
\mathrm{SignedGoldenRamifierStrippedCore}
\Longrightarrow
\mathrm{SignedBranchARefuter}
\Longrightarrow
\text{Branch-B contradiction}
$$

である。

## 直接依存する定義・補題

直接依存は三つである。

- 0237 `SignedGoldenRamifierStrippedCore`
- `SignedBranchARefuter`
- `signedGoldenRamifierStrippedPacket_of_normalForm`

最後の変換は、signed normal form から five-adic power split、square-golden exceptional packet、ramifier-stripped packet へ至る既存 pipeline をまとめた `noncomputable def` である。

本 theorem 自身は `GoldenInt` の座標、ノルム、整除、Euclidean-domain theorem を直接使用しない。それらはすべて stripped packet を構成する下位層に封じ込められている。

## 証明の流れ

proof は二段だけである。

```lean
by
  intro u v w hNF
  exact hCore (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

1. `intro u v w hNF` により `SignedBranchARefuter` が要求する任意の indices と normal-form packet を受け取る。
2. `signedGoldenRamifierStrippedPacket_of_normalForm hNF` により stripped packet を得る。
3. その packet を `hCore` に渡すと `False` が得られ、goal が閉じる。

証明中に場合分け、算術 tactic、rewrite、座標計算は一切ない。0231–0237 までに構築した interface が十分強いため、ここでは純粋な関数合成だけが残っている。

## Lean 固有の処理

`SignedGoldenRamifierStrippedCore` と `SignedBranchARefuter` はいずれも `abbrev ... : Prop` である。そのため elaborator は必要に応じてそれらを透明に展開し、`intro u v w hNF` を通常の関数 introduction として処理できる。

`u v w` は定義側では implicit binder `{u v w : ℕ}` だが、tactic proof では `intro` によって局所変数として導入される。

また `signedGoldenRamifierStrippedPacket_of_normalForm` は `noncomputable def` だが、本 theorem は Prop の証明であり、その chosen packet の具体的計算値を評価する必要はない。必要なのは「その型の packet が得られる」という項だけである。

`exact hCore (...)` では Lean が `hCore` の implicit indices を、渡された stripped packet の型から推論する。

## 冗長・重複箇所

論理的には本 theorem は極めて薄い wrapper である。downstream で毎回

```lean
hCore (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

と書けば同じ結果になるため、最小主義なら named theorem を省ける。

しかし現在の開発では各 reduction layer に receiver contract と lifting theorem を置く方針が一貫している。例えば five-adic core、power-split core、square-golden core なども、局所 core から `SignedBranchARefuter` へ持ち上げる bridge を持つ。

したがって本 theorem の重複は意図的な API redundancy と見るのが自然である。これにより dependency boundary が theorem 名として可視化され、下流が packet construction の詳細に依存しなくなる。

## 最適化候補

1. **現行 theorem を維持する**
   - reduction layer の境界が最も読みやすい。

2. **term-style に短縮する**

```lean
fun hNF => hCore (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

   のような直接項へ縮められる可能性がある。正確な implicit binder の elaboration は今回 Lean build を行わないため未検証である。

3. **一般的な core-lifting helper を導入する**
   - `A → B` と `B → False` から `A → False` を作る generic helper は書けるが、この程度の一行 theorem に抽象化を追加すると、かえって証明経路が読みにくくなる可能性が高い。

4. **packet conversion pipeline を structure morphism 的に整理する**
   - normal form → five-adic → power split → exceptional → stripped の変換が増えるなら、namespace 内で naming pattern を統一する価値がある。

現状では局所 proof の短縮より、named architectural boundary を残す価値の方が高い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。しかし本 theorem 自身が必要とする機能は基本的な dependent function elaboration、`intro`、`exact` 程度であり、高度な Mathlib theorem や tactic は直接使用しない。

実際の依存はほぼプロジェクト内部の

- `SignedGoldenRamifierStrippedCore`
- `SignedBranchARefuter`
- `signedGoldenRamifierStrippedPacket_of_normalForm`

に集約される。

したがって宣言単独の import surface は非常に小さい。ただし module 全体では golden order、five-adic packet、square-golden bridge など多数の上流定義を必要とするため、最小 import は module 単位で測定すべきである。今回は Lean build を行わないため、正確な最小 import 集合は未検証である。

## Comparator challenge 化の可否

小さいが適している。比較候補は次の三つである。

- A: 現行 tactic proof `intro ...; exact ...`
- B: term-style lambda による直接合成
- C: generic contradiction-lifting helper を介する実装

比較軸は proof term の短さ、dependency boundary の可視性、elaboration の安定性、source audit の読みやすさ、将来 packet conversion が変更された際の修正範囲である。

特に A と B は数学的には完全に同じであり、Lean code style と API readability の比較として明瞭である。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` generated section である。

source では 0237 `SignedGoldenRamifierStrippedCore` の直後に本 theorem が置かれ、その次に `branchB_false_of_goldenRamifierStrippedCore` が続く。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` も存在する。ただし、本 theorem は内部 receiver bridge であり、対応する具体的 PDF ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0239 `branchB_false_of_goldenRamifierStrippedCore`** である。

```lean
theorem branchB_false_of_goldenRamifierStrippedCore
    (hCore : SignedGoldenRamifierStrippedCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_goldenRamifierStrippedCore hCore) hPack hBranch
```

0238 が stripped core を `SignedBranchARefuter` へ持ち上げたので、0239 はその refuter を既存の signed routing theorem に渡し、元の Branch-B counterexample pack まで矛盾を戻す。