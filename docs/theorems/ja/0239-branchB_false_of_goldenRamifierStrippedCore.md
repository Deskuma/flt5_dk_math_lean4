# 0239 — `branchB_false_of_goldenRamifierStrippedCore`

## Lean の型

```lean
/-- The stripped core also closes every routed Branch-B counterexample pack. -/
theorem branchB_false_of_goldenRamifierStrippedCore
    (hCore : SignedGoldenRamifierStrippedCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_goldenRamifierStrippedCore hCore) hPack hBranch
```

これは `theorem` である。0237 `SignedGoldenRamifierStrippedCore` として与えられた stripped packet 用の矛盾 core を、0238 で `SignedBranchARefuter` へ持ち上げ、さらに既存の Branch-B routing theorem へ渡すことで、元の `CounterexamplePack` まで `False` を返す。

## 数学的主張

概念的な入力は次の三つである。

- `hCore`：任意の ramifier-stripped packet は矛盾する。
- `hPack`：FLT5 反例候補をまとめた `CounterexamplePack x y z`。
- `hBranch`：Branch-B 条件 `¬ 5 ∣ z - y`。

0238 により

$$
\mathrm{SignedGoldenRamifierStrippedCore}
\Longrightarrow
\mathrm{SignedBranchARefuter}
$$

が既に得られている。さらに上流には、signed Branch-A refuter があれば routed Branch-B candidate を矛盾へ送る theorem

$$
\mathrm{SignedBranchARefuter}
\Longrightarrow
\bigl(\mathrm{CounterexamplePack}\land \neg 5\mid(z-y)\bigr)
\Longrightarrow
\bot
$$

が存在する。

本 theorem はこの二段階を合成して、

$$
\mathrm{SignedGoldenRamifierStrippedCore}
\Longrightarrow
\bigl(\mathrm{CounterexamplePack}\land \neg 5\mid(z-y)\bigr)
\Longrightarrow
\bot
$$

を得る。

したがって新しい整数計算や黄金整数計算を行う theorem ではない。数学的内容は、既に完成した contradiction receiver を元の Branch-B 入口へ戻す **routing / lifting bridge** である。

## 証明全体での役割

`SignedGoldenRamifierStripped.lean` では、exceptional five-adic data から黄金整数

$$
\alpha=M+N\varphi
$$

を構成し、可視 ramifier

$$
\tau=2+\varphi
$$

を一度除去して

$$
\alpha=\tau\beta
$$

とする stripped state を得る。0231–0237 ではその stripped state と、そこから矛盾を返す receiver contract を構築した。

0238 はその局所 core を `SignedBranchARefuter` へ持ち上げた。本 0239 はさらに一段上へ戻り、既存の Branch-B routing layer と接続する。

全体像は

$$
\text{Branch-B counterexample}
\longrightarrow
\text{signed Branch-A normal form}
\longrightarrow
\text{ramifier-stripped packet}
\longrightarrow
\bot
$$

であり、本 theorem はこの pipeline の最上流側の adapter である。

この分離により、下流の黄金整数 arithmetic は `CounterexamplePack` や Branch-B の詳細を知る必要がなく、上流 routing 側も `beta`、`tau`、ノルム、共役などの詳細を知らずに済む。

## 直接依存する定義・補題

直接依存する named theorem / contract は次の三つである。

- 0237 `SignedGoldenRamifierStrippedCore`
- 0238 `signedBranchARefuter_of_goldenRamifierStrippedCore`
- `branchB_false_of_signedBranchARefuter`

さらに statement 上で

- `CounterexamplePack`
- Branch-B 条件 `¬ 5 ∣ z - y`

を使用する。

直接の依存関係は

$$
hCore
\xrightarrow{\text{0238}}
\mathrm{SignedBranchARefuter}
\xrightarrow{\text{branchB routing}}
\bot
$$

である。

## 証明の流れ

proof は一つの `exact` だけである。

```lean
by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_goldenRamifierStrippedCore hCore) hPack hBranch
```

1. `hCore` を 0238 に渡し、`SignedBranchARefuter` を得る。
2. その refuter と `hPack`、`hBranch` を `branchB_false_of_signedBranchARefuter` に渡す。
3. 戻り値が `False` なので goal が閉じる。

証明中に `intro`、`rw`、`simp`、`ring`、`omega` などは一切使わない。既存 theorem の関数合成だけで閉じる。

## Lean 固有の処理

Lean では theorem も関数として扱えるため、

```lean
signedBranchARefuter_of_goldenRamifierStrippedCore hCore
```

は `SignedBranchARefuter` 型の項になる。その項をそのまま

```lean
branchB_false_of_signedBranchARefuter
```

の第一引数へ渡している。

`{x y z : ℕ}` は implicit binder なので、`hPack : CounterexamplePack x y z` と `hBranch` の型から elaborator が indices を推論する。

また `hBranch : ¬ 5 ∣ z - y` は Lean の precedence 上、`¬ (5 ∣ z - y)` と解釈される。ここでは Branch-B の routing condition をそのまま既存 theorem へ渡しており、本 theorem 自身は divisibility を展開しない。

## 冗長・重複箇所

論理的には本 theorem は薄い wrapper であり、downstream で直接

```lean
branchB_false_of_signedBranchARefuter
  (signedBranchARefuter_of_goldenRamifierStrippedCore hCore) hPack hBranch
```

と書けば同じ結果が得られる。

しかし named theorem を置く利点は大きい。

- stripped-core layer と Branch-B routing layer の接続点が theorem 名として可視化される。
- 上流 proof が 0238 の存在を知らずに済む。
- stripped core の内部実装が変更されても、Branch-B 側の API を保ちやすい。
- theorem museum 上でも dependency pipeline を宣言単位で追跡できる。

したがってこれは論理的重複ではあるが、architectural API redundancy として合理的である。

## 最適化候補

1. **現行 theorem を維持する**
   - dependency boundary が最も明瞭。

2. **term-style にする**

```lean
branchB_false_of_signedBranchARefuter
  (signedBranchARefuter_of_goldenRamifierStrippedCore hCore) hPack hBranch
```

   と `:=` 形式へ縮められる可能性が高い。

3. **0238 と 0239 を一般 lifting helper へ抽象化する**
   - `A → B` と `B → False` の合成として一般化できるが、一行 theorem 群では抽象化コストが上回る可能性が高い。

4. **routing theorem 群の naming pattern を統一する**
   - `..._of_<Core>` / `branchB_false_of_<Core>` の規則を一貫させると dependency graph が読みやすくなる。

局所 proof の短縮より、現在の named boundary を保つ方が価値が高い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用しているが、本 theorem 自身が直接必要とする Mathlib 機能はごく小さい。

- dependent function application
- `False`
- 自然数と divisibility notation

実質的な依存の大半は project 内の `SignedBranchARefuter`、`CounterexamplePack`、stripped-core bridge にある。

この theorem 単独なら Mathlib 全体は不要と考えられるが、実際の module は five-adic packet、黄金整数、routing layer を import しているため、最小 import は module 単位で検証すべきである。今回は Lean build を行わないため、正確な最小 import 集合は未検証である。

## Comparator challenge 化の可否

小さいが可能である。比較候補は次の三つ。

- A: 現行 `by exact ...`
- B: term-style `:= ...`
- C: generic contradiction-composition helper を利用する実装

比較軸は proof term の短さ、elaboration の安定性、dependency boundary の可視性、source audit の読みやすさ、将来 routing API が変わった際の修正範囲である。

A と B は数学的には同一で、Lean style 比較として分かりやすい。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` generated section である。

正本 source では 0238 の直後に本 theorem が置かれ、その次に 0240 `SignedGoldenFifthPowerUpToUnitCore` が続くことを確認した。

対象ブランチには日本語・英語 PDF が置かれているが、本 theorem は内部 routing bridge であり、対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0240 `SignedGoldenFifthPowerUpToUnitCore`** である。

```lean
abbrev SignedGoldenFifthPowerUpToUnitCore : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w),
    ∃ epsilon gamma : GoldenInt,
      GoldenUnit epsilon ∧
      p.beta = goldenMul epsilon (goldenPow gamma 5)
```

0239 までは contradiction receiver の routing bridge だったが、0240 では stripped packet から必要となる本質的な代数出力

$$
\beta=\varepsilon\gamma^5
$$

を contract として定義する。ここから `SignedGoldenConjugateCoprime.lean`、Euclidean-domain gcd、fifth-power factor extraction へ進む。