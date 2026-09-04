# 0079 — `signedBranchARefuter_of_fiveAdicCore`

## Lean の型

```lean
theorem signedBranchARefuter_of_fiveAdicCore
    (hCore : SignedFiveAdicCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedFiveAdicPacket_of_normalForm hNF)
```

## 数学的主張

`SignedFiveAdicCore` は、任意の exact five-adic packet を矛盾へ送る受信器である。

$$
\forall u,v,w,\quad
\mathrm{SignedFiveAdicPacket}(u,v,w)\to\bot.
$$

一方 `SignedBranchARefuter` は、任意の signed Branch-A normal form を矛盾へ送る受信器である。本定理は、normal form から 0077 `signedFiveAdicPacket_of_normalForm` により packet を一つ選び、それを `hCore` に渡すことで、packet-level の反証器から normal-form-level の反証器を構成する。

概念的には

$$
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedFiveAdicPacket}
\longrightarrow
\bot
$$

という二段の合成である。

## 証明全体での役割

本定理は five-adic packet 層と signed Branch-A 層の adapter である。0076–0077 が normal form から packet を供給し、0078 が packet を矛盾へ送る `SignedFiveAdicCore` の型を定めた。本号はその二つを接続して `SignedBranchARefuter` を得る。

直後の `branchB_false_of_fiveAdicCore` は、本定理を既存の `branchB_false_of_signedBranchARefuter` に渡すだけで Branch B を閉じる。したがって本定理は「局所的な five-adic contradiction core」を「Branch-B closure に使える refuter」へ昇格させる接続点である。

## 直接依存する定義・補題

直接依存は次の三つである。

- `SignedFiveAdicCore`
- `SignedBranchARefuter`
- `signedFiveAdicPacket_of_normalForm`

`SignedFiveAdicPacket`、`padicValNat`、`GN5`、`SumGN5`、mod 25 の諸補題は本定理からは直接参照されない。それらは 0077 が返す packet と 0078 の core contract の背後へ隠蔽されている。

## 証明の流れ

1. `hCore : SignedFiveAdicCore` を仮定する。
2. `SignedBranchARefuter` の定義を展開する形で `intro u v w hNF` とし、任意の normal form `hNF` を受け取る。
3. `signedFiveAdicPacket_of_normalForm hNF` で `SignedFiveAdicPacket u v w` を得る。
4. その packet を `hCore` に渡して `False` を得る。

証明は実質的に関数合成一回である。

## Lean 固有の処理

### `intro` による `abbrev` の展開

`SignedBranchARefuter` は命題 alias なので、Lean は目標を必要に応じて展開し、`intro u v w hNF` を受理する。adapter theorem の側では alias の詳細を書き直す必要がない。

### 暗黙引数の推論

`hCore` の型は

```lean
∀ {u v w : ℕ}, SignedFiveAdicPacket u v w → False
```

であり、`u v w` は implicit である。`signedFiveAdicPacket_of_normalForm hNF` の戻り型から Lean が三変数を推論するため、

```lean
hCore (signedFiveAdicPacket_of_normalForm hNF)
```

だけでよい。

### `noncomputable def` の利用

0077 は `Classical.choice` を使う `noncomputable def` である。本定理自身には `noncomputable` 指定は不要である。ここで必要なのは packet の計算値ではなく、その packet が持つ証明情報を `hCore` に渡して `False` を得ることだからである。

## 冗長・重複箇所

proof script 自体に冗長性はほぼない。`intro` の後に一行で core を適用しており、adapter として最小級である。

設計上は、`branchB_false_of_fiveAdicCore` が本定理を一度呼ぶだけなら、この adapter をその定理へインライン化することもできる。しかし `SignedBranchARefuter` という既存境界を維持することで、five-adic core と Branch-B routing を疎結合に保てるため、現行の独立 theorem には明確な役割がある。

## 最適化候補

第一候補は、0076 の存在証明と 0077 の classical selection を一本の直接 constructor にまとめ、`signedFiveAdicPacket_of_normalForm` を constructive に返す設計である。その場合、本定理の形は変わらないが classical choice への間接依存を除ける可能性がある。ただしこれは Lean ビルド未実施の設計案である。

第二候補は、関数合成を明示する generic adapter を作ることだが、本 theorem は既に一行で十分に透明なので、抽象化は過剰になる可能性が高い。

第三に、本定理を `[simp]` や自動化対象にする必要性は低い。これは rewrite lemma ではなく proof architecture の bridge だからである。

## 必要 Mathlib import と import 最適化候補

対象の `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用している。本定理自身が直接使うのはローカル宣言 `SignedFiveAdicCore`、`SignedBranchARefuter`、`signedFiveAdicPacket_of_normalForm` と基本的な tactic 構文だけで、Mathlib の個別数論 API を直接呼ばない。

manifest 上ではこの領域は `DkMath/FLT/Five/SignedFiveAdic.lean` に属する。従って分割版では、これら三宣言を提供するローカルモジュールと Lean の基本 tactic 環境だけで足りる可能性が高い。

ただし対象ブランチでは standalone source を最終根拠としており、分割元モジュールの正確な import graph は今回再検証していない。最小 Mathlib import は未確認である。

## 既存 PDF との関係

今回の最終根拠は対象ブランチの Lean source である。既存の日本語・英語 PDF に、この短い adapter theorem と一対一対応する具体的ページは今回特定できていない。そのため PDF 固有の説明やページ番号は推測で補っていない。

## Comparator challenge 化の可否

**適している。** ただし難しい数学証明の比較ではなく、proof architecture の比較課題として適している。

比較候補は次の通りである。

- 現行の named adapter theorem
- `branchB_false_of_fiveAdicCore` へのインライン化
- generic function-composition helper による記述
- 0076–0077 を constructive constructor に変えた上で同じ adapter を維持する方式

評価軸は、依存境界の見通し、エラーメッセージ、再利用性、classical choice への依存、コード量である。

## 次に読むべき定理

次は

```lean
theorem branchB_false_of_fiveAdicCore
    (hCore : SignedFiveAdicCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_fiveAdicCore hCore) hPack hBranch
```

である。

本号が five-adic core から signed Branch-A refuter を構成し、次号はそれを既存の Branch-B routing theorem へ渡す。これにより common five-adic core が Branch B 全体の contradiction へ到達する。