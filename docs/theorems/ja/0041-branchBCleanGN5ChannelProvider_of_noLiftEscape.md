# 0041 — `branchBCleanGN5ChannelProvider_of_noLiftEscape`

## 宣言

```lean
theorem branchBCleanGN5ChannelProvider_of_noLiftEscape
    (hEscape : BranchBNoLiftEscape) :
    BranchBCleanGN5ChannelProvider := by
  intro x y z hPack hBranch
  rcases hEscape hPack hBranch with ⟨q, hqPrime, hqGN, hqGap, hqNoLift⟩
  exact ⟨q, hqPrime, hqGN, hqGap, hqNoLift⟩
```

完全修飾名は次です。

```text
DkMath.FLT.Five.branchBCleanGN5ChannelProvider_of_noLiftEscape
```

## 1. Lean の型

```lean
BranchBNoLiftEscape → BranchBCleanGN5ChannelProvider
```

展開すると、入力 `hEscape` は任意の Branch B 反例候補に対して、ある自然数 `q` と次の四事実を返します。

```lean
Nat.Prime q
q ∣ GN5 (z - y) y
¬ q ∣ z - y
¬ q ^ 2 ∣ GN5 (z - y) y
```

出力は、同じデータを `CleanGN5Channel (z-y) y q` に束ねて返す provider です。

## 2. 数学的主張

Branch B 条件

$$
5\nmid z-y
$$

の下で、no-lift escape が素数 $q$ を供給し、

$$
q\mid GN5(z-y,y),\qquad q\nmid z-y,
$$

$$
q^2\nmid GN5(z-y,y)
$$

を示せるなら、その四事実はそのまま clean channel を構成するのに十分です。

数学的内容を新しく増やす定理ではありません。連言で返された局所算術データを、名前付きフィールドを持つ構造体へ変換する同値方向の一つです。

## 3. 証明全体での役割

前号 `BranchBNoLiftEscape` は、素数性と三つの整除条件を平坦な連言として返す unbundled interface でした。一方、`counterexample_false_of_clean_GN5Channel_by_dvd` などの局所反証器は `CleanGN5Channel` を受け取ります。

本定理は両者の間に置かれる adapter です。

```text
BranchBNoLiftEscape
        ↓ 本定理
BranchBCleanGN5ChannelProvider
        ↓ provider-based refuter
Branch B contradiction
```

したがって、no-lift prime の存在証明側は構造体の詳細を意識せず連言を返せます。反証側は連言の結合順を意識せず `CleanGN5Channel` のフィールドを使えます。

## 4. 直接依存する定義・補題

### `BranchBNoLiftEscape`

任意の `CounterexamplePack x y z` と Branch B 条件から、素数 `q` と四つの局所条件を返します。

### `BranchBCleanGN5ChannelProvider`

任意の Branch B 反例候補に対して、ある `q` と `CleanGN5Channel (z-y) y q` を返します。

### `CleanGN5Channel`

次の四フィールドを持つ命題構造体です。

```lean
prime : Nat.Prime q
dvd_GN5 : q ∣ GN5 g y
not_dvd_gap : ¬ q ∣ g
noLift : ¬ q ^ 2 ∣ GN5 g y
```

本証明は算術補題を直接呼びません。依存は interface の展開と構造体構築だけです。

## 5. 証明の流れ

1. `intro x y z hPack hBranch` により provider の暗黙変数と二つの仮定を導入します。
2. `hEscape hPack hBranch` を適用し、存在する `q` と四証拠を得ます。
3. `rcases` で存在と右結合された連言を一度に分解します。
4. 同じ五要素を `⟨q, ...⟩` で再梱包し、`BranchBCleanGN5ChannelProvider` の要求する存在と `CleanGN5Channel` を構築します。

証明項はデータの順序を変えず、失わず、そのまま別の container に移します。

## 6. Lean 固有の処理

### `abbrev` の透過展開

`BranchBNoLiftEscape` と `BranchBCleanGN5ChannelProvider` はともに `abbrev ... : Prop` です。Lean は型検査時に透過的に展開するため、`unfold` は不要です。

### 暗黙量化変数への `intro`

provider の本体は `∀ {x y z : ℕ}, ...` です。波括弧で宣言された暗黙変数でも、関数を構成する証明では `intro x y z` として導入できます。

### `rcases` による存在と連言の同時分解

```lean
rcases hEscape hPack hBranch with
  ⟨q, hqPrime, hqGN, hqGap, hqNoLift⟩
```

は、`Exists` と右結合された `And` をまとめて除去します。

### 構造体の positional construction

```lean
⟨q, hqPrime, hqGN, hqGap, hqNoLift⟩
```

では最初の要素が存在 witness、残りが `CleanGN5Channel` のフィールド順です。短い一方、フィールド順の変更には弱い書き方です。

## 7. 冗長・重複箇所

証明は意図的な再梱包だけであり、数学的重複はありません。ただし入力と出力が実質的に同じ四条件を表すため、論理レベルでは強い重複があります。

この重複は API 境界として有益です。

- provider の証明者には unbundled な連言が扱いやすい。
- consumer には named field を持つ構造体が扱いやすい。
- 変換定理を一か所に置くことで、フィールド順への依存を局所化できる。

## 8. 最適化候補

### 名前付きフィールドで構築する

保守性を重視するなら、次の形がより頑健です。

```lean
  refine ⟨q, ?_⟩
  exact {
    prime := hqPrime
    dvd_GN5 := hqGN
    not_dvd_gap := hqGap
    noLift := hqNoLift
  }
```

現在の証明のほうが短く、フィールド数も少ないため、現状では妥当です。

### 一般 adapter として抽象化する

同じ bundled / unbundled 変換が複数箇所で現れるなら、`CleanGN5Channel.of_components` のような constructor lemma を設けられます。ただし現在の一回だけなら過剰抽象化です。

### 逆向き定理

監査や provider の交換可能性を明示する目的で、

```lean
BranchBCleanGN5ChannelProvider → BranchBNoLiftEscape
```

も容易に証明できます。両 interface が論理的に同値であることを定理化できますが、後続で逆向きを使わないなら必須ではありません。

## 9. 必要 Mathlib import と import 最適化候補

standalone 版は `import Mathlib` で検証される生成物です。本定理自体が使用するのは、Lean の基本論理機構、`Nat`、存在、連言、構造体構築だけです。

個別モジュール `Provider.lean` の正確な import 行は standalone 生成物では保持されません。依存構造からは、少なくとも `BranchBNoLiftEscape`、`BranchBCleanGN5ChannelProvider`、`CleanGN5Channel`、`CounterexamplePack`、`GN5` が可視となるプロジェクト内 import が必要です。

Mathlib 側の必要量は極小であり、`import Mathlib` はこの定理単体には明らかに過大です。ただしプロジェクト内モジュールの transitive import を含む正確な最小 import は、別途 import 監査と Lean ビルドで確認すべき候補です。本号ではビルドを行っていません。

## 10. Comparator challenge 化の可否

適しています。ただし数学難度ではなく、proof engineering の比較課題です。

### Challenge

次の二つの `Prop` interface 間の adapter を、展開を明示せず証明せよ。

```lean
BranchBNoLiftEscape → BranchBCleanGN5ChannelProvider
```

### 比較観点

- `rcases` で一行分解するか。
- `obtain` を段階的に使うか。
- positional constructor か named-field constructor か。
- `simpa [BranchBNoLiftEscape, BranchBCleanGN5ChannelProvider]` を使うか。
- interface のフィールド順変更に対する耐性。

短さだけなら現行証明が強く、保守性なら named-field 構築が優位です。

## 11. 推測と確認範囲

確認済み事項は、standalone Lean ソースに記録された宣言名、型、証明本体、ならびに前後の provider 層の宣言です。

個別 `Provider.lean` の import 行に関する最小化案は推測を含む設計提案であり、Lean ビルドによる確認はしていません。また、既存 PDF は proof architecture の文脈資料であり、本号の定理型と証明の最終根拠は Lean ソースです。

## 12. 次に読むべき定理

次は次の provider consumer を読むのが自然です。

```text
DkMath.FLT.Five.branchB_false_of_clean_provider_by_dvd
```

これは `BranchBCleanGN5ChannelProvider` から具体的な clean channel を取得し、既出の局所 refuter を適用して Branch B を閉じる定理です。本号が interface 変換なら、次号は変換後の provider が実際に矛盾を運ぶことを示す consumer となります。
