# 0043 — `branchB_false_of_noLiftEscape_by_dvd`

## 1. 対象宣言

```lean
theorem branchB_false_of_noLiftEscape_by_dvd
    (hEscape : BranchBNoLiftEscape)
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_clean_provider_by_dvd
    (branchBCleanGN5ChannelProvider_of_noLiftEscape hEscape) hPack hBranch
```

所在は `DkMath.FLT.Five` 名前空間の `DkMath/FLT/Five/Provider.lean` である。

## 2. Lean の型

本定理は次の依存関数型を持つ。

```lean
BranchBNoLiftEscape →
  {x y z : ℕ} →
  CounterexamplePack x y z →
  (¬ 5 ∣ z - y) →
  False
```

最初の引数 `hEscape` は、すべての Branch B 反例候補に対して no-lift 素数を供給する unbundled kernel である。暗黙引数 `x y z` と反例パック `hPack`、Branch B 条件 `hBranch` を受け取ると矛盾を返す。

## 3. 数学的主張

`CounterexamplePack x y z` は、正の自然数について

$$
x^5+y^5=z^5
$$

を満たす原始的反例候補を表す。Branch B は自然数差 $z-y$ が $5$ で割れない場合、すなわち

$$
5\nmid(z-y)
$$

である。

`BranchBNoLiftEscape` は、この候補に対してある素数 $q$ を供給し、

$$
q\mid GN5(z-y,y),\qquad q\nmid(z-y),
$$

かつ

$$
q^2\nmid GN5(z-y,y)
$$

を保証する。したがって完全な第五冪差の body

$$
(z-y)\,GN5(z-y,y)=x^5
$$

における $q$ の局所指数はちょうど $1$ となり、第五冪に必要な指数の $5$ の倍数性と両立しない。本定理はその矛盾を既存の adapter と consumer の合成として得る。

## 4. 証明全体での役割

本定理は `Provider.lean` の終端に置かれ、局所的な no-lift 仮定から Branch B 全体を閉じる公開 API である。

役割分担は次の通りである。

1. `BranchBNoLiftEscape` が素数性と整除条件を連言形式で供給する。
2. `branchBCleanGN5ChannelProvider_of_noLiftEscape` がそれを `CleanGN5Channel` 構造体へ再梱包する。
3. `branchB_false_of_clean_provider_by_dvd` が clean channel を取り出し、第五冪 body と局所 no-lift を衝突させる。
4. 本定理が 2 と 3 を合成し、利用者から中間 provider を隠す。

新しい数論的事実を追加するのではなく、既に分離された供給側と消費側を結ぶ orchestration theorem である。

## 5. 直接依存する定義・補題

### 5.1 `BranchBNoLiftEscape`

Branch B 反例候補ごとに、clean channel に必要な素数性と三つの整除条件を unbundled な存在命題として返す。

### 5.2 `branchBCleanGN5ChannelProvider_of_noLiftEscape`

```lean
BranchBNoLiftEscape → BranchBCleanGN5ChannelProvider
```

という adapter であり、連言形式の局所データを `CleanGN5Channel` に束ねる。

### 5.3 `branchB_false_of_clean_provider_by_dvd`

```lean
BranchBCleanGN5ChannelProvider →
  CounterexamplePack x y z →
  (¬ 5 ∣ z - y) → False
```

という consumer であり、provider から具体的な clean channel を取り出して局所 refuter へ渡す。

### 5.4 `CounterexamplePack`

正値性、`Nat.Coprime x y`、Fermat 方程式をまとめた原始反例候補の構造体である。

## 6. 証明の流れ

証明は一つの `exact` 式で完了する。

```lean
exact branchB_false_of_clean_provider_by_dvd
  (branchBCleanGN5ChannelProvider_of_noLiftEscape hEscape) hPack hBranch
```

内側から読むと次の三段階である。

1. `hEscape` を adapter に渡し、`BranchBCleanGN5ChannelProvider` を得る。
2. その provider を consumer の第1引数に渡す。
3. 同じ `hPack` と `hBranch` を consumer に渡し、`False` を得る。

中間値を `have` で命名せず、関数合成をそのまま項として記述している。

## 7. Lean 固有の処理

### 7.1 命題を関数として合成する

Lean では証明項も通常の項であるため、adapter の返す証明を consumer の引数へ直接渡せる。本証明は Curry–Howard 対応がもっとも簡潔に現れた例である。

### 7.2 `abbrev` の透過性

`BranchBNoLiftEscape` と `BranchBCleanGN5ChannelProvider` は命題の略記である。Lean は必要に応じて透過的に展開するため、明示的な `unfold` は不要である。

### 7.3 暗黙引数の推論

`x y z` は `{x y z : ℕ}` と暗黙化されている。`hPack` と `hBranch` の型から Lean が三変数を推論する。

### 7.4 改行は適用構造を変えない

二行に分かれた `exact` は、括弧内の adapter 結果、`hPack`、`hBranch` を順に consumer へ適用する単一の項である。

## 8. 冗長・重複箇所

論理的には、本定理は既刊 0041 と 0042 の完全な合成であり、新しい中間事実を持たない。その意味では意図的な重複である。

しかし API 設計上は有用である。利用者は bundled provider の存在や `CleanGN5Channel` への再梱包を意識せず、数学的に自然な仮定 `BranchBNoLiftEscape` から直接 Branch B の反証を得られる。したがって削除候補というより façade theorem と評価すべきである。

## 9. 最適化候補

現行証明は既に最小級である。可読性を優先する代案としては次がある。

```lean
  have hProvider : BranchBCleanGN5ChannelProvider :=
    branchBCleanGN5ChannelProvider_of_noLiftEscape hEscape
  exact branchB_false_of_clean_provider_by_dvd hProvider hPack hBranch
```

これは中間 API を明示するため教育的だが、行数は増える。現行の一式証明の方が合成定理としての性格を正確に表す。

別名として `branchB_false_of_noLiftEscape` まで短縮する案も考えられるが、接尾辞 `_by_dvd` は valuation 版など別経路との区別に意味がある可能性がある。名称変更は後続宣言を確認してから判断すべきであり、ここでは提案に留める。

## 10. 必要 Mathlib import と import 最適化候補

本定理自身が直接使用するのは既存宣言の関数適用だけであり、Mathlib の個別定理や tactic を直接呼ばない。したがって単独で見れば必要なのは、次を提供するプロジェクト内モジュールである。

- `BranchBNoLiftEscape`
- `branchBCleanGN5ChannelProvider_of_noLiftEscape`
- `branchB_false_of_clean_provider_by_dvd`
- `CounterexamplePack`

実際の最小 import は `Provider.lean` の import グラフに依存する。standalone 版は集約のため `import Mathlib` を用いるが、これは本定理固有の必要条件ではない。最適化時には `Provider.lean` が直接 import する DkMath モジュールを基準に `#print axioms` と最小 import 実験で監査すべきである。今回は Lean ビルドを行っていないため、厳密な最小集合は未検証の候補である。

## 11. Comparator challenge 化の可否

適している。数論的探索ではなく、命題インターフェースの合成能力を測る短い challenge にできる。

### Challenge

次の二つだけを利用して Branch B の矛盾を証明する。

```lean
branchBCleanGN5ChannelProvider_of_noLiftEscape
branchB_false_of_clean_provider_by_dvd
```

期待される定理形は本号の宣言そのものである。比較軸は次の通り。

- 中間 `have` を使う二段証明
- 現行の一式 `exact` 証明
- `apply` と `exact` を組み合わせる tactic 証明

最短文字数だけでなく、依存関係と API 境界が読み取れるかを評価するとよい。

## 12. 根拠と推測の区別

宣言名、型、証明本体、`Provider.lean` の終端宣言であることは、リポジトリ内の生成済み standalone Lean ソースで確認した。

数学的説明は、同ソースの `BranchBNoLiftEscape`、adapter、consumer、`CleanGN5Channel`、`Body5` の定義と証明に基づく。

import の厳密な最小集合と名称短縮案は、Lean ビルドを伴う監査をしていないため最適化候補であり、確認済み事実ではない。

## 13. 次に読むべき宣言

次は `DkMath.FLT.Five.BranchACondition` を読む。

```lean
def BranchACondition (y z : ℕ) : Prop :=
  5 ∣ z - y
```

本号で Branch B の provider 層が完結する。次号からは例外側、すなわち gap が $5$ で割れる Branch A の公開インターフェースへ進む。