# 0040 — `BranchBNoLiftEscape`

## 1. 宣言

```lean
/-- Unbundled no-lift escape data for every Branch-B counterexample candidate. -/
abbrev BranchBNoLiftEscape : Prop :=
  ∀ {x y z : ℕ},
    CounterexamplePack x y z →
    ¬ 5 ∣ z - y →
    ∃ q : ℕ,
      Nat.Prime q ∧
      q ∣ GN5 (z - y) y ∧
      ¬ q ∣ z - y ∧
      ¬ q ^ 2 ∣ GN5 (z - y) y
```

> 注記：上の型は、直前の記事、目録の依存順、後続 adapter の名称、およびリポジトリ内資料が述べる bundled / unbundled 対応から復元した。GitHub コード検索が一時的に 502 を返したため、個別ソース行の再取得だけはこの回に完了できなかった。したがって、連言の結合順やコメント文言は監査対象である一方、数学的内容と API の役割は確認できている。

## 2. Lean の型

`BranchBNoLiftEscape` は `Prop` の略称である。任意の自然数 `x y z` に対し、

- `CounterexamplePack x y z`
- Branch B 条件 `¬ 5 ∣ z - y`

を受け取り、ある自然数 `q` と、次の四条件を返す。

```lean
Nat.Prime q
q ∣ GN5 (z - y) y
¬ q ∣ z - y
¬ q ^ 2 ∣ GN5 (z - y) y
```

前号の `BranchBCleanGN5ChannelProvider` が四条件を `CleanGN5Channel` に束ねて返したのに対し、本宣言は同じ情報を連言のまま返す。

## 3. 数学的主張

原始的な正の Fermat 反例候補

$$
x^5+y^5=z^5
$$

が Branch B、

$$
5\nmid z-y
$$

に属するなら、ある素数 $q$ が存在して、

$$
q\mid GN5(z-y,y),
$$

$$
q\nmid z-y,
$$

$$
q^2\nmid GN5(z-y,y)
$$

を同時に満たす、という no-lift escape 条件である。

最後の条件は $q$-進付値が少なくとも $2$ へ持ち上がらないことを表す。前二条件と合わせると、$q$ は cyclotomic 側に一度だけ現れ、gap 側には現れない clean prime channel となる。

## 4. 証明全体での役割

本宣言は、Branch B の反例候補から局所素数障害を供給する **unbundled kernel** である。

前号との関係は次の通り。

- `BranchBNoLiftEscape` は素数性と三つの整除条件を連言で返す。
- `BranchBCleanGN5ChannelProvider` は同じ四条件を `CleanGN5Channel` 構造体に再梱包して返す。
- 後続の `branchBCleanGN5ChannelProvider_of_noLiftEscape` が両者を接続する。

したがって本宣言は、数学的な no-lift 証明と、下流 API が要求する構造体形式を分離する境界である。

## 5. 直接依存する定義・補題

### 5.1 `CounterexamplePack`

正値性、原始性、Fermat 方程式を保持する入力パケットである。本宣言の型ではその内部フィールドを直接展開しない。

### 5.2 `GN5`

第五冪差の cyclotomic 因子であり、

$$
(g+y)^5-y^5=g\,GN5(g,y)
$$

を満たす。ここでは $g=z-y$ を代入する。

### 5.3 `Nat.Prime` と整除

witness `q` は自然数であり、その素数性を別の命題 `Nat.Prime q` として返す。残り三条件は自然数上の整除関係である。

### 5.4 Branch B 条件

`¬ 5 ∣ z-y` は、gap が $5$ で割れない分岐を指定する。no-lift 素数の供給はこの分岐に限定される。

## 6. 証明の流れ

`abbrev` なので宣言自身に証明本体はない。これを実装する証明は概念的に次の流れを持つ。

1. `hPack : CounterexamplePack x y z` を受け取る。
2. `hBranch : ¬ 5 ∣ z-y` を受け取る。
3. `GN5 (z-y) y` の素因子候補から `q` を選ぶ。
4. `q` の素数性を示す。
5. `q ∣ GN5 (z-y) y` を示す。
6. gap と cyclotomic 因子の互いに素性などから `¬ q ∣ z-y` を示す。
7. no-lift 議論から `¬ q^2 ∣ GN5 (z-y) y` を示す。
8. `⟨q, hPrime, hDvd, hNotGap, hNotSq⟩` の形で返す。

この宣言は 3–7 の具体的実装をまだ提供せず、その結果型を固定する。

## 7. Lean 固有の処理

### 7.1 `abbrev` の透過性

`hEscape : BranchBNoLiftEscape` は通常、

```lean
hEscape hPack hBranch
```

と直接適用できる。

### 7.2 右結合する連言

Lean の `∧` は右結合するため、返り値は概念的に、

```lean
Nat.Prime q ∧
  (q ∣ GN5 (z-y) y ∧
    (¬ q ∣ z-y ∧
      ¬ q^2 ∣ GN5 (z-y) y))
```

である。`rcases` では四証拠を一度に分解できる。

```lean
rcases hEscape hPack hBranch with
  ⟨q, hq, hqGN, hqGap, hqSq⟩
```

### 7.3 否定は関数型

`¬ q ∣ z-y` と `¬ q^2 ∣ GN5 ...` は、それぞれ整除証拠を受け取って `False` を返す関数である。

### 7.4 witness と証拠の二層

外側は `∃ q`, 内側は連言である。後続 adapter は witness を取り出し、四証拠を `CleanGN5Channel.mk` に渡す。

## 8. 冗長・重複箇所

前号 `BranchBCleanGN5ChannelProvider` と論理内容はほぼ同じである。違いは表現だけであり、

- bundled: `CleanGN5Channel ... q`
- unbundled: 四条件の連言

である。

この重複には意味がある。数学的な no-lift 証明は連言を直接返す方が構築しやすく、消費側は構造体の名前付き projection を利用する方が読みやすい。adapter を一つ置くことで、両側の都合を分離できる。

## 9. 最適化候補

### 9.1 `CleanGN5Channel` へ一本化

本宣言を削除し、最初から bundled provider だけを使う設計は可能である。ただし no-lift 証明の中で構造体構築が混ざり、数学的 kernel と API packaging の境界が曖昧になる。

### 9.2 専用構造体の導入

四条件を `BranchBNoLiftEscapeData` のような構造体へ束ねる案もある。しかしそれは `CleanGN5Channel` と実質的に重複するため、現在の unbundled 形式の方が軽量である。

### 9.3 `q^2 ∣ ...` の正規化

プロジェクト全体で `q ^ 2` と `q * q` が混在するなら、square-divisibility 補題の適用に rewrite が増える。表記を統一すると後続証明が安定する可能性がある。

これらは設計提案であり、本作業では Lean ビルドによる検証を行っていない。

## 10. 必要 Mathlib import と import 最適化候補

宣言自体が必要とする Mathlib 基盤は限定的である。

- 自然数 `ℕ`
- `Nat.Prime`
- 整除 `∣`
- 冪 `q ^ 2`
- 存在量化と連言

プロジェクト内宣言としては少なくとも次が見える必要がある。

- `CounterexamplePack`
- `GN5`

正確な個別 import 行は、GitHub コード検索の一時障害によりこの回では再取得できなかった。推測上は `CounterexamplePack` と `GN5` を公開する局所モジュールだけで足り、`Mathlib` 全体 import は縮小できる可能性がある。最小 import の確定にはモジュール単体での Lean 検証が必要だが、本作業ではビルドを行わない。

## 11. Comparator challenge 化の可否

適している。特に bundled / unbundled API の比較課題として良い。

### Challenge A — 型の再構成

自然言語仕様から `BranchBNoLiftEscape` の `Prop` 型を再構成させる。

### Challenge B — 再梱包 adapter

unbundled witness を受け取り、

```lean
∃ q, CleanGN5Channel (z-y) y q
```

へ変換する短い Lean 証明を書かせる。

### Challenge C — 連言順序の頑健性

四条件の順序を変えた型を提示し、既存 `rcases` と constructor 証明への影響を比較させる。

### Challenge D — API 設計比較

本宣言を `abbrev`、`def`、structure の三方式で設計し、透過性・可読性・再利用性を評価させる。

## 12. 根拠と推測の区別

確認済み事項：

- 0039 まで日英記事が存在し、本宣言が次の依存順として指定されていること
- 本宣言が no-lift 条件の unbundled kernel であること
- 次の adapter が `branchBCleanGN5ChannelProvider_of_noLiftEscape` であること
- 前号の bundled provider と同じ局所データを扱うこと

一時障害により再確認できなかった事項：

- 個別 Lean ソースにおける連言の厳密な括弧順
- ソースコメントの逐語的文言
- 個別モジュールの正確な import 行

数学的主張、宣言の役割、日英構成は既存記事と目録に基づく。上記三点は次回コード検索が復旧した際の監査対象とする。

## 13. 次に読むべき宣言

次は、

```lean
DkMath.FLT.Five.branchBCleanGN5ChannelProvider_of_noLiftEscape
```

を読む。

これは `BranchBNoLiftEscape` が返す witness と四つの証拠を分解し、`CleanGN5Channel` 構造体へ再梱包して `BranchBCleanGN5ChannelProvider` を構成する adapter 定理である。
