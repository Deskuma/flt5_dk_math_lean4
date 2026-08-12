# 0052 — `SignedBranchAOrientation`

## 1. Lean の宣言

```lean
/-- The two exceptional five-adic orientations of an exponent-five equation. -/
inductive SignedBranchAOrientation (u v w : ℕ) : Prop
  | differenceGap
      (five_dvd_left : 5 ∣ u)
      (five_dvd_gap : 5 ∣ w - v) :
      SignedBranchAOrientation u v w
  | sumGap
      (five_dvd_result : 5 ∣ w)
      (five_dvd_sum : 5 ∣ u + v) :
      SignedBranchAOrientation u v w
```

完全修飾名は `DkMath.FLT.Five.SignedBranchAOrientation` である。

## 2. Lean の型

```lean
SignedBranchAOrientation (u v w : ℕ) : Prop
```

これは証明データを持つ命題値の帰納型であり、二つの構成子を持つ。

```lean
SignedBranchAOrientation.differenceGap
  : 5 ∣ u → 5 ∣ w - v → SignedBranchAOrientation u v w

SignedBranchAOrientation.sumGap
  : 5 ∣ w → 5 ∣ u + v → SignedBranchAOrientation u v w
```

## 3. 数学的主張

`SignedBranchAOrientation u v w` は、指数 5 の候補を後続の共通五進降下へ送る際に、次のどちらかの方向が成立することを表す。

1. 差分型：

$$
5\mid u,
\qquad
5\mid(w-v).
$$

2. 和型：

$$
5\mid w,
\qquad
5\mid(u+v).
$$

したがって、この宣言は単一の算術等式を証明するものではなく、五進例外局面を二つの正規化された形へ分類する直和的な論理インターフェースである。

## 4. 証明全体での役割

前号までに、Branch B 条件から $5\nmid x$ を得た後、Fermat 方程式の法 5 分析によって $5\mid y$ または $5\mid z$ が導かれる。各場合は次のように本帰納型へ格納される。

```text
5 ∣ y
  → 左右交換した pack
  → 5 ∣ y かつ 5 ∣ z - x
  → differenceGap

5 ∣ z
  → 元の pack
  → 5 ∣ z かつ 5 ∣ x + y
  → sumGap
```

後続の `SignedBranchANormalForm` は `CounterexamplePack` と本 orientation を一つの構造体にまとめる。これにより、その先の five-adic・golden-order 降下は Branch B の元の非対称な入力を直接扱わず、二構成子だけを場合分けすればよい。

## 5. 直接依存する定義・補題

本宣言自体の直接依存は標準的な自然数算術だけである。

- `ℕ`
- 整除関係 `Dvd.dvd`、記法 `∣`
- 自然数加法 `u + v`
- 自然数減法 `w - v`

リポジトリ固有の既出定義や補題を宣言本体では参照しない。ただし、実際の構成子生成では前号までの次の結果が直接利用される。

- `CounterexamplePack.swap`
- `five_dvd_z_sub_x_of_fermat5_of_five_dvd_y`
- `five_dvd_x_add_y_of_fermat5_of_five_dvd_z`

## 6. 構成の流れ

帰納型なので証明スクリプトはなく、二つの構成規則が定義そのものである。

- `differenceGap` は $5\mid u$ と $5\mid(w-v)$ を受け取る。
- `sumGap` は $5\mid w$ と $5\mid(u+v)$ を受け取る。
- どちらも同じ結論 `SignedBranchAOrientation u v w` を生成する。

利用側では `cases`、`rcases`、構成子パターン、または `induction` により二方向を完全に分解できる。

## 7. Lean 固有の処理

### 7.1 `inductive ... : Prop`

`Prop` に置かれた帰納型なので、各構成子のフィールドは計算用データではなく証明証拠として使われる。後続で orientation を場合分けすると、対応する二つの整除仮定が局所コンテキストへ現れる。

### 7.2 名前付き構成子引数

`five_dvd_left`、`five_dvd_gap`、`five_dvd_result`、`five_dvd_sum` は構成子フィールド名である。これらは生成された recursor やパターン照合の可読性を高める。

### 7.3 自然数の切り詰め減算

`w - v` は整数差ではなく `Nat.sub` である。したがって `w < v` なら $w-v=0$ となる。ただし実際の `differenceGap` 経路では `CounterexamplePack` と Fermat 方程式から必要な順序が別途保証される。宣言単独では順序条件を持たないため、この点は意味論上の前提として後続正規形の `pack` 側に委ねられている。

### 7.4 排他的和ではない

この帰納型は「ちょうど一方」を主張しない。両方の整除条件が成立するなら、同じ三つ組に対して二種類の証明項を構成できる。後続で必要なのは排他性ではなく、少なくとも一つの降下入口が存在することである。

## 8. 冗長・重複箇所

論理的には次の選言で表すこともできる。

```lean
(5 ∣ u ∧ 5 ∣ w - v) ∨ (5 ∣ w ∧ 5 ∣ u + v)
```

したがって命題内容だけを見れば独自帰納型は冗長である。しかし、構成子名が `differenceGap` と `sumGap` という数学的意味を保持し、後続証明の分岐を安定した API にするため、この重複は意図的な semantic packaging と評価できる。

## 9. 最適化候補

1. 後続で構成子ごとの補題が増えるなら、各場合の射影補題や `cases` 用 simp 補題を追加する余地がある。
2. 自然数減法の意味を完全に閉じたいなら、`differenceGap` に `v ≤ w` を含める、または差を整数上で定義する設計も考えられる。ただし現在は `CounterexamplePack` が順序情報を担うため、重複仮定になる可能性が高い。
3. 単なる選言へ戻すと宣言数は減るが、後続の名前付き分岐と文書可読性を失う。現設計の方が証明アーキテクチャには適している。
4. 構成子名の `differenceGap` と `sumGap` は十分に明確であり、短縮による利益は小さい。

## 10. 必要な Mathlib import

生成済み standalone ソースは `import Mathlib` を使用している。宣言本体に必要なのは自然数、加減算、整除、帰納型の基礎だけであり、`Mathlib` 全体は過大である。

分割元 `DkMath/FLT/Five/SignedBranchA.lean` の正確な import 行は今回取得できていないため、以下は最小化候補としての推測である。

```lean
import Mathlib.Data.Nat.Basic
```

ただし同じモジュール内の後続定理は `congrArg`、剰余、`interval_cases`、`norm_num` などを使うため、ファイル単位ではより広い import が必要になる。宣言単体の最小 import とモジュール全体の最小 import は分けて監査すべきである。

## 11. Comparator challenge 化の可否

可能である。ただし「証明を完成させる」課題より、適切な表現を選ぶ設計課題に向く。

### Challenge 案

次の選言を、名前付き二構成子を持つ `Prop` の帰納型として再設計せよ。

$$
(5\mid u\land5\mid(w-v))
\lor
(5\mid w\land5\mid(u+v)).
$$

比較観点は次の通り。

- `Or` と独自帰納型の証明項の違い
- 構成子名が後続の case split に与える可読性
- 排他性を型が主張していないことの理解
- `Nat.sub` の切り詰め意味の認識

小規模で明確なため、Lean 初級から中級への API 設計 challenge として適している。

## 12. 根拠と推測の区別

宣言名、型、二つの構成子、各整除フィールド、および直後に `SignedBranchANormalForm` が置かれることは、対象ブランチの生成済み `Flt5DkMath/FLT5StandAlone.lean` で確認した。

分割元ファイルの正確な import 行と、既存 PDF におけるこの帰納型の呼称は今回直接確認できていない。import 最小化に関する記述は推測として提示した。

## 13. 次に読むべき宣言

次は次の構造体を読む。

```lean
structure SignedBranchANormalForm (u v w : ℕ) : Prop where
  pack : CounterexamplePack u v w
  orientation : SignedBranchAOrientation u v w
```

`SignedBranchANormalForm` は反例パケットと本号の二方向タグを結合し、後続の共通五進降下が受け取る正規化済み入力を定義する。