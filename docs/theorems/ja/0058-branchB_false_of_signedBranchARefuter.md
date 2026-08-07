# 0058 — `branchB_false_of_signedBranchARefuter`

## Lean の型

```lean
theorem branchB_false_of_signedBranchARefuter
    (hRefuter : SignedBranchARefuter)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  rcases signedBranchA_normalForm_of_branchB hPack hBranch with hDiff | hSum
  · exact hRefuter hDiff
  · exact hRefuter hSum
```

本定理は、signed Branch A の正規形をすべて排除できる契約 `SignedBranchARefuter` が与えられたなら、Branch B 条件を満たす任意の `CounterexamplePack` そのものが矛盾することを述べる。

## 数学的主張

仮定は三つである。

1. `hRefuter : SignedBranchARefuter`：任意の signed Branch A 正規形から矛盾を得られる。
2. `hPack : CounterexamplePack x y z`：`x,y,z` は正の原始的な指数 5 の Fermat 候補である。
3. `hBranch : ¬ 5 ∣ z - y`：Branch B 条件、すなわち gap `z-y` が 5 で割れない。

前号までの routing theorem により、この Branch B 候補は

$$
\operatorname{SignedBranchANormalForm}(y,x,z)
\quad\text{または}\quad
\operatorname{SignedBranchANormalForm}(x,y,z)
$$

のいずれかへ送られる。

`SignedBranchARefuter` はどちらの座標順でも正規形を `False` へ送れるので、いずれの分岐でも矛盾する。したがって

$$
\operatorname{CounterexamplePack}(x,y,z)
\land 5\nmid(z-y)
\land \operatorname{SignedBranchARefuter}
\Longrightarrow \bot
$$

となる。

## 証明全体での役割

本定理は、0056 の routing theorem と 0057 の refuter contract を合成する **closure bridge** である。

前段は Branch B の算術的事情を処理し、必要なら `x,y` を交換して共通の `SignedBranchANormalForm` に正規化する。後段はその正規形の由来を知らず、ただ `False` を返す。本定理はこの二層を接続する。

```text
CounterexamplePack x y z
       +
5 ∤ z-y
       ↓ 0056
SignedBranchANormalForm y x z
          ∨
SignedBranchANormalForm x y z
       ↓ 0057
      False
```

したがって、後続の five-adic、power-split、golden-order 各層は Branch B の場合分けを再実装する必要がない。各層は `SignedBranchARefuter` を構成すれば、本定理を介して Branch B 全体を閉じられる。

## 直接依存する定義・補題

直接依存は次の三つである。

- `SignedBranchARefuter`
- `CounterexamplePack`
- `signedBranchA_normalForm_of_branchB`

とくに証明の本体で使う producer は

```lean
signedBranchA_normalForm_of_branchB hPack hBranch
```

であり、その結果型は

```lean
SignedBranchANormalForm y x z ∨ SignedBranchANormalForm x y z
```

である。

`SignedBranchARefuter` は暗黙の `u v w` を正規形の型から推論するため、各枝では `hRefuter hDiff` / `hRefuter hSum` とだけ書けばよい。

## 証明の流れ

### 1. Branch B 候補を signed 正規形へ routing する

```lean
rcases signedBranchA_normalForm_of_branchB hPack hBranch with hDiff | hSum
```

ここで二つのケースに分解する。

- `hDiff : SignedBranchANormalForm y x z`
- `hSum : SignedBranchANormalForm x y z`

前者は difference orientation 側で、0056 内部では `CounterexamplePack.swap` を経由している。後者は sum orientation 側で、元の座標順を保つ。

### 2. difference 側を refuter へ渡す

```lean
exact hRefuter hDiff
```

`hRefuter` の暗黙引数は `hDiff` から `(u,v,w)=(y,x,z)` と推論される。

### 3. sum 側を refuter へ渡す

```lean
exact hRefuter hSum
```

こちらは `(u,v,w)=(x,y,z)` と推論される。

以上で両分岐とも目標 `False` が閉じる。

## Lean 固有の処理

### `rcases ... with hDiff | hSum`

論理和を場合分けし、各枝で正規形の証明項を直接名前付けしている。`cases` よりも結果を簡潔に取り出せる書き方である。

### 暗黙引数の推論

`SignedBranchARefuter` は

```lean
∀ {u v w : ℕ}, SignedBranchANormalForm u v w → False
```

なので、`hRefuter hDiff` と適用した時点で `hDiff` の型から `u=y, v=x, w=z` が決まる。座標を手で指定しないため、0056 で swap された枝でも型が整合性を保証する。

### `False` を直接返す closure theorem

結論は否定命題の外側をさらに包装せず、直接 `False` である。したがって consumer は

```lean
exact branchB_false_of_signedBranchARefuter hRefuter hPack hBranch
```

のように矛盾をそのまま利用できる。

## 冗長・重複箇所

証明は三行で、本質的な冗長性はほぼない。

二つの枝で

```lean
exact hRefuter ...
```

が重複しているが、これは論理和の二枝を明示することで routing の意味が見えやすくなっている。例えば次のように短くする余地はある。

```lean
rcases signedBranchA_normalForm_of_branchB hPack hBranch with h | h <;>
  exact hRefuter h
```

しかしこの圧縮は difference/sum の意味名を失わせる。定理博物館の観点では現行コードの方が読みやすい。

## 最適化候補

### 1. tactic 圧縮は可能だが推奨度は低い

上記の `<;>` による一行化でコード量は減る。ただし証明構造がすでに最小級であり、可読性を犠牲にするほどの利益はない。

### 2. generic sum eliminator による関数的記述

理論上は `Or.elim` を使って

```lean
exact Or.elim
  (signedBranchA_normalForm_of_branchB hPack hBranch)
  hRefuter
  hRefuter
```

に近い関数的記述も可能である。ただし左右の正規形は型引数が異なるため、Lean の推論状況によって注釈が必要になる可能性がある。現行の `rcases` は型の流れが明確で堅牢である。

### 3. この bridge 自体は抽象化しすぎない

`P ∨ Q` と `P → False`, `Q → False` から `False` を得る一般論へ抽象化することもできるが、ここでは `SignedBranchANormalForm` への routing が証明アーキテクチャ上の重要な境界である。固有名を持つ closure theorem として残す価値が高い。

## 必要な Mathlib import

対象ブランチの生成済み `Flt5DkMath/FLT5StandAlone.lean` は全体として

```lean
import Mathlib
```

を使用している。

本定理自身が直接使う Lean 機能は `rcases`、論理和、暗黙引数推論、関数適用であり、算術 tactic や新しい Mathlib 定理を直接呼んでいない。実質的な依存はプロジェクト内の `SignedBranchARefuter` と `signedBranchA_normalForm_of_branchB` に集中している。

元の分割モジュール `DkMath/FLT/Five/SignedBranchA.lean` の正確な import 行は今回取得した standalone artifact からは確認できないため、以下は **推測** である。import 最小化を行うなら、このモジュールで使用される前段の算術補題・tactic 全体を監査して決めるべきであり、本定理単体だけを根拠に `Mathlib` を削除できるとは断定できない。

### import 最適化候補

本定理だけなら、論理構文以外に追加 Mathlib import はほぼ不要である可能性が高い。しかし同じ `SignedBranchA.lean` には法 25 の有限分類、`norm_num`、`interval_cases` 等の依存が存在するため、モジュール単位の import 最適化は別途全宣言を対象に行う必要がある。

## Comparator challenge 化の可否

**可。難度は低〜中。**

課題としては、次の API を与える。

```lean
hRoute : A → B ∨ C
hRefuteB : B → False
hRefuteC : C → False
```

あるいは本プロジェクトの固有型をそのまま与え、Branch B 候補を `False` へ閉じる最小証明を書かせる。

比較ポイントは、

- `rcases` / `cases` / `Or.elim` の選択
- 暗黙引数を正しく利用できるか
- swap された座標順を手で再構成せず型に任せられるか
- 不要に 0056 の内部算術を再証明しないか

である。

とくに「既存 API を合成するだけで済む箇所を、下位補題まで展開して再証明しない」という proof engineering の良い Comparator challenge になる。

## 根拠と推測

`branchB_false_of_signedBranchARefuter` の宣言、完全な三行の証明本体、および `SignedBranchA.lean` の末尾に位置することは、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` で確認した。

同 artifact では、この後に `SignedFiveAdic.lean` が続き、`SignedFiveAdicSource`、`SignedFiveAdicPacket`、`SignedFiveAdicCore`、`signedBranchARefuter_of_fiveAdicCore`、`branchB_false_of_fiveAdicCore` へ発展することも確認できる。

既存の日本語・英語 PDF については、今回 GitHub 上で既知ファイル名を検索・取得しようとしたが具体的内容を確認できなかった。そのため PDF 由来の記述は追加せず、Lean ソースのみを確定根拠とした。PDF に関する具体的対応箇所は **未確認** であり、推測していない。

## 次に読むべき定理

次は、新しい five-adic 層の入口として

```lean
DkMath.FLT.Five.SumGN5
```

を読む。

これは `SignedFiveAdic.lean` の冒頭側に置かれた、sum orientation 用の正の自然数 residual である。difference orientation が既存の `GN5 (w-v) v` を使うのに対し、sum orientation では `(u+v)` を carrier とするため、対応する residual を `ℕ` 上で与える必要がある。ここから二つの signed orientation を一つの exact five-adic packet へ統合する準備が始まる。