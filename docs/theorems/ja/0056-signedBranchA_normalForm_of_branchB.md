# 0056 — `signedBranchA_normalForm_of_branchB`

## 1. Lean の宣言

```lean
/-- Every Branch-B pack is routed into one of the two signed Branch-A orientations. -/
theorem signedBranchA_normalForm_of_branchB
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    SignedBranchANormalForm y x z ∨ SignedBranchANormalForm x y z := by
  have h5x : ¬ 5 ∣ x := five_not_dvd_x_of_branchB hPack hBranch
  rcases five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x hPack.hEq h5x with
    h5y | h5z
  · left
    refine ⟨hPack.swap, ?_⟩
    exact SignedBranchAOrientation.differenceGap h5y
      (five_dvd_z_sub_x_of_fermat5_of_five_dvd_y hPack.hEq h5y)
  · right
    refine ⟨hPack, ?_⟩
    exact SignedBranchAOrientation.sumGap h5z
      (five_dvd_x_add_y_of_fermat5_of_five_dvd_z hPack.hEq h5z)
```

## 2. Lean の型

```lean
{x y z : ℕ} →
CounterexamplePack x y z →
(¬ 5 ∣ z - y) →
SignedBranchANormalForm y x z ∨
  SignedBranchANormalForm x y z
```

正の原始的 FLT5 候補 `hPack` と Branch B 条件 `5 ∤ z - y` を受け取り、座標を交換した difference-gap 正規形か、元の座標順の sum-gap 正規形のいずれかを返す。

## 3. 数学的主張

`CounterexamplePack x y z` は、とくに

$$
x^5+y^5=z^5,
\qquad
x,y,z>0,
\qquad
\gcd(x,y)=1
$$

を保持する。さらに Branch B 条件

$$
5\nmid(z-y)
$$

を仮定する。

既刊 0048 によって

$$
5\nmid x
$$

が従い、0055 によって

$$
5\mid y
\quad\text{または}\quad
5\mid z
$$

へ分岐する。

前者なら 0050 から

$$
5\mid(z-x)
$$

を得る。ここで左右を交換して $(u,v,w)=(y,x,z)$ とすれば、

$$
5\mid u,
\qquad
5\mid(w-v),
$$

すなわち `differenceGap` orientation になる。

後者なら 0051 から

$$
5\mid(x+y)
$$

を得る。元の $(u,v,w)=(x,y,z)$ のままで、

$$
5\mid w,
\qquad
5\mid(u+v),
$$

すなわち `sumGap` orientation になる。

したがって Branch B の候補は、signed five-adic 降下が受け取る二種類の正規形のどちらかへ必ず routing される。

## 4. 証明全体での役割

この定理は `SignedBranchA.lean` 前半の合流点である。これ以前の補題は、Branch B から five-adic exceptional geometry を抽出するための部品だった。

```text
CounterexamplePack x y z
       +
5 ∤ (z - y)
       ↓ 0048
     5 ∤ x
       ↓ 0055
  5 ∣ y  ∨  5 ∣ z
    ↓             ↓
  0050          0051
5 ∣ z-x       5 ∣ x+y
    ↓             ↓
 swap          keep
    ↓             ↓
differenceGap   sumGap
      \          /
       \        /
 SignedBranchANormalForm
```

ここで重要なのは、後続の five-adic 証明が Branch B の由来を直接扱わなくてよくなることである。後段は `SignedBranchANormalForm u v w` だけを入口にし、`differenceGap` と `sumGap` の二構成子を共通 API として場合分けできる。

つまり本定理は、前段の「元の反例候補の座標事情」と後段の「符号付き five-adic 降下」の間に置かれた normalization/routing bridge である。

## 5. 直接依存する定義・補題

リポジトリ固有の直接依存は次である。

- `CounterexamplePack`
- `CounterexamplePack.swap` — 0046
- `five_not_dvd_x_of_branchB` — 0048
- `five_dvd_z_sub_x_of_fermat5_of_five_dvd_y` — 0050
- `five_dvd_x_add_y_of_fermat5_of_five_dvd_z` — 0051
- `SignedBranchAOrientation` — 0052
- `SignedBranchANormalForm` — 0053
- `five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x` — 0055

Lean/Mathlib 側の直接的な構文・論理機構としては、`rcases`、`Or`、`left`、`right`、`refine`、構造体構築 `⟨..., ...⟩` を用いる。

この定理自身は新たな整数論計算をしていない。必要な算術はすべて 0048、0050、0051、0055 に分離済みであり、本体は論理的 routing と構造体再梱包に徹している。

## 6. 証明の流れ

1. `five_not_dvd_x_of_branchB hPack hBranch` により `h5x : ¬ 5 ∣ x` を得る。
2. `five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x hPack.hEq h5x` を適用し、`h5y : 5 ∣ y` または `h5z : 5 ∣ z` に場合分けする。
3. `h5y` の枝では結論の左側を選ぶ。
4. pack は `hPack.swap : CounterexamplePack y x z` へ交換する。
5. 0050 により `5 ∣ z - x` を得て、`SignedBranchAOrientation.differenceGap h5y ...` を構成する。
6. これらを組にして `SignedBranchANormalForm y x z` を完成する。
7. `h5z` の枝では結論の右側を選ぶ。
8. pack は交換せず `hPack` をそのまま使う。
9. 0051 により `5 ∣ x + y` を得て、`SignedBranchAOrientation.sumGap h5z ...` を構成する。
10. これらを組にして `SignedBranchANormalForm x y z` を完成する。

証明の算術的核心はすでに前号までに消化されており、本定理はその結果を型の形へ正規化する。

## 7. Lean 固有の処理

### 7.1 `rcases ... with h5y | h5z`

0055 の結論は選言 `5 ∣ y ∨ 5 ∣ z` であるため、`rcases` で二枝に分ける。数学上のケース分けが Lean の proof state の分岐へそのまま対応している。

### 7.2 `left` / `right`

目標自身も

```lean
SignedBranchANormalForm y x z ∨
SignedBranchANormalForm x y z
```

という選言なので、入力側のケース分けと出力側の選言選択が一対一に対応する。

### 7.3 `refine ⟨hPack.swap, ?_⟩`

`SignedBranchANormalForm` は

```lean
structure SignedBranchANormalForm (u v w : ℕ) : Prop where
  pack : CounterexamplePack u v w
  orientation : SignedBranchAOrientation u v w
```

なので、第一フィールドに交換済み pack を渡し、第二フィールドをサブゴールとして残す。`differenceGap` 枝では座標交換が必要なのは、orientation の第一座標に `5 ∣ u` を置くためである。

### 7.4 型が座標交換を検査する

`hPack.swap` を使った後の型は `CounterexamplePack y x z` である。続く `differenceGap h5y ...` の型も `SignedBranchAOrientation y x z` でなければならない。したがって「どの座標をどこへ移したか」という bookkeeping は型検査器が強制する。

これは紙の証明で起こりやすい $x,y$ の取り違えを防ぐ大きな利点である。

## 8. 冗長・重複箇所

本体は短く、明白な冗長性はほとんどない。

二枝はどちらも

```text
選言の枝を選ぶ
→ pack を供給する
→ orientation を供給する
```

という同じ形をしている。しかし差分枝だけ `swap` が必要であり、orientation の構成子も異なるため、無理に共通化すると可読性を落とす可能性が高い。

`hPack.hEq` が二つの downstream lemma へ繰り返し渡されるが、局所名を付けるほどの重複ではない。

## 9. 最適化候補

1. 現行証明は十分短く、局所最適化の優先度は低い。
2. 0050 と 0051 の「Fermat 方程式を法 5 へ落とす」共通部分を前段で抽象化すれば、この定理の直接依存はより意味論的な routing lemma だけになる可能性がある。
3. `SignedBranchAOrientation` と `SignedBranchANormalForm` を一つの inductive packet に統合する設計も可能だが、pack と orientation を分離した現在の設計の方が後続 API の再利用性は高い。
4. 本定理の結論を単一の existential package、たとえば座標 permutation を含む正規形へ変える案もある。しかし現在の二分型は後続の `rcases` に自然であり、difference/sum の数学的区別も可視化される。

したがって現状は「コード行数最小」より「降下の二入口を型に残す」ことを優先した設計と評価できる。

## 10. 必要な Mathlib import と import 最適化候補

対象ブランチの生成済み `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

ただし本定理単体は Mathlib の重い算術 tactic を直接使わず、主として基礎論理とリポジトリ内補題の合成だけである。そのため、この宣言自体が追加で要求する Mathlib import は実質的に極小である。

実際の分割元 `SignedBranchA.lean` では、前段の `Fin 25`、剰余、`norm_num`、`interval_cases`/有限決定処理なども同一モジュールに含まれるため、ファイル単位の最小 import は本定理だけからは決められない。

最適化するなら、まず `SignedBranchA.lean` を「有限剰余算術」と「routing/normal-form packaging」に分割し、後者が前者の公開補題だけを import する構造にすると import 境界が明確になる。これは実ビルドで検証していない設計候補であり、推測を含む。

## 11. Comparator challenge 化の可否

適している。とくに「数学の同値証明」より「型設計と routing の比較」に向く。

### Challenge 案

同じ Branch B 入力から signed normal form を構成する二方式を比較する。

- 解法 A: 現行どおり `5 ∣ y ∨ 5 ∣ z` を得て、`Or` の二枝で `differenceGap` / `sumGap` を構成する。
- 解法 B: `five_dvd_y_or_z...` を内包した専用 routing lemma を作り、最終定理を一行に近い構成へする。

比較項目は、依存の透明性、座標交換ミスへの耐性、エラーメッセージ、proof term の単純さ、後続 API の扱いやすさである。

もう一つの challenge は、結論を `Or` ではなく「permutation と orientation を持つ単一 existential normal form」で設計し直し、後続証明が簡潔になるかを比較することである。

## 12. 根拠と推測の区別

宣言名、完全な型、証明本体、直接呼び出している 0048・0050・0051・0055、`hPack.swap` の使用、および直後に `SignedBranchARefuter` と `branchB_false_of_signedBranchARefuter` が置かれることは、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` で確認した。

対象ブランチの既存目録では 0055 の次として本定理が指定されていたことも確認した。

既存の日本語・英語 PDF はこのリポジトリの解説資料として扱うが、今回の宣言に対応する厳密な PDF 節・ページをこの作業では抽出していない。そのため、PDF 固有の文章やページ情報を推測で補ってはいない。

Mathlib の最小 import 候補およびモジュール分割案は、削減ビルドを行っていないため設計上の推測である。

## 13. 次に読むべき宣言

直後の未解説宣言は、signed normal form をすべて反駁する後続層の契約を表す abbrev である。

```lean
abbrev SignedBranchARefuter : Prop :=
  ∀ {u v w : ℕ}, SignedBranchANormalForm u v w → False
```

その直後には、本号の routing theorem とこの refuter 契約を合成して Branch B を閉じる

```lean
theorem branchB_false_of_signedBranchARefuter
    (hRefuter : SignedBranchARefuter)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False
```

が続く。

依存順を一宣言ずつ厳密に進めるなら、次号は `SignedBranchARefuter` を読むのが自然である。