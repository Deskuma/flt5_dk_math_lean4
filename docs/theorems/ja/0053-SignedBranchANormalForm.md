# 0053 — `SignedBranchANormalForm`

## 1. Lean の宣言

```lean
/-- A primitive exponent-five candidate equipped with its signed five-adic orientation. -/
structure SignedBranchANormalForm (u v w : ℕ) : Prop where
  pack : CounterexamplePack u v w
  orientation : SignedBranchAOrientation u v w
```

完全修飾名は `DkMath.FLT.Five.SignedBranchANormalForm` である。

## 2. Lean の型

```lean
SignedBranchANormalForm (u v w : ℕ) : Prop
```

生成される構成子と射影は概ね次の型を持つ。

```lean
SignedBranchANormalForm.mk
  : CounterexamplePack u v w →
    SignedBranchAOrientation u v w →
    SignedBranchANormalForm u v w

SignedBranchANormalForm.pack
  : SignedBranchANormalForm u v w → CounterexamplePack u v w

SignedBranchANormalForm.orientation
  : SignedBranchANormalForm u v w → SignedBranchAOrientation u v w
```

## 3. 数学的主張

`SignedBranchANormalForm u v w` は、三つ組 $(u,v,w)$ が指数 5 の正の原始的候補であり、同時に signed five-adic 降下へ入るための方向付けを備えていることを表す。

`pack` フィールドは概略、

$$
u>0,\qquad v>0,\qquad w>0,
$$

$$
\gcd(u,v)=1,
$$

$$
u^5+v^5=w^5
$$

を保持する。

`orientation` フィールドは、前号の二方向のどちらかを保持する。

$$
5\mid u\ \land\ 5\mid(w-v),
$$

または

$$
5\mid w\ \land\ 5\mid(u+v).
$$

したがって本構造体は、新しい算術結論を証明するものではなく、後続の共通降下が要求する事実を一つの正規化済み入力へ梱包する。

## 4. 証明全体での役割

Branch B の初期入力は `CounterexamplePack x y z` と $5\nmid(z-y)$ である。法 5 の解析後、$5\mid y$ の場合は左右を交換して `(y,x,z)` を差分型へ送り、$5\mid z$ の場合は `(x,y,z)` を和型へ送る。

```text
Branch-B pack
    ↓ mod 5 routing
┌─────────────────────────────┐
│ differenceGap: swapped pack │
│ sumGap:        original pack│
└─────────────────────────────┘
    ↓
SignedBranchANormalForm
    ↓
common exact five-adic descent
```

この構造体によって、後続の `SignedFiveAdicPacket` 生成は Branch B の由来や左右交換の経緯を再検討せず、`pack` と `orientation` の二つだけを受け取ればよい。

## 5. 直接依存する定義・補題

宣言本体が直接依存するリポジトリ固有宣言は二つである。

- `CounterexamplePack u v w`
- `SignedBranchAOrientation u v w`

標準 Lean 側では次だけを用いる。

- 自然数型 `ℕ`
- `structure ... : Prop`
- 依存するフィールド型と自動生成される構成子・射影

証明項はなく、既存の二命題を named fields で積にした宣言である。

## 6. 構成の流れ

構造体宣言なので証明スクリプトはない。

1. `pack` に正値、原始性、Fermat 方程式を持つ `CounterexamplePack u v w` を格納する。
2. `orientation` に `differenceGap` または `sumGap` の証拠を格納する。
3. 二つのフィールドをそろえると `SignedBranchANormalForm u v w` が構成される。
4. 利用側は `hNF.pack` と `hNF.orientation`、または `rcases hNF with ⟨hPack, hOrientation⟩` で内容を取り出す。

直後の `signedBranchA_normalForm_of_branchB` は、実際にこの構造体を二つの経路から構成する最初の主要 consumer である。

## 7. Lean 固有の処理

### 7.1 `structure ... : Prop`

本構造体は `Type` ではなく `Prop` に置かれている。目的は計算データを返すことではなく、後続証明に必要な証拠をまとめることである。証明無関係性の対象となり、実行時データ構造として使う設計ではない。

### 7.2 パラメータの共有

`u v w` は構造体全体のパラメータであり、両フィールドが同じ三つ組を参照する。これにより、pack の座標と orientation の座標を取り違えた項は型検査で拒否される。

### 7.3 named-field construction

利用側では次のように構成できる。

```lean
refine ⟨hPack, ?_⟩
exact SignedBranchAOrientation.sumGap h5w h5sum
```

または、より明示的に書ける。

```lean
exact {
  pack := hPack
  orientation := hOrientation
}
```

短い二フィールド構造体なので、実装では山括弧による構成が自然である。

### 7.4 論理積との関係

命題内容だけなら次と同値である。

```lean
CounterexamplePack u v w ∧ SignedBranchAOrientation u v w
```

独自構造体を置く利点は、`pack` と `orientation` という安定した射影名、後続 API の引数型、文書上の数学的名称を得られる点にある。

## 8. 冗長・重複箇所

論理的には単なる `And` の再包装であり、証明能力を増やしてはいない。その意味では宣言は冗長である。

一方で、後続には `SignedFiveAdicPacket`、power split、square-golden packet など、多数の層が本正規形を共通入口として参照する。そこで毎回二つの引数を別々に渡すより、一つの意味名を持つ構造体に束ねる方が依存境界を安定させる。

また `CounterexamplePack` 内の方程式と orientation 内の整除条件の整合性を、この構造体自身は追加検証しない。しかし後続の構成定理が正しい証拠だけを供給するため、意図した API 境界としては十分である。

## 9. 最適化候補

1. 現状の二フィールド構造体は最小であり、宣言自体に削減余地はほぼない。
2. `abbrev` で論理積へ置き換えると宣言量は減るが、射影名と専用型名を失うため推奨しにくい。
3. 後続で常に `pack` から positivity や equation を取り出すなら、頻出射影を委譲する補助補題を追加できる。ただし API が膨らむため、実際の重複が確認されてからでよい。
4. orientation と pack の整合性をより強く型に埋め込む設計も可能だが、現在すでに同じ `u v w` を共有しており、過剰な再包装になりやすい。
5. `SignedBranchANormalForm` という名称はやや長いが、signed／Branch A／normal form の三役を正確に示すため、短縮による利益は小さい。

## 10. 必要な Mathlib import

対象ブランチの生成済み standalone ソースはファイル全体として次を使用する。

```lean
import Mathlib
```

本宣言単体では `CounterexamplePack` と `SignedBranchAOrientation` が見えていればよく、Mathlib の個別機能を新たに要求しない。分割元の依存順から考えると、概念上の最小 import は次のようなリポジトリ内モジュールである。

```lean
import DkMath.FLT.Five.Basic
import DkMath.FLT.Five.SignedBranchA
```

ただしこれは宣言単体を切り出した場合の候補である。実際には本宣言自身が `SignedBranchA.lean` に置かれているため、同一ファイルを自己 import することはできない。分割元ファイルの正確な import 行は今回の取得資料には現れていないため、最小 import の記述は推測である。

ファイル単位では、直前の合同算術や直後の routing theorem が剰余、`interval_cases`、`norm_num` などを使う。したがって import 最適化は本構造体だけでなく `SignedBranchA.lean` 全体を対象に測定すべきである。

## 11. Comparator challenge 化の可否

可能である。小規模な API 設計 challenge に向く。

### Challenge 案

次の二つの証拠を、同じ座標を共有する命題構造体として梱包せよ。

```lean
hPack : CounterexamplePack u v w
hOrientation : SignedBranchAOrientation u v w
```

要求事項は次の通り。

- 構造体を `Prop` に置く。
- フィールド名を `pack` と `orientation` にする。
- 構成子記法と named-field 記法の双方で項を構成する。
- 構造体を `rcases` で分解する。
- 単なる `And` と比較し、専用構造体の利点を説明する。

証明難度は低いが、命題構造体による semantic packaging と座標整合性を学ぶ題材として有効である。

## 12. 根拠と推測の区別

宣言名、完全な型、二つのフィールド、コメント、直後に `signedBranchA_normalForm_of_branchB` が置かれること、および後続の `SignedFiveAdicPacket` が本構造体を保持することは、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` で確認した。

既存 PDF における本構造体の叙述名と、分割元 `DkMath/FLT/Five/SignedBranchA.lean` の正確な import 行は今回直接確認できていない。import 最小化に関する記述は推測として明示した。

## 13. 次に読むべき定理

次は次の routing theorem を読む。

```lean
theorem signedBranchA_normalForm_of_branchB
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    SignedBranchANormalForm y x z ∨ SignedBranchANormalForm x y z := by
  ...
```

これは Branch B の反例候補を法 5 で分類し、差分型では左右交換した正規形、和型では元の順序の正規形を構成する。本号で定義した容器へ実際の算術証拠を流し込む最初の定理である。