# 0075 — `SignedFiveAdicPacket`

## Lean の型

```lean
structure SignedFiveAdicPacket (u v w : ℕ) : Type where
  normal : SignedBranchANormalForm u v w
  carrier : ℕ
  residual : ℕ
  distinguished : ℕ
  source : SignedFiveAdicSource u v w carrier residual distinguished
  factor_eq : carrier * residual = distinguished ^ 5
  carrier_pos : 0 < carrier
  residual_pos : 0 < residual
  distinguished_pos : 0 < distinguished
  five_dvd_carrier : 5 ∣ carrier
  five_dvd_distinguished : 5 ∣ distinguished
  residual_mod_twentyFive : residual % 25 = 5
  residual_shape : ∃ M : ℕ, residual = 5 + 25 * M
  residual_padicValNat : padicValNat 5 residual = 1
  carrier_padicValNat_shape :
    ∃ m : ℕ, padicValNat 5 carrier = 4 + 5 * m
```

根拠は `docs/flt5-theorem-museum` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath.FLT.Five` 名前空間内の宣言である。

本号は theorem ではなく `structure ... : Type` 宣言である。しかし直前の `SignedFiveAdicSource` を受け、直後の `nonempty_signedFiveAdicPacket_of_normalForm` がこの structure の inhabitant を実際に構築するため、依存順ではここを先に読む必要がある。

## 数学的主張

`SignedFiveAdicPacket u v w` は、signed Branch A の二 orientation から共通に抽出できる five-adic 情報を一つの record にまとめた型である。

数学的には、ある三つの自然数

$$
carrier,\quad residual,\quad distinguished
$$

を選び、それらについて

$$
carrier\cdot residual=distinguished^5
$$

と、正値性

$$
carrier>0,\qquad residual>0,\qquad distinguished>0,
$$

5 に関する可除性

$$
5\mid carrier,\qquad 5\mid distinguished,
$$

residual の法 $25$ での精密な形

$$
residual\equiv5\pmod{25},
$$

したがってある $M\in\mathbb N$ が存在して

$$
residual=5+25M,
$$

さらに exact valuation

$$
v_5(residual)=1
$$

と carrier の valuation shape

$$
\exists m\in\mathbb N,\qquad v_5(carrier)=4+5m
$$

を同時に保持する。

加えて `source` フィールドにより、この共通三つ組が difference orientation 由来か sum orientation 由来かという provenance も保存する。

## 証明全体での役割

0052–0056 で signed Branch A の orientation と normal form が作られ、0059–0073 で sum residual、法 $25$、exact $5$-進付値、carrier valuation shape が順に整備された。0074 は difference/sum の出自を `SignedFiveAdicSource` として型にした。

0075 は、それらを **後段が再証明せず使える一個の five-adic API** に封入する境界である。

特に重要なのは、後続層が各 orientation の細かな剰余計算を再度開かなくてよい点である。コメントにも、packet が

- `residual ≡ 5 (mod 25)`
- `v_5(residual)=1`
- `v_5(carrier) ≡ 4 (mod 5)`

を記録し、後段で residue proof を再開しない意図が明記されている。

直後の `nonempty_signedFiveAdicPacket_of_normalForm` は `SignedBranchANormalForm u v w` から

```lean
Nonempty (SignedFiveAdicPacket u v w)
```

を構成し、difference / sum の双方をこの共通 packet へ畳み込む。

## 直接依存する定義・補題

型に直接現れる主要宣言は次の通り。

- `SignedBranchANormalForm`
- `SignedFiveAdicSource`
- `padicValNat`
- 自然数 `ℕ`
- `Nat` 上の積・冪・順序・可除性・剰余

また各フィールドの証明を構成する後続 theorem の観点では、直前までに整備された以下の補題群が実質的依存になる。

- `GN5_cast_mod25_eq_five`
- `SumGN5_cast_mod25_eq_five`
- `mod_twentyFive_eq_five_of_zmod_eq_five`
- `eq_five_add_twentyFive_mul_of_mod_eq_five`
- `five_dvd_of_eq_five_add_twentyFive_mul`
- `not_twentyFive_dvd_of_mod_eq_five`
- `padicValNat_five_eq_one_of_dvd_not_sq`
- `padicValNat_carrier_shape_of_mul_eq_fifth`

ただしこれらは `structure` の型式そのものに全て名前として現れるわけではない。packet の inhabitant を構築する際の証明依存である。

## 宣言の流れ

本宣言には tactic proof はない。各フィールドが共通 invariant の契約を順に記述する。

1. `normal` で元の `SignedBranchANormalForm u v w` を保持する。
2. `carrier`, `residual`, `distinguished` で orientation を抽象化した三つの数を保存する。
3. `source` で三つ組の difference/sum provenance を保存する。
4. `factor_eq` で五乗因数分解を共通式に固定する。
5. 三つの `_pos` フィールドで非零性を扱いやすい形で保存する。
6. `five_dvd_carrier`, `five_dvd_distinguished` で 5 の荷重を明示する。
7. `residual_mod_twentyFive` と `residual_shape` で residual が単に 5 の倍数ではなく、法 $25$ でちょうど 5 の類にあることを保存する。
8. `residual_padicValNat` で $v_5(residual)=1$ をキャッシュする。
9. `carrier_padicValNat_shape` で carrier の付値が $4\pmod5$ であることを existential witness 付きで保存する。

したがって structure 自体が「signed orientation を five-adic invariant へ正規化した結果」の仕様書になっている。

## Lean 固有の処理

### `structure ... : Type`

前号 `SignedFiveAdicSource : Prop` と異なり、本号は `Type` に住む。これは単なる命題ではなく、数値フィールド `carrier`, `residual`, `distinguished` と、それらに関する証明をまとめて保持する dependent record である。

### 値と証明の混在

`carrier : ℕ` のようなデータと、`carrier_pos : 0 < carrier` のような証明が同じ structure に入る。Lean ではこの設計により、packet を一度受け取れば projection を通して算術データと保証の双方へ直接アクセスできる。

### `Nonempty` との関係

直後の theorem は `SignedFiveAdicPacket u v w` 自体を直接返さず、`Nonempty (...)` を返す。したがって packet は後段で計算値として取り出すより、「必要な共通 invariant を満たす inhabitant が存在する」という証明上の容器として使われる設計と読める。

### existential フィールド

`residual_shape` と `carrier_padicValNat_shape` は witness を structure 内に保存する。

```lean
∃ M : ℕ, residual = 5 + 25 * M
```

```lean
∃ m : ℕ, padicValNat 5 carrier = 4 + 5 * m
```

単なる合同式だけでなく、後で `rcases` して直接利用できる算術 witness を残す API になっている。

## 冗長・重複箇所

この packet は意図的に情報を重複して保持している。

例えば

```lean
residual_mod_twentyFive : residual % 25 = 5
```

から `residual_shape` は除法算法で導出できる。また `% 25 = 5` から `5 ∣ residual` と `¬ 25 ∣ residual` を導き、0072 を使えば `residual_padicValNat = 1` も再構成できる。

同様に `residual_mod_twentyFive = 5` は residual が $0$ でないことを含意するので、`residual_pos` も自然数上では導出可能である。

さらに `carrier_padicValNat_shape` は `factor_eq`, `carrier_pos`, `residual_pos`, `distinguished_pos`, `residual_padicValNat` から 0073 を使って再構成できる。

したがって論理的最小性だけを求めればフィールド数は減らせる。しかし現行設計は **証明キャッシュ** として、後段の利用者が同じ bridge を何度も再実行しないことを優先している。この重複は museum 的には重要な設計意図である。

## 最適化候補

1. `residual_shape` を stored field ではなく projection theorem として `residual_mod_twentyFive` から導出する案がある。
2. `residual_padicValNat` も `% 25 = 5` から導出する projection theorem にできる。ただし後段で頻繁に使うなら現行のキャッシュ型の方が簡潔である。
3. `residual_pos` は `residual_mod_twentyFive` から導出可能なので、logical core を小さくするなら削除候補になる。
4. `carrier_padicValNat_shape` は 0073 の適用結果なので、packet 構築コストを下げたい場合は theorem 化できる。ただし後段 API の使いやすさとの trade-off がある。
5. `five_dvd_carrier` と `carrier_padicValNat_shape` の関係も監査可能である。後者は付値が少なくとも $4$ なので通常は 5 可除を含意するが、`padicValNat` API から毎回可除性へ戻すより explicit field の方が扱いやすい可能性が高い。
6. record を「最小核」と「派生キャッシュ」に二層化し、core structure + derived API に分ける設計も Comparator 対象として有力である。

これらはコード読解上の設計候補であり、Lean ビルドによる検証はしていない。

## 必要 Mathlib import と import 最適化候補

対象ブランチの standalone artifact 先頭では

```lean
import Mathlib
```

が使われている。

本 structure が直接必要とする Mathlib 側の要素は、自然数、順序、可除性、剰余、冪、および `padicValNat` である。リポジトリ内依存として `SignedBranchANormalForm` と `SignedFiveAdicSource` が必要になる。

standalone では `Mathlib` 全体が確実な import だが、本宣言単体には過剰である可能性が高い。元の分割モジュール `DkMath/FLT/Five/SignedFiveAdic.lean` の正確な import 行は今回対象ブランチ上で確認できていないため、個別 Mathlib module まで絞った最小 import は **未確認・推測** とする。

import 最適化を行うなら、まず `padicValNat` の定義・補題を提供する Mathlib module と `SignedBranchANormalForm` / `SignedFiveAdicSource` の所在を分けて監査し、`import Mathlib` から段階的に縮小するのが安全である。

## Comparator challenge 化の可否

**証明探索 challenge としては低適性、API/design challenge としては高適性** である。

比較課題としては「二 orientation から得られる five-adic invariant を、後段が最も使いやすい Lean API として設計せよ」がよい。

比較案は、

- 現行の全派生情報をキャッシュする fat record
- 最小 invariant のみを持つ thin record + projection theorem 群
- core / derived の二層 structure
- orientation ごとの packet を sum type で包み、共通 interface を typeclass / coercion で与える設計

などである。

評価軸は、後段証明の行数、再証明の回数、constructor の複雑さ、依存関係の透明性、rewrite の容易さ、将来の一般化可能性が適切である。

## 次に読むべき定理

Lean ソースの直後は

```lean
private theorem nonempty_signedFiveAdicPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    Nonempty (SignedFiveAdicPacket u v w) := by
```

である。

0075 は packet の **仕様** を定めただけで、まだ inhabitant の存在を示していない。次号では `SignedBranchANormalForm` の `differenceGap` / `sumGap` を場合分けし、これまでの mod $25$・可除性・valuation 補題を実際に束ねて `SignedFiveAdicPacket` を構築する。

したがって依存順では次に `DkMath.FLT.Five.nonempty_signedFiveAdicPacket_of_normalForm` を読むのが自然である。

## 根拠と注意

- structure 本体と直後の構築 theorem は、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` で確認した。
- 三つの入口 README は存在・非空であり、0074 まで日英対応で登録済みだったため初期化は不要だった。
- GitHub コード検索は今回 502 upstream error となったため、既知の対象ブランチ上の standalone Lean ソースを直接取得して根拠とした。
- 既存日本語・英語 PDF における本 structure の具体的対応ページは今回確認できなかった。したがって PDF 固有の説明やページ番号は推測で補っていない。
- Lean ビルドは行っていない。最適化候補は未検証である。
