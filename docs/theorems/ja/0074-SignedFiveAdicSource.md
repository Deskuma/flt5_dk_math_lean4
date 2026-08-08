# 0074 — `SignedFiveAdicSource`

## Lean の型

```lean
inductive SignedFiveAdicSource
    (u v w carrier residual distinguished : ℕ) : Prop
  | difference :
      carrier = w - v →
      residual = GN5 (w - v) v →
      distinguished = u →
      SignedFiveAdicSource u v w carrier residual distinguished
  | sum :
      carrier = u + v →
      residual = SumGN5 u v →
      distinguished = w →
      SignedFiveAdicSource u v w carrier residual distinguished
```

根拠は `docs/flt5-theorem-museum` ブランチの生成済み `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/SignedFiveAdic.lean` 部分である。

本号は theorem ではなく `inductive ... : Prop` 宣言である。しかし博物館は定義・構造・補題・定理を依存順に一宣言ずつ読む方針であり、0073 の直後かつ後続 `SignedFiveAdicPacket` の直接依存なので、定理だけを先に読むと依存順が逆転する。そのため本号で先に扱う。

## 数学的主張

`SignedFiveAdicSource u v w carrier residual distinguished` は、共通 five-adic packet に格納される三つ組

$$
(carrier, residual, distinguished)
$$

が、二つある signed orientation のどちらから来たかを記録する provenance 命題である。

`difference` constructor は

$$
carrier=w-v,
\qquad residual=GN5(w-v,v),
\qquad distinguished=u
$$

を表し、`sum` constructor は

$$
carrier=u+v,
\qquad residual=SumGN5(u,v),
\qquad distinguished=w
$$

を表す。

この宣言自体は新しい算術定理を主張しない。二つの表現上異なる branch を、同じ `carrier/residual/distinguished` インターフェースへ写した後も、その出自を失わないためのタグ付き命題である。

## 証明全体での役割

0073 までに、どちらの orientation でも residual の $5$-進付値が $1$、carrier の $5$-進付値が $4\pmod5$ になるための算術部品が揃った。次に必要なのは、それらを一つの共通 packet に束ねることである。

`SignedFiveAdicSource` はその packet の provenance フィールドとなる。直後の `SignedFiveAdicPacket` には

```lean
source : SignedFiveAdicSource u v w carrier residual distinguished
```

が入り、`nonempty_signedFiveAdicPacket_of_normalForm` の difference branch では

```lean
source := .difference rfl rfl rfl
```

sum branch では

```lean
source := .sum rfl rfl rfl
```

として構成される。

したがって後段は arithmetic invariant を共通化しながら、必要なら「この packet が差型から来たか和型から来たか」を pattern match で復元できる。

## 直接依存する定義・補題

直接依存する主要宣言は次の通り。

- `GN5`
- `SumGN5`
- 自然数 `ℕ`
- proposition universe `Prop`

数学的・証明的には `SignedBranchANormalForm` の二 orientation と対応するが、この inductive 宣言の型そのものには `SignedBranchANormalForm` は現れない。対応関係は後続 `SignedFiveAdicPacket` と `nonempty_signedFiveAdicPacket_of_normalForm` で具体化される。

## 宣言の流れ

本宣言には `:= by` で始まる証明本体はない。その代わり constructor が二本あり、それぞれ provenance の作り方を規定する。

1. 共通パラメータとして `u v w carrier residual distinguished : ℕ` を固定する。
2. `difference` constructor では carrier を `w - v`、residual を `GN5 (w - v) v`、distinguished を `u` に同定する三等式を要求する。
3. `sum` constructor では carrier を `u + v`、residual を `SumGN5 u v`、distinguished を `w` に同定する三等式を要求する。
4. どちらかの constructor が成立すれば、同じ命題 `SignedFiveAdicSource ...` が得られる。

つまり proof flow ではなく、二つの生成規則からなるデータ provenance の formation rule と読むのが正確である。

## Lean 固有の処理

### `inductive ... : Prop`

`SignedFiveAdicSource` はデータを返す `Type` ではなく `Prop` に置かれている。したがって目的は計算可能な branch tag を保存することではなく、「この三つ組が正当な二 orientation のどちらかから来た」という論理的証拠を保存することにある。

### constructor 内の等式

constructor は値そのものを内部で再定義せず、外から与えられた `carrier`, `residual`, `distinguished` が各 orientation の値と一致することを等式として要求する。この設計により、同じ packet structure が orientation に依存しないフィールド名を使える。

### `.difference rfl rfl rfl` / `.sum rfl rfl rfl`

後続 packet 構築では値を constructor の期待形そのものに選んでいるため、三つの同一視はすべて `rfl` で閉じる。Lean の dependent constructor を使った provenance 記録として非常に軽い実装になっている。

## 冗長・重複箇所

`difference` と `sum` はともに三つの等式を並べるため形は重複している。しかし、この重複は二 orientation の対応を明示するための意図的なものと見られる。

一方で `carrier`, `residual`, `distinguished` を inductive の外部パラメータにし、constructor 側で三本の等式を要求する設計はやや冗長でもある。constructor 自身が三つ組を existential に生成する設計や、orientation ごとの record を持つ設計も可能である。ただし現行設計は後続 `SignedFiveAdicPacket` の共通フィールドと非常に噛み合っている。

## 最適化候補

1. `SignedFiveAdicSource` を `SignedBranchAOrientation` から直接導出できる relation として一般化し、branch の対応表を一か所に集約する候補がある。
2. 三本の等式を一つの product equality や小さな record にまとめることもできるが、可読性と rewrite のしやすさは現行の個別等式が優れる可能性が高い。
3. provenance を後段で elimination しないなら `source` フィールド自体が不要か監査できる。ただし現時点の資料だけでは後続全体での使用有無を確定していないため、削除候補と断定はしない。
4. constructor 名 `difference` / `sum` は十分簡潔だが、`SignedBranchAOrientation.differenceGap` / `.sumGap` との対応を名前でさらに明示する案もある。

## 必要 Mathlib import と import 最適化候補

生成済み standalone artifact で確認できる import は

```lean
import Mathlib
```

である。ただし本宣言そのものが Mathlib から直接必要とするのは自然数と等式・inductive proposition の基礎だけであり、実質的な外部依存は `GN5` と `SumGN5` というリポジトリ内宣言である。

manifest 上の元モジュールは `DkMath/FLT/Five/SignedFiveAdic.lean` だが、対象ブランチでは分割元ファイルそのものを確認できていない。したがって元ファイルの正確な import 行と最小 import 集合は未確認である。`Mathlib` 全体は standalone 生成物としては確実だが、本宣言単体には過剰である可能性が高い。ここでの最小 import 評価は **推測** である。

## Comparator challenge 化の可否

**単独 challenge としての適性は低い。**

本宣言には証明探索がほぼなく、設計比較の対象だからである。ただし「二つの orientation を共通 packet に統合する provenance 型を設計せよ」という API/design comparator には向いている。

比較候補は、

- 現行の `inductive ... : Prop` + 三等式型
- orientation tag と dependent function で値を決める型
- branch ごとの record を sum type で包む型
- provenance を持たず packet の算術 invariant のみにする型

である。評価軸は constructor の簡潔さ、後続 rewrite のしやすさ、branch 情報の復元性、packet の共通化度がよい。

## 次に読むべき宣言

Lean ソースの直後は

```lean
structure SignedFiveAdicPacket (u v w : ℕ) : Type where
```

である。0074 が出自だけを記録するのに対し、0075 では normal form、carrier、residual、distinguished、factor equation、positivity、5 の可除性、mod 25、exact valuation、carrier valuation shape までを一つの record に束ねる。

したがって依存順では次に `DkMath.FLT.Five.SignedFiveAdicPacket` を読むのが自然である。その後に初めて、packet の存在を構成する theorem `nonempty_signedFiveAdicPacket_of_normalForm` へ進める。

## 根拠と注意

- 宣言本体、直後の `SignedFiveAdicPacket`、および `nonempty_signedFiveAdicPacket_of_normalForm` での `.difference` / `.sum` 構築は、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` で確認した。
- 0073 の記事自身も依存順の次宣言を `SignedFiveAdicSource` と明記している。
- 既存日本語・英語 PDF における本宣言の具体的ページ対応は今回確認できなかったため、PDF 固有の説明・ページ番号は推測で補っていない。
- Lean ビルドは行っていない。最適化案はコード読解上の候補であり、未検証である。
