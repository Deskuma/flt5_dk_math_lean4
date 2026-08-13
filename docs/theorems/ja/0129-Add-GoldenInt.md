# 0129 — `instance : Add GoldenInt`

## Lean の型

```lean
instance : Add GoldenInt := ⟨goldenAdd⟩
```

これは theorem ではなく、`GoldenInt` に Lean / Mathlib 標準の二項加法型クラス `Add` を与える匿名 instance である。

既に 0121 で

```lean
def goldenAdd (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst + y.fst, x.snd + y.snd⟩
```

が定義されている。本宣言はその raw coordinate operation を標準記法

```lean
x + y
```

へ接続する。

## 数学的主張

`GoldenInt` を

$$
x=a+b\varphi,
$$

$$
y=c+d\varphi,
$$

ただし

$$
\varphi^2=\varphi+1
$$

と読むと、加法は

$$
x+y=(a+c)+(b+d)\varphi
$$

であり、座標では

$$
(a,b)+(c,d)=(a+c,b+d)
$$

となる。

本 instance 自身は新しい等式を証明しない。0121 `goldenAdd` で既に定義された座標加法を `Add GoldenInt` の `add` field として登録し、Lean の標準 `+` と同一視するための adapter である。

## 証明全体での役割

0127 と 0128 で `0` と `1` の標準記法が導入された後、本宣言は最初の標準二項演算を `GoldenInt` に与える。

この登録直後には

```lean
instance : Neg GoldenInt := ⟨goldenNeg⟩
instance : Sub GoldenInt := ⟨goldenSub⟩
instance : Mul GoldenInt := ⟨goldenMul⟩
```

が続き、raw arithmetic API が順に Lean の代数階層へ接続される。

さらに source は

```lean
@[simp] theorem golden_fst_add (x y : GoldenInt) :
    (x + y).fst = x.fst + y.fst := rfl
@[simp] theorem golden_snd_add (x y : GoldenInt) :
    (x + y).snd = x.snd + y.snd := rfl
```

を与える。これらが `rfl` で閉じるのは、本 instance が `goldenAdd` を直接 `add` field に格納しているからである。

その後の

```lean
instance goldenAddCommGroup : AddCommGroup GoldenInt := by
  ...
```

では加法群構造が構築される。本宣言はその前段階として、標準 `+` の意味を raw coordinate addition に固定する。

FLT5 全体では、黄金整数の共役、ノルム、整除、Euclidean-domain 構造、五乗因子分解へ進む際、加法を Mathlib 標準記法で扱えることが不可欠である。したがって本宣言は小さいが、以後の algebraic hierarchy を成立させる基礎 API boundary である。

## 直接依存する定義・補題

直接依存は次の三点である。

1. `GoldenInt`
2. `goldenAdd`
3. Lean / Mathlib の `Add` 型クラス

`goldenZero`、`goldenOne`、`goldenNeg`、`goldenSub`、`goldenMul`、`GoldenInt.ext` には論理的には依存しない。

ただし source organization としては、carrier、raw zero/one/add/neg/sub/mul/pow、extensionality を先に定義し、その後に標準 typeclass instance 群をまとめて登録する順序になっている。

## 証明の流れ

proof script はない。宣言本体

```lean
⟨goldenAdd⟩
```

だけで `Add GoldenInt` を構築する。

概念的には次の一段である。

1. `goldenAdd : GoldenInt → GoldenInt → GoldenInt` を `Add GoldenInt` の `add` field に格納する。

その結果、期待型が `GoldenInt` の文脈では

```lean
x + y
```

が typeclass synthesis を通じて `goldenAdd x y` に展開される。

## Lean 固有の処理

### 1. 型クラス登録

`instance` 宣言なので、後続コードは `Add GoldenInt` を明示引数として渡さずに `x + y` を使用できる。Lean の typeclass synthesis がこの instance を自動的に解決する。

### 2. constructor notation `⟨goldenAdd⟩`

`Add α` は二項演算

```lean
add : α → α → α
```

を保持する typeclass structure である。期待型が `Add GoldenInt` と既知なので、Lean は `⟨goldenAdd⟩` をその唯一の field を埋める constructor expression として elaboration する。

### 3. overloaded notation `+`

`+` は型に依存する多相的な記法である。本 instance 以後、`GoldenInt` が期待される場所の

```lean
x + y
```

は `goldenAdd x y` を意味する。

### 4. definitional equality

本 instance が `goldenAdd` を直接登録するため、

```lean
(x + y).fst
```

は kernel reduction により

```lean
x.fst + y.fst
```

まで落ちる。同様に `.snd` は `x.snd + y.snd` へ還元される。

したがって

```lean
@[simp] theorem golden_fst_add ... := rfl
@[simp] theorem golden_snd_add ... := rfl
```

が theorem-level rewrite を必要とせず `rfl` で成立する。

### 5. raw API と標準 API の境界

`goldenAdd` は明示名を持つ raw coordinate API、本宣言で導入される `+` は Mathlib algebra hierarchy 用の標準 API である。両者を definitional equality で接続することにより、低レベル座標計算と高レベル代数構造の双方を簡潔に扱える。

### 6. instance 構築順序

`Add GoldenInt` は `AddCommGroup GoldenInt` より前に独立して登録される。これにより後続の座標 simp lemma や構造法則の証明で、標準 `+` を早い段階から使える。

一方で、後続の `goldenAddCommGroup` は raw `goldenAdd` を再び明示的に参照しており、bootstrap 中の definitional transparency を優先した設計と読める。

## 冗長・重複箇所

0121 と本宣言は同じ数学的演算を二層に分けて保持している。

```lean
def goldenAdd (x y : GoldenInt) : GoldenInt := ...
instance : Add GoldenInt := ⟨goldenAdd⟩
```

技術的には instance 側へ座標式を直接 inline できる。

```lean
instance : Add GoldenInt :=
  ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
```

しかし現状の分離には、

- raw arithmetic を typeclass hierarchy より先に bootstrap できる
- `goldenAdd` を明示名で再利用できる
- 標準 `+` が何に対応するか監査しやすい
- `rfl` による座標 projection lemma を保ちやすい

という利点がある。

0127 `Zero`、0128 `One`、この 0129 `Add`、続く `Neg` / `Sub` / `Mul` は同じ adapter pattern を繰り返すため、コード形としては明らかな重複である。ただし各 raw operation と標準 typeclass の一対一対応を露出させるための意図的な重複とも解釈できる。

## 最適化候補

### 候補 A — 現状維持

最も監査しやすい。`goldenAdd` と `+` の対応が一行で分かり、projection lemma が `rfl` のまま保たれる。

### 候補 B — instance へ inline

`goldenAdd` を削除し、座標式を `Add` instance に直接埋め込む案である。

コード宣言数は減るが、raw layer を標準 typeclass layer より先に使う現在の bootstrap 設計が崩れる。また後続で `goldenAdd` を明示利用している箇所の書き換えが必要になる。

### 候補 C — primitive operation bundle を導入

zero / one / add / neg / sub / mul を独自 structure にまとめ、その bundle から標準 instance を生成する方法も考えられる。

ただし現在の規模では abstraction cost の方が大きい可能性がある。

### 候補 D — `AddCommGroup` から `Add` を供給

最初から `AddCommGroup GoldenInt` を構築し、そこから `Add` を得る設計も可能である。

しかしその場合、加法群法則を証明する前に標準 `+` を使用したい bootstrap code の依存関係が複雑になる。現在の段階的登録は循環を避ける点で素直である。

### 候補 E — named instance 化

匿名 instance に名前を与えれば、Comparator、import debugging、`#synth` 周辺の調査で明示参照しやすくなる。通常利用では自動 synthesis が十分なので必須ではない。

### 候補 F — `@[simp]` projection lemma の自動生成

`golden_fst_add` / `golden_snd_add` は定義的に自明なので、raw operation 群に対する projection simp lemma を一定パターンで生成する仕組みを導入すれば repetition を削減できる。ただし少数宣言しかない現状では手書きの方が追跡しやすい。

## 必要 Mathlib import と import 最適化候補

対象 standalone source は全体として

```lean
import Mathlib
```

を使用している。

本宣言単独に必要なのは `GoldenInt`、`goldenAdd`、`Add` 型クラスと基本的な instance machinery だけであり、この一行のためだけに umbrella import `Mathlib` 全体が必要とは考えにくい。

一方、同じ `GoldenOrder` 区間では続けて `AddCommGroup`、`CommRing`、`IsDomain` などを構築するため、ファイル単位の最小 import は本宣言だけからは決定できない。

この博物館作業では Lean build を行わない方針なので、具体的な最小 Mathlib module 名は未検証であり、推測として固定しない。

import 最適化を行うなら、`GoldenOrder` を単独 module として切り出した状態で umbrella import を外し、必要 theorem / class の不足を一つずつ補う Comparator 実験が妥当である。

## Comparator challenge 化の可否

 **適している。小規模だが bootstrap / API-design 比較として有用である。**

比較対象は例えば次である。

1. raw `goldenAdd` + separate `Add` instance
2. coordinate formula を instance に inline
3. `AddCommGroup` からまとめて供給
4. 独自 primitive-operation bundle から instance を生成
5. anonymous instance と named instance の比較

評価軸は、

- `(x + y).fst` / `.snd` が `rfl` で期待座標へ落ちるか
- bootstrap dependency が循環しないか
- `goldenAdd` を明示的に再利用できるか
- standard notation と raw definition の対応が監査しやすいか
- typeclass synthesis が安定するか
- import footprint が小さいか

である。

特に「標準 `+` をいつ導入するのが最も依存関係を単純に保てるか」は、形式化ライブラリ設計の小さな Comparator challenge として意味がある。

## 既存資料との対応

対象ブランチには

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを GitHub 上で確認した。

今回、PDF の存在までは確認したが、本文の `Add GoldenInt` instance に対応する具体的ページ・節は直接照合していない。そのため PDF 固有のページ番号や叙述は推測で補わない。

形式的内容の最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` 内 `GoldenOrder.lean` generated section とする。

## 次に読むべき宣言

直後の宣言は

```lean
instance : Neg GoldenInt := ⟨goldenNeg⟩
```

である。

0129 で標準加法 `+` が利用可能になった。次は 0122 `goldenNeg` を標準単項マイナス `-x` へ接続し、加法逆元の標準 API を導入する段階へ進む。