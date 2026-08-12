# 0119 — `goldenZero`

## Lean の型

```lean
def goldenZero : GoldenInt := ⟨0, 0⟩
```

`goldenZero` は 0118 で導入した `GoldenInt` の二座標をともに整数零にした要素である。

$$
goldenZero=(0,0).
$$

`GoldenInt` を $a+b\varphi$ の座標モデルとして読むと、これは

$$
0+0\varphi=0
$$

に対応する。

## 数学的主張

この宣言は theorem ではなく定義であり、黄金整数座標系における加法単位元の候補を具体的に与える。

重要なのは、この時点ではまだ Lean の型クラス `[Zero GoldenInt]` 自体は導入されていないことである。source では後続に

```lean
instance : Zero GoldenInt := ⟨goldenZero⟩
```

が置かれ、そこで初めて通常の記法 `(0 : GoldenInt)` が `goldenZero` を参照するようになる。

したがって 0119 は「零元の座標値を定める層」であり、型クラスとして零元を公開する層とは分離されている。

## 証明全体での役割

`GoldenOrder.lean` は `GoldenInt` を $\mathbb Z[\varphi]$ の直接座標モデルとして育てていく。0118 が carrier を定め、0119 はその最初の distinguished element として零元を置く。

後続では `goldenOne`、`goldenAdd`、`goldenNeg`、`goldenSub`、`goldenMul` が続き、それらを `Zero`、`One`、`Add`、`Neg`、`Sub`、`Mul` instance に接続する。その後に加法・乗法の法則を証明して ring structure を構築するため、`goldenZero` は環構造構築の最小基礎部品である。

FLT5 固有の数論情報を直接処理する宣言ではないが、後段の黄金整数整除・ノルム・Euclidean 構造・降下を成立させる algebraic infrastructure の入口に属する。

## 直接依存する定義・補題

直接依存はほぼ 0118 `GoldenInt` のみである。

- `GoldenInt` — 値を構築する対象型。
- 整数リテラル `0 : ℤ` — `fst`, `snd` の両座標。
- structure constructor notation `⟨0, 0⟩` — `GoldenInt.mk 0 0` の省略記法。

FLT5 の equation、five-adic packet、square-golden packet などには直接依存しない。

## 証明・構築の流れ

proof script は存在しない。定義本体そのものが constructor application である。

```lean
⟨0, 0⟩
```

Lean は期待型 `GoldenInt` から、この記法を概念的に

```lean
GoldenInt.mk 0 0
```

と解釈する。よって unfolding すれば

```lean
(goldenZero).fst = 0
(goldenZero).snd = 0
```

は定義簡約で得られる。

この「まず raw definition を置き、後で typeclass instance に接続する」という流れは直後の `goldenOne` にも繰り返される。

## Lean 固有の処理

### 期待型による constructor 推論

`⟨0, 0⟩` に `GoldenInt.mk` と明記していないが、左辺の返り値型が `GoldenInt` なので Lean が constructor を推論する。

### 数値リテラルの型推論

二つの `0` は `GoldenInt.fst`, `GoldenInt.snd` の型が `ℤ` であることから整数零へ elaboration される。

### definitional equality

`goldenZero` は theorem ではないため、座標展開に論理的な証明は不要である。`rfl`、`simp [goldenZero]`、あるいは unfolding により座標値を直接利用できる。

### raw definition と typeclass instance の分離

後続の

```lean
instance : Zero GoldenInt := ⟨goldenZero⟩
```

によって `(0 : GoldenInt)` が利用可能になる。この二段階設計により、零元の具体値と型クラス公開を別々に監査できる。

## 冗長・重複箇所

宣言自体は最小であり、内部の冗長性はない。

ただし設計レベルでは、後続 instance を

```lean
instance : Zero GoldenInt := ⟨⟨0, 0⟩⟩
```

のように直接書けば `goldenZero` という名前付き定義を省略できる。にもかかわらず raw definition を分離しているのは、演算の concrete coordinate implementation に名前を与え、instance construction と切り離すためと読める。

この意図は `goldenOne`、`goldenAdd`、`goldenNeg` などにも共通するため、局所的重複というより API 設計上の一貫したパターンである。

## 最適化候補

### 1. instance へ inline する

コード行数だけなら `goldenZero` を消して `Zero GoldenInt` instance に `⟨0,0⟩` を直接埋め込める。しかし concrete operation に独立した名前がなくなり、後続 proof で raw implementation を明示参照しにくくなる。

### 2. `@[simp]` 座標補題を追加する

例えば

```lean
@[simp] theorem goldenZero_fst : goldenZero.fst = 0 := rfl
@[simp] theorem goldenZero_snd : goldenZero.snd = 0 := rfl
```

を用意する案はある。ただし instance 導入後に `(0 : GoldenInt).fst` などを `rfl` / `simp` で処理できるなら、専用補題は過剰になる可能性がある。

### 3. operation bundle の一括定義

zero/one/add/neg/sub/mul を一つの algebraic structure construction に直接埋め込む方法もある。しかし現行のように座標演算を小さな named definitions に分割した方が、後続の ring-law 証明や Comparator では実装を追跡しやすい。

## 必要 Mathlib import と import 最適化候補

standalone source は冒頭で

```lean
import Mathlib
```

を一括 import している。

`goldenZero` 単独では、既に `GoldenInt` が利用可能なら新たな Mathlib theorem を何も必要としない。必要なのは structure constructor と整数リテラルだけであり、0119 のために `Mathlib` 全体を import する必要はない。

module 単位では後続に ring structure、整数算術、`Zsqrtd 5` への写像、`simp` / `ring` を用いる証明があるため、`GoldenOrder.lean` 全体の最小 import はより大きい。本記事では Lean build を行っていないため、具体的な最小 import 集合は未検証であり、import 縮小可能性は設計上の推測として扱う。

## Comparator challenge 化の可否

小さい宣言なので単独 challenge としては難易度が低すぎるが、`GoldenInt` の primitive operations 設計比較の一部としては適している。

比較候補は、(a) 現行の raw definition + instance 二段階方式、(b) typeclass instance へ直接 inline する方式、(c) ring structure 構築時に zero/one/operations をまとめて供給する方式である。

評価軸は、定義展開の透明性、`simp` の扱いやすさ、instance search との分離、後続 ring-law proof の短さ、コード監査性である。

## 根拠資料と推測の範囲

形式的根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenOrder.lean` generated section である。そこでは `GoldenInt` の直後に `goldenZero`、`goldenOne`、座標演算群が並び、その後に `Zero GoldenInt` などの instance が導入されている。

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。今回は PDF 本文の `goldenZero` 対応箇所を直接照合していないため、PDF のページ番号・節番号や表現については推測していない。

`@[simp]` 補題追加や import 最小化は最適化候補であり、現行 source が採用しているという主張ではない。

## 次に読むべき宣言

依存順で直後は

```lean
def goldenOne : GoldenInt := ⟨1, 0⟩
```

である。

0119 が加法単位元候補 $0$ を与えたのに対し、次は乗法単位元候補 $1$ を同じ座標モデルで定める。したがって次号は `goldenOne` を読むのが自然である。
