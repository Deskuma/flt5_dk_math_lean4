# 0128 — `instance : One GoldenInt`

## Lean の型

```lean
instance : One GoldenInt := ⟨goldenOne⟩
```

これは theorem ではなく、`GoldenInt` に Lean / Mathlib 標準の乗法単位元型クラス `One` を与える匿名 instance である。

既に 0120 で

```lean
def goldenOne : GoldenInt := ⟨1, 0⟩
```

が定義されている。本宣言はその raw coordinate definition を標準記法

```lean
(1 : GoldenInt)
```

へ接続する。

## 数学的主張

`GoldenInt` は黄金整数を座標

$$
x=a+b\varphi,
$$

ただし

$$
\varphi^2=\varphi+1
$$

として表す。その乗法単位元は

$$
1=1+0\varphi
$$

なので、座標では

$$
(1,0)
$$

である。

本 instance 自身は新しい数学命題を証明しない。0120 `goldenOne` で既に選択された要素を `One GoldenInt` の `one` field として登録し、Lean の標準代数記法 `1` と同一視するための adapter である。

## 証明全体での役割

0127 `instance : Zero GoldenInt` が raw zero を標準 `0` へ接続したのに対し、本宣言は raw one を標準 `1` へ接続する対称な typeclass boundary である。

この登録の直後には

```lean
instance : Add GoldenInt := ⟨goldenAdd⟩
instance : Neg GoldenInt := ⟨goldenNeg⟩
instance : Sub GoldenInt := ⟨goldenSub⟩
instance : Mul GoldenInt := ⟨goldenMul⟩
```

が続く。さらに後続では

```lean
@[simp] theorem golden_fst_one : (1 : GoldenInt).fst = 1 := rfl
@[simp] theorem golden_snd_one : (1 : GoldenInt).snd = 0 := rfl
```

が `rfl` で成立する。

したがって本宣言は、0120 で座標として固定された乗法単位元を、後続の `CommRing GoldenInt`、冪、単元、整除、Euclidean-domain 構造が利用する標準 API へ昇格させる小さな橋である。

特に 0125 `goldenPow` は raw API として零乗を `goldenOne` で定義している。後続で標準冪 `x ^ n` を `goldenPow x n` へ一致させる際、本 instance により raw `goldenOne` と標準 `1` が definitional に接続されるため、冪の単位元法則を簡潔に保てる。

## 直接依存する定義・補題

直接依存は次の三点に限られる。

1. `GoldenInt`
2. `goldenOne`
3. Lean / Mathlib の `One` 型クラス

論理的には `goldenZero`、`goldenAdd`、`goldenMul`、`GoldenInt.ext` などには依存しない。ただし source organization としては raw arithmetic API を先に定義し、その後に標準 typeclass instance 群をまとめて登録する順序を採っている。

## 証明の流れ

proof script はない。宣言本体

```lean
⟨goldenOne⟩
```

だけで `One GoldenInt` を構築する。

概念的には次の一段である。

1. `goldenOne : GoldenInt` を `One GoldenInt` の `one : GoldenInt` field に格納する。

その結果、期待型が `GoldenInt` の文脈では

```lean
1
```

が typeclass synthesis を通じて `goldenOne` に展開される。

## Lean 固有の処理

### 1. 型クラス登録

`instance` 宣言なので、後続コードは `One GoldenInt` を明示引数として受け取る必要がない。Lean の typeclass synthesis が自動的にこの instance を発見する。

### 2. constructor notation `⟨goldenOne⟩`

`One α` は `one : α` を保持する typeclass structure である。期待型が `One GoldenInt` と既知なので、Lean は

```lean
⟨goldenOne⟩
```

をその field を埋める constructor expression として elaboration する。

### 3. overloaded numeral `1`

`1` は多相的な記法であり、期待型と typeclass machinery によって意味が決まる。本宣言以後、`GoldenInt` が期待される場所の `1` は黄金整数の $(1,0)$ を表す。

ここで重要なのは、右辺の `goldenOne` 自身はすでに明示的な `GoldenInt` 値なので、instance 定義時に自己循環を起こさないことである。

### 4. definitional equality

instance field に `goldenOne` を直接格納しているので、

```lean
(1 : GoldenInt).fst
```

は kernel reduction により `goldenOne.fst`、さらに `1` へ落ちる。同様に `.snd` は `0` まで還元される。

このため後続の

```lean
@[simp] theorem golden_fst_one : (1 : GoldenInt).fst = 1 := rfl
@[simp] theorem golden_snd_one : (1 : GoldenInt).snd = 0 := rfl
```

が theorem rewrite や `simp` を必要とせず `rfl` で閉じる。

### 5. raw API と標準 API の境界

`goldenOne` は明示名を持つ raw coordinate API、本宣言の `1` は Mathlib algebra hierarchy 用の標準 API である。この二層を definitional equality で接続している点が設計上の要点である。

## 冗長・重複箇所

0120 と本宣言は同じ数学的データを二層で保持している。

```lean
def goldenOne : GoldenInt := ⟨1, 0⟩
instance : One GoldenInt := ⟨goldenOne⟩
```

技術的には

```lean
instance : One GoldenInt := ⟨⟨1, 0⟩⟩
```

と直接書くこともできるため、コード量だけなら `goldenOne` は省略可能である。

しかし現在の設計では `goldenPow` の基底ケースが

```lean
| 0 => goldenOne
```

と typeclass registration 前から定義できる。したがってこの重複は、raw arithmetic を標準代数階層より先に bootstrap するための意図的な API 分離と解釈できる。

0127 `Zero GoldenInt` とほぼ完全に対称な declaration pattern であり、構造的重複は大きい。ただしこの対称性そのものが carrier の基本定数を監査しやすくしている。

## 最適化候補

### 候補 A — 現状維持

raw `goldenOne` と `One GoldenInt` の接続が一行で見え、`goldenPow` の bootstrap も自然である。definitional equality も保たれる。

### 候補 B — instance へ inline

```lean
instance : One GoldenInt := ⟨⟨1, 0⟩⟩
```

として `goldenOne` を削除する案である。

ただし `goldenPow` を typeclass registration より前に定義する現在の順序を維持するなら、零乗の基底値を別の形で与える必要が生じる。

### 候補 C — `goldenOfInt` から統一生成

例えば

```lean
def goldenOfInt (n : ℤ) : GoldenInt := ⟨n, 0⟩
```

を primitive にして、

```lean
def goldenZero := goldenOfInt 0
def goldenOne := goldenOfInt 1
```

とする案である。整数埋め込みとの接続が後続で重要になるなら、零元・単位元の重複を意味のある embedding API にまとめられる。

一方、現段階では abstraction を一つ増やすため、単純さとの交換になる。

### 候補 D — primitive instance 群を algebra structure と同時に bundle

`Zero`、`One`、`Add`、`Neg`、`Sub`、`Mul` を個別に登録せず `CommRing GoldenInt` construction にまとめることも可能である。

しかし現在の段階的構築は、各記法がどの raw operation に definitional に対応するかを監査しやすい。FLT5 証明のように後続で座標計算を多用する場合、この透明性には価値がある。

### 候補 E — named instance 化

匿名 instance に名前を与えれば、import debugging、Comparator、`#synth` 周辺の調査で明示参照しやすくなる。通常利用では typeclass synthesis が十分なので必須ではない。

## 必要 Mathlib import と import 最適化候補

対象 standalone source は全体として

```lean
import Mathlib
```

を使用している。

本宣言単独に必要なのは `GoldenInt`、`goldenOne`、`One` typeclass と基本的な instance machinery だけであるため、本一行のためだけに `Mathlib` 全体が必要とは考えにくい。

ただし実際の `GoldenOrder` 区間は続けて `AddCommGroup`、`CommRing`、`IsDomain` などを構築する。ゆえにファイル単位の最小 import は本 instance 単独からは確定できない。

具体的な最小 Mathlib module 名は Lean build を行っていないため未検証であり、推測として固定しない。

## Comparator challenge 化の可否

 **適している。ただし小規模な API-design challenge 向けである。**

比較対象としては次が考えられる。

1. raw `goldenOne` + separate `One` instance
2. coordinate を instance に inline
3. `goldenOfInt` 経由で zero / one を統一
4. primitive instance 群を `CommRing` bundle に集約
5. anonymous instance と named instance の比較

評価軸は、

- `(1 : GoldenInt).fst = 1` と `.snd = 0` が `rfl` のまま保てるか
- `goldenPow` の bootstrap に循環が生じないか
- raw API と標準 notation の関係が読みやすいか
- typeclass synthesis が安定しているか
- import footprint が小さいか

である。

特に「標準 `1` を早く導入しすぎず、それでも後続 `CommRing` には自然に接続する」という bootstrap order は Comparator の良い観察点になる。

## 既存資料との対応

対象ブランチには

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを GitHub 上で確認した。

今回、PDF 本文を直接取得して `One GoldenInt` instance に対応するページ・節を照合しようとしたが、取得経路では PDF 本文を展開できなかった。そのため PDF 固有のページ番号や叙述は推測で補わない。

形式的内容の最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` 内 `GoldenOrder.lean` generated section とし、PDF は既存の叙述資料として位置付ける。

## 次に読むべき宣言

直後の宣言は

```lean
instance : Add GoldenInt := ⟨goldenAdd⟩
```

である。

0127 と 0128 で標準定数 `0` と `1` が揃った。次は 0121 `goldenAdd` を標準記法 `x + y` へ接続し、座標加法を Mathlib の additive API に載せる段階へ進む。