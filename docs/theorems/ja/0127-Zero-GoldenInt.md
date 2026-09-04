# 0127 — `instance : Zero GoldenInt`

## Lean の型

```lean
instance : Zero GoldenInt := ⟨goldenZero⟩
```

これは名前付き theorem ではなく、`GoldenInt` に標準の零元型クラス `Zero` を与える匿名 instance である。

既に 0119 で

```lean
def goldenZero : GoldenInt := ⟨0, 0⟩
```

が定義されている。本宣言はその raw definition を Lean の標準記法

```lean
(0 : GoldenInt)
```

へ接続する。

## 数学的主張

`GoldenInt` は座標

$$
x=a+b\varphi
$$

で黄金整数を表す。その零元は

$$
0=0+0\varphi
$$

なので、座標としては

$$
(0,0)
$$

である。

本 instance 自身は新しい数学命題を証明しない。0119 `goldenZero` で既に選ばれている要素を、Lean の代数型クラス `Zero GoldenInt` の carrier として登録する宣言である。

したがって数学的内容は「黄金整数環の零元は座標 $(0,0)$ である」という定義的選択に尽きる。

## 証明全体での役割

0120–0125 では `goldenOne`、`goldenAdd`、`goldenNeg`、`goldenSub`、`goldenMul`、`goldenPow` という raw API が構築された。0126 `GoldenInt.ext` で equality proof の座標分解も準備された。

ここからは、それらの raw operation を Lean / Mathlib が理解する標準代数 API へ順に接続する。

本 instance が入ることで、以後は

```lean
0
```

と書くだけで `goldenZero` を参照できる。直後には

```lean
instance : One GoldenInt := ⟨goldenOne⟩
instance : Add GoldenInt := ⟨goldenAdd⟩
instance : Neg GoldenInt := ⟨goldenNeg⟩
instance : Sub GoldenInt := ⟨goldenSub⟩
instance : Mul GoldenInt := ⟨goldenMul⟩
```

が続き、その後 `AddCommGroup GoldenInt`、`CommRing GoldenInt`、`IsDomain GoldenInt` へ発展する。

したがって本宣言は、座標モデル `GoldenInt` を Mathlib の通常の代数階層へ載せ始める最初の adapter である。

## 直接依存する定義・補題

直接依存は非常に小さい。

1. `GoldenInt`
2. `goldenZero`
3. Lean / Mathlib の `Zero` 型クラス

特に 0126 `GoldenInt.ext` や `goldenAdd`、`goldenMul` には論理的には依存しない。依存順としては raw API 一式を完成させてから typeclass registration に入る設計になっている。

## 証明の流れ

proof script は存在しない。宣言本体

```lean
⟨goldenZero⟩
```

が `Zero GoldenInt` structure の constructor にそのまま渡される。

概念的には次の一段だけである。

1. `goldenZero : GoldenInt` を用意する。
2. `Zero GoldenInt` が要求する `zero : GoldenInt` field にそれを格納する。

これにより Lean の notation resolution は

```lean
(0 : GoldenInt)
```

を `Zero.zero` 経由で `goldenZero` に解釈する。

## Lean 固有の処理

### 1. 型クラス instance 登録

`instance` として登録されるため、明示的に引数として渡さなくても typeclass synthesis が `Zero GoldenInt` を自動発見する。

この時点以後、`0` を期待型 `GoldenInt` の文脈で使える。

### 2. constructor notation `⟨goldenZero⟩`

`Zero α` は零元を一つ持つ小さな typeclass structure である。期待型が `Zero GoldenInt` と分かっているため、Lean は

```lean
⟨goldenZero⟩
```

をその唯一の主要 field を埋める constructor expression として elaboration する。

### 3. definitional equality

この instance は `goldenZero` を直接 field に格納しているため、後続の

```lean
@[simp] theorem golden_fst_zero : (0 : GoldenInt).fst = 0 := rfl
@[simp] theorem golden_snd_zero : (0 : GoldenInt).snd = 0 := rfl
```

が `rfl` で閉じる。

これは重要な設計上の利点である。`0` と raw coordinate zero の間に theorem-level rewrite を挟まず、kernel reduction だけで座標まで落とせる。

### 4. 記法解決

整数リテラルの `0` は多相的であり、期待型に応じて適切な `OfNat` / `Zero` 系の instance が利用される。ここでは `GoldenInt` の零元として解釈されるための基礎 instance を与えている。

## 冗長・重複箇所

0119 `goldenZero` と本 instance は見かけ上同じ情報を二度書いている。

```lean
def goldenZero : GoldenInt := ⟨0, 0⟩
instance : Zero GoldenInt := ⟨goldenZero⟩
```

技術的には instance 側に

```lean
instance : Zero GoldenInt := ⟨⟨0, 0⟩⟩
```

と直接書くこともできる。

しかし raw API と標準 typeclass API を分離しているため、後続の standalone calculations では `goldenZero` を明示名として使え、Mathlib の代数階層では `0` を使える。したがってこれは単純な無駄というより API 層の意図的な重複である。

## 最適化候補

### 候補 A — 現状維持

最も明瞭である。raw coordinate definition と standard algebra notation の境界が一行で見える。

### 候補 B — instance へ inline

```lean
instance : Zero GoldenInt := ⟨⟨0, 0⟩⟩
```

として `goldenZero` を削除する案である。

コード量は減るが、`goldenZero` を explicit API として使う後続コードや説明の対称性が失われる。

### 候補 C — 標準 algebra structure を早期に bundle する

`Zero`、`One`、`Add`、`Neg`、`Sub`、`Mul` を個別登録せず、`AddCommGroup` や `CommRing` construction の中でまとめて提供する設計も可能である。

ただし現在の段階的設計は各 primitive operation の definitional equality を追いやすく、証明博物館としても監査しやすい。

### 候補 D — named instance 化

匿名 instance に名前を与えることで source navigation や明示的参照を容易にする案である。通常は typeclass synthesis で十分なので必須ではないが、Comparator や import debugging では名前付き instance が便利な場合がある。

## 必要 Mathlib import と import 最適化候補

対象 standalone source は全体として

```lean
import Mathlib
```

を使用している。

本宣言単独が必要とするのは `GoldenInt`、`goldenZero`、`Zero` typeclass と基本的な instance machinery だけである。したがって本 instance のためだけに `Mathlib` 全体が必要とは考えにくい。

一方、実際の modular source ではこの直後に `One`、`Add`、`Neg`、`Sub`、`Mul`、`AddCommGroup`、`CommRing` まで構築するため、ファイル単位の最小 import は本一行だけからは決められない。

具体的な最小 module 名は Lean build を行っていないため未検証であり、ここでは推測として固定しない。

## Comparator challenge 化の可否

 **適しているが、小規模 challenge 向けである。**

比較対象は例えば次である。

1. raw `goldenZero` + separate `Zero` instance
2. instance への coordinate inline
3. named instance
4. `CommRing` construction まで bundle して primitive instance をまとめる設計

評価軸は definitional equality、source readability、API の二層性、typeclass synthesis の透明性、後続 `rfl` lemma の簡潔さ、import footprint である。

特に「どの設計なら `(0 : GoldenInt).fst = 0` を `rfl` のまま保てるか」は良い比較点になる。

## 既存資料との対応

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が既存資料として置かれている。

この回では PDF 本文中の anonymous `Zero GoldenInt` instance に対応する具体的なページ・節を直接解析していない。したがって PDF 固有の説明やページ番号は推測しない。

形式的内容の最終根拠は、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` 内 `GoldenOrder.lean` generated section である。

## 次に読むべき宣言

直後の宣言は

```lean
instance : One GoldenInt := ⟨goldenOne⟩
```

である。

0127 で raw zero が標準 `0` へ接続された。次は 0120 `goldenOne` を標準 `1` へ接続し、加法・否定・減法・乗法の instance 群へ進む。