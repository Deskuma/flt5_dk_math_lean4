# 0118 — `GoldenInt`

## Lean の型

```lean
structure GoldenInt where
  fst : ℤ
  snd : ℤ
deriving DecidableEq
```

`GoldenInt` は二つの整数座標 `fst`, `snd` を持つ structure である。Lean source の説明では、基底 $1,\varphi$ に関する

$$
a+b\varphi,\qquad a,b\in\mathbb Z,
$$

を整数対 $(a,b)$ で表し、後続で

$$
\varphi^2=\varphi+1
$$

という関係に従う乗法を与えるための carrier と位置づけられている。

`deriving DecidableEq` により、二つの `GoldenInt` の等号は計算可能に判定できる。

## 数学的主張

この宣言そのものは theorem ではなく、黄金整数環を扱うための基礎データ型の定義である。数学的には

$$
\mathbb Z[\varphi]
 = \{a+b\varphi\mid a,b\in\mathbb Z\},
$$

を座標環として直接実装する入口に当たる。

ただし重要な注意として、ここで `GoldenInt` を定義しただけでは、まだ Lean 上で環構造も、$\varphi^2=\varphi+1$ も、$\mathbb Q(\sqrt5)$ の整数環との同型も証明されていない。source の module comment も、体レベルの同型を構築するのではなく、この座標モデルに対して後から ring・norm・divisibility・Euclidean-domain structure を証明して使う方針を明示している。

したがって「`GoldenInt` は $\mathbb Z[\varphi]$ そのもの」という読み方は、後続で構築される演算と法則まで含めた数学的意味であり、この structure 宣言単独では「整数の直積型」にすぎない。

## 証明全体での役割

0117 までで `SignedSquareGoldenExceptionalCore` を仮定すれば Branch-B を閉じられるところまで、矛盾を受け取る interface が整った。ここから `GoldenOrder.lean` は、その core を最終的に供給するための黄金整数算術を下から構築する段階に入る。

`GoldenInt` はその最下層 carrier である。後続ではこの型上に零元・単位元・加法・負号・乗法・共役・ノルムを実装し、さらに零因子の不存在、整域性、整除、Euclidean 構造へ進む。

特に module comment は、後続で用いる二つの distinguished elements

$$
\sqrt5\text{-direction}:\quad 2\varphi-1,
$$

$$
\tau=2+\varphi
$$

をこの座標環上で定義し、FLT5 の ramification identities に接続することを説明している。

したがって 0118 は、これまで自然数・整数上の packet として保持してきた FLT5 の情報を、黄金整数の因数分解・整除・降下へ移すための新しい代数 universe の入口である。

## 直接依存する定義・補題

この宣言自身の直接依存は極めて少ない。

- `ℤ` — 二つの座標の型。
- Lean の `structure` — `fst`, `snd` という二つの projection を持つデータ型を生成する。
- `DecidableEq` — `deriving` により自動生成される等号判定 instance。

FLT5 固有の既存 theorem や packet には直接依存しない。これは意図的で、`GoldenOrder.lean` がそれまでの FLT5 reduction 層とは独立した代数基盤を構築していることを示す。

## 証明・構築の流れ

proof script は存在しない。structure 宣言によって Lean は概念的に次のものを生成する。

1. constructor `GoldenInt.mk : ℤ → ℤ → GoldenInt`
2. projection `GoldenInt.fst : GoldenInt → ℤ`
3. projection `GoldenInt.snd : GoldenInt → ℤ`
4. equality decision procedure `[DecidableEq GoldenInt]`

したがって例えば `⟨a, b⟩ : GoldenInt` は $a+b\varphi$ の座標表現として後続コードで利用できる。

直後には

```lean
def goldenZero : GoldenInt := ⟨0, 0⟩

def goldenOne : GoldenInt := ⟨1, 0⟩
```

が置かれており、0118 の carrier に具体的な環演算を載せ始める。

## Lean 固有の処理

### `structure` を使う理由

単なる `ℤ × ℤ` でも同じ二座標を保持できるが、専用 structure にすることで `fst`, `snd` を意味のある API として固定し、後から `Add`, `Mul`, `Neg`, `Zero`, `One` などの instance を `GoldenInt` 専用に与えられる。

また型そのものが異なるため、通常の整数対と黄金整数座標を Lean が混同しない。

### `deriving DecidableEq`

座標型 `ℤ` には decidable equality があるため、structure の等号判定を自動導出できる。後続の有限的判定や `simp` における具体的等式処理にも使いやすい。

### extensionality

structure equality は最終的に二座標の equality に還元できる。source の後続 theorem では `GoldenInt.ext` を使い、`fst` と `snd` の二目標へ分解して座標ごとに `simp` / `ring` で閉じる形が現れる。

## 冗長・重複箇所

この宣言自体に proof 上の冗長性はほぼない。二座標 carrier と equality 判定だけの最小定義である。

設計レベルでは、数学的には既存の一般的な二次代数型を利用する選択肢があるため、「専用 pair structure を新設すること」は抽象化の重複と見ることもできる。しかし source は、$\mathbb Q(\sqrt5)$ の整数環との field-level isomorphism を先に構築せず、FLT5 に必要な算術だけを監査しやすい座標形式で直接証明する方針を明示している。このため現在の重複はかなり意図的である。

## 最適化候補

### 1. carrier を `ℤ × ℤ` にする

コード量だけを減らすなら type synonym や product を使える。しかし projection の意味、instance の独立性、定理名の可読性が落ちるため、現状の専用 structure の方が proof architecture には適している。

### 2. 一般的な quadratic algebra へ接続する

将来的には `AdjoinRoot` や `QuadraticAlgebra` など Mathlib の一般構造との同型を追加し、この座標モデルで証明した theorem を一般理論へ橋渡しできる可能性がある。

ただしこれは現在の carrier を置換する最適化というより、外部 interoperability の追加である。FLT5 proof の局所性・可読性という観点では、座標モデルを残したまま同型だけを証明する方が安全である。

### 3. named coordinate semantics

`fst`, `snd` は汎用名なので、`a`, `b` 相当の意味を明示する補助 accessor を追加する余地はある。ただし既存 proof が `x.fst`, `x.snd` を広範囲に使うなら rename cost の方が大きい可能性がある。

## 必要 Mathlib import と import 最適化候補

対象 standalone source は冒頭で

```lean
import Mathlib
```

を一括 import している。

しかし `GoldenInt` 宣言単独で直接必要なのは `ℤ`、structure、`DecidableEq` の導出だけであり、Mathlib 全体は明らかに過大である。Lean/Init と整数型を提供する最小 import まで縮小できる可能性が高い。

一方、`GoldenOrder.lean` module 全体では後続に ring structure、`Zsqrtd 5` への写像、`ring` / `simp` を用いる証明などがあるため、module 単位の最小 import は 0118 単独より大きくなる。

本記事では Lean build を実行していないので、具体的な最小 import 集合は未検証である。ここは推測として区別しておく。

## Comparator challenge 化の可否

適している。特に「黄金整数を Lean でどうモデル化するか」は実装比較に向く。

候補は例えば次の三案である。

1. 現行の専用 `structure GoldenInt := (fst snd : ℤ)`。
2. `ℤ × ℤ` を carrier とする軽量実装。
3. Mathlib の一般的な quadratic / adjoin-root 構造を利用する実装。

比較軸は、定義量、`simp` の扱いやすさ、`ring` への接続、norm/conjugation の表現、Euclidean-domain 証明の難易度、FLT5 downstream theorem の短さ、一般数学との interoperability である。

この challenge は「最短コード」を競うより、FLT5 の後続 proof がどの carrier で最も透明になるかを比較するのが有益である。

## 根拠資料と推測の範囲

形式的根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenOrder.lean` generated section である。そこでは `GoldenInt` を $a+b\varphi$ の直接座標モデルとし、$\varphi^2=\varphi+1$ に基づく乗法・共役・ノルムを後続で構築する方針が明記されている。

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし今回は PDF 本文の `GoldenInt` 対応ページを直接照合していないため、ページ番号・節番号や PDF 側の表現は推測していない。

import 最小化案と一般 quadratic algebra への接続案は設計候補であり、現行 source がそれを採用しているという主張ではない。

## 次に読むべき宣言

依存順で直後は

```lean
def goldenZero : GoldenInt := ⟨0, 0⟩
```

である。

これは `GoldenInt` carrier に最初の具体的な環要素 $0$ を与える宣言であり、その次の `goldenOne` とともに黄金整数環の演算 API 構築が始まる。したがって次号は `goldenZero` を読むのが自然である。
