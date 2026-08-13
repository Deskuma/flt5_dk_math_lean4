# 0123 — `goldenSub`

## Lean の型

```lean
def goldenSub (x y : GoldenInt) : GoldenInt := goldenAdd x (goldenNeg y)
```

`goldenSub` は `GoldenInt` 上の減法を、すでに導入済みの加法 `goldenAdd` と加法逆元 `goldenNeg` の合成として定義する。

## 数学的主張

`GoldenInt` を黄金整数

$$
x=a+b\varphi,\qquad y=c+d\varphi,
$$

ただし

$$
\varphi^2=\varphi+1
$$

の座標表示と読むと、

$$
x-y=(a-c)+(b-d)\varphi
$$

である。Lean の定義はこの式を新たに座標展開して書くのではなく、

$$
x-y=x+(-y)
$$

という加法群の標準的な定義をそのまま採用している。

したがって計算上は

```text
goldenSub ⟨a,b⟩ ⟨c,d⟩
  = goldenAdd ⟨a,b⟩ (goldenNeg ⟨c,d⟩)
  = goldenAdd ⟨a,b⟩ ⟨-c,-d⟩
  = ⟨a-c,b-d⟩
```

となる。

## 証明全体での役割

この宣言は FLT5 の数論的核心を直接証明する補題ではなく、後続の黄金整数環 `GoldenInt` の基本演算 API を構成する基礎層に属する。

0118 で carrier `GoldenInt` が導入され、0119 `goldenZero`、0120 `goldenOne`、0121 `goldenAdd`、0122 `goldenNeg` と進んだ後、本宣言で減法が得られる。直後には `goldenMul`、`goldenPow` が続き、さらに `Sub GoldenInt` instance が

```lean
instance : Sub GoldenInt := ⟨goldenSub⟩
```

として登録される。

よって `goldenSub` は raw coordinate API と Lean の標準 `-` 記法を接続する前段であり、後続の環・ノルム・整除・Euclidean-domain 構造を通常の algebraic notation で記述するための部品である。

## 直接依存する定義・補題

直接依存は次の三点である。

1. `GoldenInt`
2. `goldenAdd`
3. `goldenNeg`

証明済み theorem への依存はない。`goldenSub` 自身は `def` であり、証明項ではなく計算定義である。

依存関係は

```text
GoldenInt
  ├─ goldenAdd
  └─ goldenNeg
       ↓
   goldenSub
```

と読める。

## 証明・定義の流れ

本宣言には tactic proof は存在しない。定義右辺を一段ずつ読むだけである。

1. `goldenNeg y` により `y` の二座標を符号反転する。
2. `goldenAdd x (...)` により、その結果を `x` へ座標ごとに加える。
3. したがって数学的には `x + (-y)`、すなわち `x-y` になる。

重要なのは、減法の座標式

$$
\langle a-c,b-d\rangle
$$

を別実装として複製していないことである。加法と負号の正しさ・単純さをそのまま再利用している。

## Lean 固有の処理

### 1. raw operation の合成

この段階ではまだ `Sub GoldenInt` instance を使わず、明示的な関数 `goldenAdd` と `goldenNeg` を使う。したがって typeclass inference に依存せず、定義間の依存が明示されている。

### 2. definitional reduction

`goldenSub` は一行の定義なので、展開すれば `goldenAdd` と `goldenNeg` の座標計算へ還元される。後続の座標 `simp` 補題は、この definitional transparency を利用して非常に短く証明できる可能性が高い。

### 3. 記法との分離

後続で

```lean
instance : Sub GoldenInt := ⟨goldenSub⟩
```

を導入して初めて `x - y` が `GoldenInt` 上で標準記法として使える。この raw definition → typeclass instance という二層構造は `goldenAdd`、`goldenNeg` と同じ設計である。

## 冗長・重複箇所

数学的には

```lean
def goldenSub (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst - y.fst, x.snd - y.snd⟩
```

とも書ける。その意味で、`goldenAdd` と `goldenNeg` を経由する現在の実装は一段間接的である。

しかしこれは不要な重複というより、むしろ座標減法の式を重ねて保持しないための意図的な再利用と見るべきである。加法群では減法を `add + neg` から導くのが標準であり、現在の実装は構造上自然である。

## 最適化候補

### 候補 A — 現状維持

最も明快である。primitive operation を `goldenAdd` と `goldenNeg` に絞り、`goldenSub` は合成として定義する。

### 候補 B — `Sub` instance を直接定義

raw 名 `goldenSub` が下流で直接参照されないなら、

```lean
instance : Sub GoldenInt :=
  ⟨fun x y => goldenAdd x (goldenNeg y)⟩
```

と inline 化できる。ただし定理名・デバッグ表示・博物館上の追跡可能性は低下する。

### 候補 C — 座標式を直接書く

```lean
def goldenSub (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst - y.fst, x.snd - y.snd⟩
```

は一見直接的だが、`goldenAdd` と `goldenNeg` との整合を別途証明・維持する必要が生じうる。現在の合成定義の方が algebraic hierarchy の意図を表している。

## 必要 Mathlib import と import 最適化候補

対象ブランチで確認できる形式ソースは `Flt5DkMath/FLT5StandAlone.lean` であり、standalone 全体は `Mathlib` を利用する構成になっている。一方、リポジトリの `Flt5DkMath` tree には現在 `Basic.lean` と `FLT5StandAlone.lean` しかなく、独立した `GoldenOrder.lean` ファイルは配置されていない。

`goldenSub` 単独が必要とする機能は極めて小さい。`GoldenInt`、整数 `ℤ`、加法・負号と先行定義 `goldenAdd` / `goldenNeg` があれば足りるため、理論上は `Mathlib` 全体を本宣言のためだけに import する必要はない。

ただし最小 import 集合はこの回では Lean build を行っていないため未検証であり、具体的な最小 module 名の断定はしない。

## Comparator challenge 化の可否

**適している。** 小規模だが設計比較が明瞭である。

Comparator challenge としては、次の実装を比較できる。

1. `goldenAdd x (goldenNeg y)` による合成
2. 座標ごとの直接減算
3. `Sub GoldenInt` instance への inline 化

評価軸は、定義の重複量、下流 `simp` の扱いやすさ、algebraic hierarchy との一致、可読性、definitional equality の使いやすさである。

現行案は「primitive を少なく保つ」という観点で有力である。

## 既存資料との対応

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在することを確認した。

ただしこの回では GitHub 経由で PDF 本文中の `goldenSub` 対応ページを直接抽出できなかったため、PDF のページ番号・節番号・文章内容について推測は行わない。形式的内容の根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` 内 `GoldenOrder.lean` generated section とする。

## 次に読むべき宣言

次は

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

である。

これは `GoldenInt` の最初の非自明な演算であり、関係式

$$
\varphi^2=\varphi+1
$$

を実際に座標計算へ反映する。`goldenSub` までの加法構造は単なる `ℤ^2` の座標演算だったが、`goldenMul` から初めて黄金整数環固有の二次関係が現れる。したがって次号 0124 では `goldenMul` を読むのが依存順として自然である。
