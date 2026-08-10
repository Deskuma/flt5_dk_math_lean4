# 0101 — `SquareGoldenN`

## Lean の型

```lean
def SquareGoldenN (z y : ℕ) : ℤ :=
  (z : ℤ) * (y : ℤ)
```

## 数学的主張

`SquareGoldenN` は theorem ではなく、`SquareGoldenNormalForm.lean` の第二の座標定義である。

自然数 `z,y` から整数

$$
N=zy
$$

を作る。Lean では積を整数世界で固定するため、右辺は

```lean
(z : ℤ) * (y : ℤ)
```

と書かれている。

0100 `SquareGoldenM` が endpoint-square mass

$$
M=z^2+y^2
$$

を与えるのに対し、本定義は endpoint cross-beam

$$
N=zy
$$

を与える。以後の square/golden normal form はこの対 $(M,N)$ を基本座標として使う。

## 証明全体での役割

0093–0099 の `SquareGoldenBridge.lean` では、黄金ノルムへ移る座標として

$$
M=(g+y)^2+y^2,\qquad N=(g+y)y
$$

が式の中へ直接埋め込まれていた。

`SquareGoldenNormalForm.lean` では endpoint を一般に `z,y` と書き直し、0100 と本定義によって

$$
M:=\mathrm{SquareGoldenM}(z,y)=z^2+y^2,
$$

$$
N:=\mathrm{SquareGoldenN}(z,y)=zy
$$

を名前付き API にする。

この $N$ は単なる積ではなく、後続の四つの保存量すべてに現れる第二座標である。

$$
M-2N,
$$

$$
M^2-4N^2,
$$

$$
\mathrm{GoldenNorm}(M,N),
$$

$$
(2M+N)^2-5N^2.
$$

したがって `SquareGoldenN` は平方世界と黄金比型二次形式を接続する cross term の担い手である。

## 直接依存する定義・補題

project-local な直接依存はない。定義そのものは次だけを利用する。

1. `ℕ` と `ℤ`。
2. 自然数から整数への coercion `(z : ℤ)`、`(y : ℤ)`。
3. 整数の乗法。

概念上は 0096 `GN5_eq_goldenNorm_squareLink` に現れた第二座標

$$
(g+y)y
$$

を一般 endpoint 座標 $zy$ として再命名したものと読める。ただしこれは source 上の直接依存ではなく、proof architecture 上の対応である。

## 証明の流れ

`def` なので theorem proof は存在しない。Lean が行うのは定義展開だけである。

```lean
SquareGoldenN z y
```

を unfold すると

```lean
(z : ℤ) * (y : ℤ)
```

になる。

この簡単な定義を独立させる意味は計算を短くすることより、後続 theorem の statement を同じ座標語彙で統一することにある。

## Lean 固有の処理

### 1. 戻り値を最初から `ℤ` にしている

入力は `ℕ` だが、出力は `ℤ` である。これにより後続で

$$
M-2N
$$

や

$$
M^2-4N^2
$$

のような減法を自然に扱える。

もし `SquareGoldenN : ℕ → ℕ → ℕ` としていたなら、後続の subtraction で `Nat.sub` の切り捨て問題を避けるための条件や cast が余計に必要になる。

### 2. cast の位置を API 境界で固定している

```lean
(z : ℤ) * (y : ℤ)
```

と定義時点で cast しているため、利用者側では毎回 coercion を書かず `SquareGoldenN z y` とだけ記述できる。

### 3. definitional reduction が使える

`SquareGoldenN` は opaque theorem ではなく `def` なので、`unfold SquareGoldenN` や `simp [SquareGoldenN]` によって積へ戻せる。直後の `squareGolden_tenth_boundary_base` も `SquareGoldenM` と `SquareGoldenN` を unfold してから `ring` で閉じる。

## 冗長・重複箇所

式 $zy$ 自体はすでに 0096 の

```lean
↑((g + y) * y) : ℤ
```

として現れている。したがって計算式だけを見れば、本定義は既存式の再包装である。

しかし重複は意図的と考えるのが自然である。0096 は `GN5` から `GoldenNorm` への bridge theorem であり、ここでは `SquareGoldenNormalForm` の公共座標 API を作っている。つまり同じ式でも役割が異なる。

また 0100 `SquareGoldenM` と本定義は常に対で現れるため、二つの独立した関数として持つことには少量の boilerplate がある。

## 最適化候補

### 候補 A — 座標対を structure 化する

例えば概念的には

```lean
structure SquareGoldenCoords where
  M : ℤ
  N : ℤ
```

のような carrier を作り、`z,y` から一度に構成する設計が考えられる。

これにより後続 theorem で `SquareGoldenM z y` と `SquareGoldenN z y` を繰り返す箇所は減る。一方、現在の二関数方式は unfold が単純で、各定理の statement も完全に明示的である。したがって必ずしも structure 化が優位とは限らない。

### 候補 B — 共通 endpoint coordinate constructor

`SquareGoldenM` と `SquareGoldenN` を pair

```lean
(SquareGoldenM z y, SquareGoldenN z y)
```

として返す小さな constructor を追加する案もある。既存 API を壊さずに、後続の bundle 化だけを進められる。

### 候補 C — 現状維持

本定義は一行で、展開も予測可能である。proof audit の観点では、過度な抽象化を避けて $M=z^2+y^2$, $N=zy$ を直接見せる現在の形は強い。現段階では最も保守的で合理的な選択である。

## 必要 Mathlib import と import 最適化候補

standalone artifact はファイル全体として

```lean
import Mathlib
```

を使用している。

しかし `SquareGoldenN` 単独では、自然数・整数・`Nat` から `Int` への coercion・整数乗法しか使わない。そのため `import Mathlib` は本定義だけに対しては大幅に広い。

一方 `SquareGoldenNormalForm.lean` 全体では、直後から `ring`、`exact_mod_cast`、既存 FLT5 theorem 群などを利用する。したがって module 単位の最小 import 集合は Lean build による検証なしには断定しない。

import 最適化を行うなら、まず project-local 依存を明示した source module を復元し、そのうえで `Mathlib` umbrella import を段階的に狭め、各段階で build を通すのが安全である。本回では build は行っていない。

## Comparator challenge 化の可否

可能。ただし theorem proving challenge というより API design challenge が適している。

比較案は次の三方式である。

1. 現在の独立関数 `SquareGoldenM` / `SquareGoldenN`。
2. pair を返す constructor。
3. `SquareGoldenCoords` structure。

評価軸は、後続 theorem の statement 長、unfold の容易さ、`simp` の挙動、cast の局所化、proof audit の読みやすさである。

また小さな Lean challenge として

```lean
example (z y : ℕ) :
    SquareGoldenN z y = (z : ℤ) * (y : ℤ) := by
  rfl
```

を出し、definitionally true な statement に `rfl` が使えることを確認する課題にもできる。

## 次に読むべき定理

Lean source で直後に置かれているのは

```lean
theorem squareGolden_tenth_boundary_base (z y : ℕ) :
    SquareGoldenM z y - 2 * SquareGoldenN z y =
      ((z : ℤ) - (y : ℤ)) ^ 2 := by
  unfold SquareGoldenM SquareGoldenN
  ring
```

である。

これは 0100 と 0101 で用意した二座標を初めて同時に使用し、

$$
M-2N=z^2+y^2-2zy=(z-y)^2
$$

という平方境界を取り出す。

したがって次号は `squareGolden_tenth_boundary_base` を読むのが依存順として自然である。

## 根拠と注記

形式的根拠は `docs/flt5-theorem-museum` ブランチの generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` に含まれる `SquareGoldenNormalForm.lean` 区間である。

standalone の manifest は元 source を `DkMath/FLT/Five/SquareGoldenNormalForm.lean` と記録しているが、このパスは本ブランチ上で直接取得できなかったため、元分割ファイルの現在内容については断定しない。generated artifact に収録された Lean code を一次的な形式根拠として扱う。

既存日本語・英語 PDF の本宣言に対する具体的なページ対応は本回では確認できていない。そのため PDF の節番号・ページ番号・叙述対応を推測で補ってはいない。