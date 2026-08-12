# 0100 — `SquareGoldenM`

## Lean の型

```lean
def SquareGoldenM (z y : ℕ) : ℤ :=
  (z : ℤ) ^ 2 + (y : ℤ) ^ 2
```

## 数学的主張

`SquareGoldenM` は theorem ではなく、`SquareGoldenNormalForm.lean` の最初に置かれた座標定義である。

自然数 `z,y` から整数

$$
M=z^2+y^2
$$

を作る。ここで平方計算は定義上 `ℤ` で行われるため、Lean の右辺は

```lean
(z : ℤ) ^ 2 + (y : ℤ) ^ 2
```

となっている。

数学的には endpoint-square mass coordinate、すなわち二つの endpoint の平方和を一つの名前付き座標 `M` にまとめたものである。

## 証明全体での役割

0093–0099 の `SquareGoldenBridge.lean` では、`GN5` を黄金比型二次形式へ移す際に

$$
M=(g+y)^2+y^2,\qquad N=(g+y)y
$$

という式を直接書いていた。

新しい `SquareGoldenNormalForm.lean` では、その endpoint-square 側の第一座標を

$$
M:=\mathrm{SquareGoldenM}(z,y)=z^2+y^2
$$

として名前付き API に昇格させる。

これにより後続の normal form は長い式を反復せず、

$$
\mathrm{GoldenNorm}(M,N),\qquad M-2N,\qquad M^2-4N^2,\qquad (2M+N)^2-5N^2
$$

という複数の保存量を同じ座標対 `(M,N)` 上で記述できる。

特に直後の `squareGolden_tenth_boundary_base` では

$$
M-2N=(z-y)^2
$$

が示され、`squareGolden_square_discriminant` では

$$
M^2-4N^2=(z^2-y^2)^2
$$

が示される。したがって `SquareGoldenM` は、黄金ノルムと平方境界を同じ座標系へ束ねるための第一成分である。

## 直接依存する定義・補題

project-local な直接依存はない。定義そのものは次だけを利用する。

1. `ℕ` と `ℤ`。
2. 自然数から整数への coercion `(z : ℤ)`、`(y : ℤ)`。
3. 整数の加法。
4. 整数の冪 `^ 2`。

概念上の先行依存としては 0096 `GN5_eq_goldenNorm_squareLink` が重要である。そこですでに同じ形の endpoint-square 座標が出現しており、本定義はその式を後続 normal form 用に再命名している。

## 証明の流れ

`def` なので証明 script は存在しない。Lean は

```lean
def SquareGoldenM (z y : ℕ) : ℤ :=
  (z : ℤ) ^ 2 + (y : ℤ) ^ 2
```

をそのまま definitional equality として登録する。

後続では `unfold SquareGoldenM`、`simp [SquareGoldenM]`、あるいは `simpa [SquareGoldenM, ...]` によって右辺へ展開できる。

## Lean 固有の処理

最も重要なのは codomain を最初から `ℤ` にしている点である。

入力は `z y : ℕ` だが、後続では

$$
M-2N
$$

や

$$
M^2-4N^2
$$

のような減法を自然に扱う。これを `ℕ` 上で定義すると truncated subtraction の問題が入り、平方・黄金ノルム側との接続も煩雑になる。

そこで入口で `z,y` を整数へ cast し、座標そのものを `ℤ` に固定している。この選択により後続の `GoldenNorm : ℤ → ℤ → ℤ` と型が直接一致する。

また `abbrev` ではなく `def` なので、通常の simplifier が常時展開する transparent alias よりも、名前付き抽象境界として扱いやすい。

## 冗長・重複箇所

式

$$
z^2+y^2
$$

自体は 0096 `GN5_eq_goldenNorm_squareLink`、0098 `endpoint_square_discriminant` などですでに現れている。

したがって計算内容だけ見れば重複である。しかし本定義の目的は新しい恒等式ではなく、`SquareGoldenNormalForm` 層で共有する coordinate vocabulary を導入することである。

この重複は proof architecture 上は意図的であり、後続 structure の field 型を短くし、同じ `M` を黄金ノルム・tenth boundary・square discriminant・discriminant-five の四系統で共有できる利点がある。

## 最適化候補

1. 現状維持。小さな名前付き座標として十分に有効。
2. `SquareGoldenM` と直後の `SquareGoldenN` を一つの coordinate structure にまとめる。例えば `SquareGoldenCoords` に `M N : ℤ` を持たせれば、二変数を常に対として扱える。
3. `SquareGoldenM` をより一般的な整数入力 `(z y : ℤ)` にする。ただし現 proof graph は自然数の FLT データから入るため、現行の `ℕ → ℤ` 境界が provenance を明確にしている。
4. 0096 の endpoint-square 式も本定義を利用するよう再編する。ただし `SquareGoldenM` は後続 module で定義されるため、依存方向を逆転させるには module 分割の変更が必要になる。
5. `abbrev` 化は可能だが、後続で意図せず展開されやすくなるので、必ずしも改善ではない。

## 必要 Mathlib import と import 最適化候補

対象 standalone artifact は `import Mathlib` を使用している。

本定義単独が必要とする機能は非常に小さく、自然数・整数、coercion、加法、冪だけである。したがって umbrella `Mathlib` はこの一宣言だけを見る限り明らかに過大である。

ただし分割元 `SquareGoldenNormalForm.lean` の後続 theorem では `ring`、`exact_mod_cast`、`simpa` などを利用するため、module 全体の最小 import 集合は Lean build を行わずには断定しない。少なくとも「`SquareGoldenM` 自身のために `Mathlib` 全体が必要」ということはない。

import 最適化を行うなら、まず `SquareGoldenNormalForm.lean` 単体で実際に使用される tactic と整数 API を列挙し、`Mathlib.Tactic.Ring` 等へ縮小できるか build で検証するのが安全である。

## Comparator challenge 化の可否

単独では challenge としては弱い。これは証明問題ではなく API 設計問題だからである。

ただし「座標設計 Comparator」としては有用で、次を比較できる。

1. 現行の独立した `SquareGoldenM` / `SquareGoldenN` 定義。
2. `(ℤ × ℤ)` を返す一つの関数。
3. `structure SquareGoldenCoords` による named fields。
4. 入力を `ℕ` のまま保持し、使用時に cast する設計。
5. 入力段階で `ℤ` に持ち上げる現行設計。

評価軸は、後続 theorem の可読性、cast の量、rewrite のしやすさ、proof graph の provenance、normal form structure の簡潔さである。

## 既存資料との対応

形式的な最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` である。generated source marker により、本定義が `DkMath/FLT/Five/SquareGoldenNormalForm.lean` の最初の宣言であり、直前の module が `SquareGoldenBridge.lean` であることを確認した。

standalone manifest でも `SquareGoldenBridge.lean` の直後に `SquareGoldenNormalForm.lean` が配置されている。

既存の日英 PDF については、今回 GitHub code search が upstream 502 を返したため具体的なページ・節番号を確認できなかった。したがって PDF 上の対応位置は推測で補っていない。

## 次に読むべき定理

依存順で直後の宣言は第二座標

```lean
def SquareGoldenN (z y : ℕ) : ℤ :=
  (z : ℤ) * (y : ℤ)
```

である。

したがって次号 0101 は `SquareGoldenN` を読むのが自然である。その後、二座標を同時に使う最初の theorem

```lean
theorem squareGolden_tenth_boundary_base (z y : ℕ) :
    SquareGoldenM z y - 2 * SquareGoldenN z y =
      ((z : ℤ) - (y : ℤ)) ^ 2 := by
  unfold SquareGoldenM SquareGoldenN
  ring
```

へ進む。