# 0131 — `instance : Sub GoldenInt`

## Lean の型

```lean
instance : Sub GoldenInt := ⟨goldenSub⟩
```

これは theorem ではなく、0123 で定義した raw operation `goldenSub` を Lean / Mathlib 標準の減算型クラス `Sub` に登録する匿名 instance である。

## 数学的主張

`GoldenInt` を

$$
x=a+b\varphi,\qquad y=c+d\varphi
$$

と読むと、0123 の `goldenSub` は

$$
x-y=(a-c)+(b-d)\varphi
$$

を表す。実装上は座標減算を直接重複記述せず、

```lean
def goldenSub (x y : GoldenInt) : GoldenInt :=
  goldenAdd x (goldenNeg y)
```

すなわち

$$
x-y=x+(-y)
$$

として構成されている。本 instance はこの raw operation を標準記法 `x - y` へ接続する。

## 証明全体での役割

`GoldenOrder` 層では、まず `goldenZero`、`goldenOne`、`goldenAdd`、`goldenNeg`、`goldenSub`、`goldenMul`、`goldenPow` という座標演算を定義し、その後で Lean 標準の algebra typeclass に順次登録している。本宣言は `Zero`、`One`、`Add`、`Neg` に続く減算 API の境界である。

これにより、後続の `AddCommGroup GoldenInt` や `CommRing GoldenInt`、および黄金整数上の恒等式で raw 名 `goldenSub x y` を露出させず、通常の `x - y` を用いられる。

## 直接依存する定義・補題

直接依存は次の三点である。

- `GoldenInt`
- `goldenSub`
- Lean 標準の `Sub` 型クラス

`goldenSub` の内部では 0121 `goldenAdd` と 0122 `goldenNeg` に依存するため、依存グラフとしては

$$
\texttt{goldenAdd},\ \texttt{goldenNeg}
\longrightarrow
\texttt{goldenSub}
\longrightarrow
\texttt{Sub GoldenInt}
$$

となる。本 instance 自体は新しい数学補題を要求しない。

## 証明・構築の流れ

証明 script は存在しない。`Sub GoldenInt` が要求する減算関数へ `goldenSub` を渡すだけである。

```lean
instance : Sub GoldenInt := ⟨goldenSub⟩
```

概念的には

$$
\text{raw coordinate subtraction}
\longrightarrow
\text{standard Lean subtraction notation}
$$

という一段の interface registration である。

## Lean 固有の処理

`⟨goldenSub⟩` は期待型 `Sub GoldenInt` から structure constructor を推論する。登録後、`x - y` は typeclass resolution によりこの instance を参照し、定義的に `goldenSub x y` へ展開される。

したがって座標射影に関する後続補題は、設計次第では `rfl` または軽い `simp` で閉じられる。ここでは theorem rewrite を介して減算記法を実装しているのではなく、notation と raw function が definitional に接続されている点が重要である。

## 冗長・重複箇所

`goldenSub` と `Sub GoldenInt` は意味だけ見れば同じ減算を二層で表すため API-level の重複がある。ただし役割は異なる。

- `goldenSub` は typeclass 構築前でも使える bootstrap 用 raw operation。
- `Sub GoldenInt` は Mathlib の標準 algebra API と記法へ参加するための公開 interface。

また `goldenSub` 自体が `goldenAdd x (goldenNeg y)` として定義されているので、座標式を再記述する数学的重複は既に避けられている。

## 最適化候補

候補は三つある。

1. `Sub` instance に `fun x y => goldenAdd x (goldenNeg y)` を直接書き、`goldenSub` を削除する。
2. `Add` と `Neg` の instance 登録後なら `fun x y => x + (-y)` と書き、標準 API のみで定義する。
3. 現行のように raw operation を残し、typeclass bootstrap と downstream notation を明確に分離する。

現行方式は一見一段多いが、定義順の循環を避けやすく、raw coordinate layer と algebra interface layer の境界も明瞭である。最適化はコード行数より、この definitional transparency を維持できるかで評価すべきである。

## 必要な Mathlib import と import 最適化候補

standalone source は全体として `import Mathlib` を利用している。しかし本 instance 自身は Mathlib の高度な定理を直接使用せず、必要なのは `GoldenInt`、`goldenSub` と標準 `Sub` interface だけである。

したがって modular source では、本宣言のためだけに `Mathlib` 全体を import する必要はないと考えられる。実際の最小 import は上流の `GoldenOrder` 定義群が要求する import に支配される。Lean build は今回行わないため、最小 import 集合そのものは未検証であり、ここは推測として扱う。

## Comparator challenge 化の可否

適している。比較課題としては、次の三方式を同じ downstream lemma 群に対して評価できる。

- raw `goldenSub` + `Sub` instance
- `x + (-y)` を直接 instance に登録
- 座標差 `⟨x.fst-y.fst, x.snd-y.snd⟩` を直接 instance に登録

比較軸は、`rfl` で閉じる補題数、simp 正規形、依存循環の有無、定義展開の読みやすさ、`AddCommGroup` 構築時の proof burden である。小さい宣言ながら、Lean における「定義的等価性をどこに置くか」を比較する良い Comparator challenge になる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum` ブランチの `Flt5DkMath/FLT5StandAlone.lean` 内 `GoldenOrder.lean` generated section である。既存の日英 PDF は叙述上の補助資料だが、本 instance に対応する具体的ページは今回直接照合していない。そのため PDF のページ番号・節番号については推測しない。

## 次に読むべき宣言

依存順の次は

```lean
instance : Mul GoldenInt := ⟨goldenMul⟩
```

である。0131 までで標準的な加法・否定・減算 API が揃い、次は 0124 `goldenMul` を標準乗法 `x * y` へ接続する。ここから `GoldenInt` 固有の関係 $\varphi^2=\varphi+1$ を埋め込んだ乗法が Mathlib の環 API に参加する。
