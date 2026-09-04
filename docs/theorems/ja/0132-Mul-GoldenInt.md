# 0132 — `instance : Mul GoldenInt`

## Lean の型

```lean
instance : Mul GoldenInt := ⟨goldenMul⟩
```

これは theorem ではなく、0124 で定義された raw operation `goldenMul` を Lean / Mathlib 標準の乗法型クラス `Mul` に登録する匿名 `instance` である。

## 数学的主張・宣言の意味

`GoldenInt` を $x=a+b\varphi$, $y=c+d\varphi$ と読み、生成元が $\varphi^2=\varphi+1$ を満たすとする。上流の `goldenMul` は

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

で定義されている。これは

$$
(a+b\varphi)(c+d\varphi)=ac+(ad+bc)\varphi+bd\varphi^2
$$

に $\varphi^2=\varphi+1$ を代入して得られる

$$
(a+b\varphi)(c+d\varphi)=(ac+bd)+(ad+bc+bd)\varphi
$$

を座標で実装したものである。本宣言は、この黄金整数固有の raw multiplication を標準記法 `x * y` に接続する。

## 証明全体での役割

`GoldenOrder` 層では、`goldenZero`、`goldenOne`、`goldenAdd`、`goldenNeg`、`goldenSub`、`goldenMul`、`goldenPow` という raw coordinate API を先に定義し、その後で Lean 標準の `Zero`、`One`、`Add`、`Neg`、`Sub`、`Mul` へ順に登録している。

本宣言はこの primitive operation registration の最後に位置する。これにより、後続の座標 simp 補題、`AddCommGroup GoldenInt`、`CommRing GoldenInt`、共役、ノルム、整除、Euclidean-domain 構造、第五冪分解などで、専用名 `goldenMul x y` を露出させず通常の `x * y` を使用できる。

特に重要なのは、抽象的な環構造を先に仮定するのではなく、黄金整数の座標乗法を明示したうえで標準 algebra interface へ接続している点である。後続の環法則がどの具体的演算に対して証明されているかを追跡しやすい。

## 直接依存する定義・補題

直接依存は次の三点である。

- `GoldenInt`
- 0124 `goldenMul`
- Lean 標準の `Mul` 型クラス

数学的な二次還元 $\varphi^2=\varphi+1$ は `goldenMul` の定義式に既に組み込まれているため、本 `instance` 自体は新しい代数補題を必要としない。

依存関係は概念的に

$$
\texttt{GoldenInt}\longrightarrow\texttt{goldenMul}\longrightarrow\texttt{Mul GoldenInt}
$$

である。

## 証明・構築の流れ

証明 script は存在しない。

```lean
instance : Mul GoldenInt := ⟨goldenMul⟩
```

という structure literal により、`Mul GoldenInt` が要求する二項演算へ `goldenMul` をそのまま渡す。概念的には raw golden-coordinate multiplication を standard Lean multiplication notation へ登録する一段の interface boundary である。

## Lean 固有の処理

`Mul` は乗法演算を保持する typeclass であり、`⟨goldenMul⟩` は期待型 `Mul GoldenInt` から constructor と field を推論して構築される。

この instance が登録された後、`x * y` は typeclass resolution によりこの乗法を選択し、定義的に `goldenMul x y` へ展開される。そのため後続の source にある

```lean
@[simp] theorem golden_fst_mul (x y : GoldenInt) :
    (x * y).fst = x.fst * y.fst + x.snd * y.snd := rfl

@[simp] theorem golden_snd_mul (x y : GoldenInt) :
    (x * y).snd = x.fst * y.snd + x.snd * y.fst + x.snd * y.snd := rfl
```

は theorem-level rewrite を挟まず `rfl` で閉じる。この definitional transparency は後続の simp 正規化にも有利である。

## 冗長・重複箇所

`goldenMul` と `Mul GoldenInt` は同じ乗法を二つの API 層で表すため、表面的には重複している。しかし役割は異なる。

- `goldenMul` は typeclass 構築前にも参照できる bootstrap 用の raw operation。
- `Mul GoldenInt` は `*` 記法と Mathlib の一般 algebra API に参加するための標準 interface。

また、黄金比関係 $\varphi^2=\varphi+1$ の還元済み座標式を `goldenMul` に一度だけ置くことで、後続で同じ代数展開を繰り返す重複を避けている。

## 最適化候補

候補は次の四系統である。

1. `Mul` instance に座標式を直接 inline し、`goldenMul` を削除する。
2. 現行どおり raw operation と typeclass layer を分離し、bootstrap の見通しを優先する。
3. 一般の二次関係 $\theta^2=p\theta+q$ に対する座標乗法を抽象化し、黄金整数を $p=q=1$ の特殊化として構成する。
4. `AdjoinRoot` や quadratic algebra 系の既存 Mathlib infrastructure に寄せ、一般的な環構造を再利用する。

現行方式はコード行数だけを見れば最小ではないが、座標計算が完全に可視で、後続の多くの補題を定義的等価性で処理できる利点がある。FLT5 の証明監査という目的では、この透明性を維持する価値が高い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本宣言単独が直接必要とするのは `GoldenInt`、`goldenMul`、標準 `Mul` interface であり、高度な Mathlib theorem は使用しない。

したがって modular source では、本 `instance` のためだけに `Mathlib` 全体を import する必要はないと考えられる。ただし `GoldenOrder` モジュール全体では整数演算、ring 構造、後続の algebra instance 構築なども利用するため、実際の最小 import はそれらの依存に支配される。今回は Lean build を行わないため、最小 import 集合は未検証であり、この部分は最適化候補としての推測である。

## Comparator challenge 化の可否

適している。比較候補として次の三方式を用意できる。

- raw `goldenMul` + `Mul` instance
- `Mul` instance への座標式直接 inline
- 一般 quadratic-order / `AdjoinRoot` ベース実装

比較軸は、`rfl` で閉じる座標補題数、`CommRing` 構築時の proof burden、simp 正規形、定義展開の読みやすさ、一般化可能性、下流 FLT5 theorem のコード量である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/GoldenOrder.lean` generated section である。source では `Sub GoldenInt` の直後に本 `Mul GoldenInt` が置かれ、その次に `golden_fst_zero` などの `@[simp]` 座標補題群が続く。

対象ブランチには日本語・英語 PDF も存在するが、本匿名 instance に対応する具体的ページは今回直接特定していない。そのため PDF のページ番号・節番号は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
@[simp] theorem golden_fst_zero : (0 : GoldenInt).fst = 0 := rfl
```

である。0127–0132 で `Zero`、`One`、`Add`、`Neg`、`Sub`、`Mul` の標準 typeclass registration が揃った。次からは、これらの標準記法が raw 座標定義へ定義的に落ちることを `@[simp]` 補題として公開する段階へ進む。
