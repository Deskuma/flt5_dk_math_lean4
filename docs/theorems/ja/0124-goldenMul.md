# 0124 — `goldenMul`

## Lean の型

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

`goldenMul` は `GoldenInt` 上の乗法を、基底関係

$$
\varphi^2=\varphi+1
$$

で二次項を還元した座標積として定義する。

## 数学的主張

`GoldenInt` の二要素を

$$
x=a+b\varphi,\qquad y=c+d\varphi
$$

とする。通常の分配法則で積を展開すると、

$$
xy=ac+(ad+bc)\varphi+bd\varphi^2
$$

である。ここで黄金比の defining relation

$$
\varphi^2=\varphi+1
$$

を代入すると、

$$
xy=(ac+bd)+(ad+bc+bd)\varphi
$$

となる。したがって座標では

$$
(a,b)(c,d)=(ac+bd,\ ad+bc+bd)
$$

であり、Lean の定義はこの式をそのまま実装している。

第一座標の `x.fst * y.fst + x.snd * y.snd` は $ac+bd$、第二座標の `x.fst * y.snd + x.snd * y.fst + x.snd * y.snd` は $ad+bc+bd$ に対応する。

## 証明全体での役割

0118 `GoldenInt` から 0123 `goldenSub` までに導入された零元・単位元・加法・負号・減法は、ほぼ `ℤ × ℤ` の加法構造として理解できた。本宣言 `goldenMul` で初めて、黄金整数環固有の二次関係

$$
\varphi^2=\varphi+1
$$

が演算そのものへ埋め込まれる。

この乗法は後続で

```lean
instance : Mul GoldenInt := ⟨goldenMul⟩
```

として Lean の標準乗法 `x * y` に接続される。また `goldenPow` の再帰ステップ、`CommRing GoldenInt` の構築、共役 `goldenConj`、ノルム `goldenNorm`、ノルムの乗法性、整除、単元、Euclidean-domain 構造、最終的な fifth-power extraction の全てがこの積に依存する。

したがって `goldenMul` は `GoldenInt` を単なる整数対から黄金整数環 `ℤ[φ]` へ変える中心的 primitive operation である。

## 直接依存する定義・補題

直接依存は非常に少ない。

1. `GoldenInt`
2. `Int` 上の加法と乗法
3. 黄金基底の意味づけとしての関係式 $\varphi^2=\varphi+1$

ただし 3 は Lean の theorem を右辺で呼び出しているわけではない。関係式を展開済みの座標公式として **定義そのものへコンパイルしている**。

`goldenAdd`、`goldenNeg`、`goldenSub` には直接依存しない。

## 証明・定義の流れ

本宣言は `def` なので tactic proof はない。数学的導出は次の通りである。

1. `x = a+bφ`、`y = c+dφ` と読む。
2. 積を $ac+(ad+bc)φ+bdφ^2$ と展開する。
3. $φ^2=φ+1$ を適用する。
4. 定数成分を $ac+bd$ にまとめる。
5. $φ$ 成分を $ad+bc+bd$ にまとめる。
6. 二つの整数を `GoldenInt` の `fst` / `snd` に格納する。

Lean ではこの導出を毎回証明するのではなく、最終座標式を primitive multiplication として採用する。

## Lean 固有の処理

### 1. structure projection による座標演算

`x.fst`、`x.snd`、`y.fst`、`y.snd` を直接使うため、積の実装は完全に明示的である。抽象的な quotient や algebra extension の reduction machinery は使っていない。

### 2. 期待型による constructor 推論

右辺の

```lean
⟨..., ...⟩
```

は期待型 `GoldenInt` から `GoldenInt.mk` と推論される。

### 3. defining relation のコンパイル

`φ^2 = φ + 1` は theorem rewrite として実行されない。すでに還元された座標公式を定義しているため、`goldenMul` の評価自体に `rw` や `ring` は不要である。

一方、後続の結合律・分配律・ノルム乗法性などでは、この座標定義を `simp [goldenMul]` で展開した後、`ring` による整数多項式正規化が有効になる。

### 4. raw API と typeclass API の分離

この時点では `goldenMul x y` という明示関数であり、後続の `Mul GoldenInt` instance により `x * y` へ接続される。この二層設計は `goldenAdd` などと同じである。

## 冗長・重複箇所

座標式

$$
(ac+bd,\ ad+bc+bd)
$$

は後続の環法則を証明する際に何度も展開される。その意味では、`simp [goldenMul] <;> ring` 型の証明が繰り返される可能性がある。

ただし `goldenMul` 自身の定義には実質的な重複はない。第一・第二座標は `φ^2=φ+1` によって一意に得られる最小の coordinate formula である。

後続で `golden_mul_eq` が

```lean
@[simp] theorem golden_mul_eq (x y : GoldenInt) : goldenMul x y = x * y := rfl
```

として導入されるため、raw function と typeclass notation の二重 API は存在する。これは冗長というより、定義追跡と標準代数記法を両立するための意図的な duplication と見るのが自然である。

## 最適化候補

### 候補 A — 現状維持

最も透明である。`ℤ[φ]` の乗法が座標から即座に読め、後続の `ring` ベース証明とも相性がよい。

### 候補 B — `Mul GoldenInt` instance へ直接 inline

```lean
instance : Mul GoldenInt :=
  ⟨fun x y =>
    ⟨x.fst * y.fst + x.snd * y.snd,
      x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩⟩
```

とできるが、`goldenMul` という明示名を失い、後続 theorem の statement やデバッグ時の追跡性が低下する。

### 候補 C — 一般二次環の共通実装

一般に $θ^2=pθ+q$ を満たす二次基底について

$$
(a,b)(c,d)=(ac+qbd,\ ad+bc+pbd)
$$

という generic coordinate multiplication を用意し、$p=q=1$ として `GoldenInt` を特殊化する方法もある。

再利用性は高いが、FLT5 専用コードとしては抽象化コストが増す。Comparator ではこの trade-off を評価できる。

### 候補 D — `AdjoinRoot` / quadratic algebra への移行

Mathlib の二次代数構造を用いて `φ` を多項式 $X^2-X-1$ の根として扱えば、defining relation を構造側へ委譲できる可能性がある。しかし現在の explicit coordinate model は計算・`ring`・norm の追跡が非常に直接的であり、形式証明の局所透明性では強い。

## 必要 Mathlib import と import 最適化候補

対象ブランチで形式的根拠として確認できる `Flt5DkMath/FLT5StandAlone.lean` は standalone 全体として `Mathlib` を利用する。一方、`goldenMul` 単独に必要なのは `GoldenInt`、整数型 `ℤ`、整数の `+` と `*`、structure constructor / projection 程度である。

したがってこの一宣言だけを理由に `Mathlib` 全体を import する必要はない。後続で `ring`、`norm_num`、`Zsqrtd`、Euclidean-domain 構造などを利用するため、`GoldenOrder` module 全体ではより広い import が必要になる。

具体的な最小 Mathlib module 集合は、この回では Lean build を行っていないため未検証であり断定しない。

## Comparator challenge 化の可否

**非常に適している。** `GoldenInt` の設計方針を比較する代表的な課題にできる。

比較候補は次の通りである。

1. 現行の explicit coordinate multiplication
2. 一般二次環 $θ^2=pθ+q$ の generic multiplication から特殊化
3. `AdjoinRoot (X^2-X-1)` など既存 algebraic structure を利用
4. `ℤ × ℤ` を carrier として multiplication だけ定義

評価軸は、定義の透明性、`rfl` / `simp` の強さ、`ring` tactic との相性、Mathlib import の大きさ、後続 norm / conjugation / Euclidean proof の容易さ、数学的再利用性である。

FLT5 の証明工程だけを見るなら、現行 explicit formula はかなり強い選択である。

## 既存資料との対応

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。

この回では PDF 本文の `goldenMul` 対応ページを直接解析していないため、PDF のページ番号・節番号・固有の説明は推測しない。形式的内容の最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` 内 `GoldenOrder.lean` generated section とする。

## 次に読むべき宣言

次は

```lean
def goldenPow (x : GoldenInt) : ℕ → GoldenInt
  | 0 => goldenOne
  | n + 1 => goldenMul (goldenPow x n) x
```

である。

これは 0120 `goldenOne` と本号 0124 `goldenMul` を再帰的に合成して自然数冪を定義する。後続では `Pow GoldenInt ℕ` / `CommRing GoldenInt` の冪 API に接続され、さらに fifth-power extraction で `goldenPow gamma 5` が直接現れる。

したがって次号 0125 では `goldenPow` を読むのが依存順として自然である。
