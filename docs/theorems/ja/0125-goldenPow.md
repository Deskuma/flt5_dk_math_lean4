# 0125 — `goldenPow`

## Lean の型

```lean
def goldenPow (x : GoldenInt) : ℕ → GoldenInt
  | 0 => goldenOne
  | n + 1 => goldenMul (goldenPow x n) x
```

`goldenPow` は `GoldenInt` 上の自然数冪を、0120 `goldenOne` と 0124 `goldenMul` から直接再帰で定義する。

## 数学的主張

数学的には通常の自然数冪

$$
x^0=1,
$$

$$
x^{n+1}=x^n x
$$

を黄金整数上で定義している。

`GoldenInt` を $a+b\varphi$、$\varphi^2=\varphi+1$ の座標モデルと読むと、`goldenPow x n` はその要素を `goldenMul` で $n$ 回掛け合わせたものになる。

たとえば定義から直接、

$$
\operatorname{goldenPow}(x,0)=\operatorname{goldenOne},
$$

$$
\operatorname{goldenPow}(x,1)=\operatorname{goldenMul}(\operatorname{goldenOne},x)
$$

となる。後続で乗法単位元法則が証明されると、これは通常の $x^0=1$、$x^1=x$ と一致する。

重要なのは、本宣言の時点では `GoldenInt` の `CommRing` instance がまだ完成していないことである。そのため標準記法 `x ^ n` に依存せず、黄金整数の raw API だけで冪を先に構成している。

## 証明全体での役割

`goldenPow` は `GoldenInt` の explicit coordinate API と Mathlib の標準環 API を接続するための橋である。

後続の `goldenCommRing : CommRing GoldenInt` では、自然数冪 `npow` が

```lean
npow := fun n x => goldenPow x n
```

として登録される。さらに

```lean
npow_zero := by intro x; rfl
npow_succ := by
  intro n x
  change goldenPow x (n + 1) = goldenMul (goldenPow x n) x
  rfl
```

と、今回の再帰方程式そのものによって環構造の冪公理が定義的等式で閉じる。

その後、

```lean
@[simp] theorem golden_pow_eq (x : GoldenInt) (n : ℕ) :
    goldenPow x n = x ^ n := rfl
```

が成立し、raw API の `goldenPow` と標準記法 `x ^ n` が `rfl` で一致する。

FLT5 の後半では fifth-power extraction が中心になるため、`goldenPow gamma 5` は多数の重要な interface に直接現れる。たとえば、整数埋め込みの五乗保存、coprime factor の fifth-power-up-to-unit、黄金単元の fifth-power class、最終的な座標多項式 `goldenPow_five_fst` / `goldenPow_five_snd` などが本定義を利用する。

したがって本宣言は、単純な再帰関数ではあるが、黄金整数層の「五乗」を全証明で共通化する基礎 API である。

## 直接依存する定義・補題

直接依存は次の三点である。

1. `GoldenInt`
2. 0120 `goldenOne`
3. 0124 `goldenMul`

加えて Lean の自然数再帰を利用する。

0121 `goldenAdd`、0122 `goldenNeg`、0123 `goldenSub` には直接依存しない。

また `CommRing GoldenInt` や標準 `Pow` instance にも依存しない。むしろ逆に、後続の `CommRing` instance が `goldenPow` を `npow` として採用する。

## 証明・定義の流れ

本宣言は `def` なので tactic proof はない。定義の流れは非常に明瞭である。

1. 底 `x : GoldenInt` を固定する。
2. 指数 `0` では `goldenOne` を返す。
3. 指数 `n + 1` では、既に計算した `goldenPow x n` に `x` を右から `goldenMul` する。
4. 再帰呼び出しの指数は `n + 1` から `n` に減るため structural recursion として受理される。
5. この二本の再帰方程式が、後続 `CommRing` の `npow_zero` / `npow_succ` とそのまま一致する。

数学的な帰納法を別 theorem として証明しているわけではなく、自然数冪の再帰規則そのものを定義にしている。

## Lean 固有の処理

### 1. curried な型

型は

```lean
def goldenPow (x : GoldenInt) : ℕ → GoldenInt
```

なので、底 `x` を固定した後に指数を取る curried function である。

これにより `goldenPow x` 自体が `ℕ → GoldenInt` として扱え、自然数再帰の定義が簡潔になる。

### 2. pattern matching による structural recursion

```lean
| 0 => goldenOne
| n + 1 => goldenMul (goldenPow x n) x
```

は `ℕ` に対する原始再帰である。再帰呼び出しが厳密に小さい `n` に対して行われるため、明示的な termination proof は不要である。

### 3. 定義的等式が強い

零乗と後者の式は theorem rewrite ではなく definitional reduction である。このため後続で

```lean
npow_zero := by intro x; rfl
```

および `npow_succ` を `rfl` で閉じられる。

これは単に proof script が短いだけでなく、custom power API と標準 `CommRing` API の間に変換補題の負債を作らない設計である。

### 4. 右乗算の再帰方向

再帰ステップは

```lean
goldenMul (goldenPow x n) x
```

であり、$x \cdot x^n$ ではなく $x^n \cdot x$ である。

これは後続 `CommRing` の `npow_succ` が要求する形と直接一致し、`change ...; rfl` で処理できる。乗法可換性がまだ証明されていない段階で、可換性 rewrite に依存せずに済む点も重要である。

### 5. 標準 `^` を先に使わない

この時点で標準環構造を使って `x ^ n` と定義すると、後で `CommRing GoldenInt` の `npow` を構築する際に循環的な依存を生む可能性がある。raw operation `goldenOne` / `goldenMul` だけで閉じることで、その循環を避けている。

## 冗長・重複箇所

数学的には `goldenPow` は一般の monoid power と同じ再帰であり、Mathlib の標準自然数冪と内容が重複する。

さらに後続で

```lean
@[simp] theorem golden_pow_eq (x : GoldenInt) (n : ℕ) :
    goldenPow x n = x ^ n := rfl
```

が導入されるため、raw API `goldenPow` と標準記法 `x ^ n` の二重 API が存在する。

ただしこの重複は意図的である。`CommRing GoldenInt` を構成する **前** に冪を必要とし、その同じ実装を `CommRing.npow` に差し込むことで、構成後は標準冪と定義的に一致させている。

したがって、ここでの duplication は循環依存を回避する bootstrap layer と見るべきである。

## 最適化候補

### 候補 A — 現状維持

最も自然である。依存が `goldenOne` と `goldenMul` だけに閉じ、後続 `npow_zero` / `npow_succ` / `golden_pow_eq` が `rfl` になる。

### 候補 B — generic な raw power helper を用意

`one` と `mul` を引数に取る一般的な primitive recursion helper を用意して `goldenPow` を特殊化することは可能である。

しかし `GoldenInt` 専用コードでは抽象化の利益が小さく、定義展開が一段深くなって `simp` / `rfl` の追跡性を悪化させる可能性がある。

### 候補 C — typeclass instance を先に構成して標準 `^` を使う

`One` / `Mul` instance を先に公開し、標準の `npowRec` 相当へ委譲する設計も考えられる。

ただし最終的な `CommRing` 構築との依存順を慎重に整理する必要があり、現行の explicit bootstrap より分かりにくくなる可能性がある。

### 候補 D — 五乗専用関数に限定する

FLT5 だけなら `goldenFifth x` のような固定指数関数にして multiplication を4回展開する案もある。

これは局所的には計算を明示できるが、単元の冪、任意指数の環 API、`goldenPhi` の冪分類などで再利用できない。証明全体では現在の自然数冪 API の方が明らかに有利である。

## 必要 Mathlib import と import 最適化候補

対象ブランチで確認した `Flt5DkMath/FLT5StandAlone.lean` は standalone 全体として

```lean
import Mathlib
```

を使用している。

一方、`goldenPow` 単独が必要とするものは `GoldenInt`、自然数 `ℕ`、`goldenOne`、`goldenMul`、自然数の pattern matching / structural recursion だけである。本宣言そのものには `ring`、`omega`、`norm_num`、`Zsqrtd` などは不要である。

したがって、この一宣言を理由に `Mathlib` 全体を import する必要はない。ただし `GoldenOrder` module 全体では直後から環法則、埋め込み、共役、ノルムなどを扱うため、必要 import は広がる。

具体的な最小 Mathlib module 集合は、この回では Lean build を行っていないため未検証であり、推測として断定しない。

## Comparator challenge 化の可否

 **適している。** 特に「数学的には同じ冪を、Lean の依存順と definitional equality を意識してどう実装するか」を比較する challenge にできる。

比較候補は次の通りである。

1. 現行の explicit primitive recursion
2. generic raw-power helper の特殊化
3. `One` / `Mul` typeclass を先行させ、標準的な power recursion を利用
4. FLT5 専用の固定五乗関数

評価軸は、依存循環の有無、`rfl` の強さ、`simp` 展開の透明性、`CommRing.npow` への接続容易性、五乗計算の可読性、後続 theorem での再利用性である。

現行実装の特に強い点は、後続 `CommRing` の `npow_succ` と再帰方向を一致させることで、乗法可換性を使う前から `rfl` で接続できることである。

## 既存資料との対応

対象ブランチには既存の日本語 PDF

`docs/pdf/FLT5-main-ja-v0-r1.pdf`

と英語 PDF

`docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在する。

この回では PDF 本文中の `goldenPow` に対応するページ・節を直接解析していないため、具体的なページ番号や PDF 固有の叙述は推測しない。

形式的内容の最終根拠は、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` 内 `GoldenOrder.lean` generated section とする。

## 次に読むべき宣言

次は

```lean
@[ext] theorem GoldenInt.ext {x y : GoldenInt}
    (hfst : x.fst = y.fst) (hsnd : x.snd = y.snd) : x = y := by
  cases x
  cases y
  simp_all
```

である。

`goldenPow` までは raw carrier と primitive operations を定義してきた。次の `GoldenInt.ext` は、二つの黄金整数が等しいことを二座標の等しさへ還元する extensionality theorem であり、後続の環法則・埋め込み・共役・ノルムに関する equality proof の基本道具になる。