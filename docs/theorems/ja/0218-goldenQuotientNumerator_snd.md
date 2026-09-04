# 0218 — `goldenQuotientNumerator_snd`

## Lean の型

```lean
theorem goldenQuotientNumerator_snd (x y : GoldenInt) :
    (goldenQuotientNumerator x y).snd =
      x.snd * y.fst - x.fst * y.snd := by
  simp [goldenQuotientNumerator, goldenMul, goldenConj]
  ring
```

これは `theorem` であり、0216 `goldenQuotientNumerator` で定義した `x * conjugate(y)` の第二座標を、`x` と `y` の整数座標だけからなる明示式へ展開する。

## 数学的主張

`x=a+bφ`、`y=c+dφ` と書く。0163 `goldenConj` より

$$
\overline y=(c+d)-d\varphi
$$

であり、黄金整数の乗法

$$
(A+B\varphi)(C+D\varphi)
=(AC+BD)+(AD+BC+BD)\varphi
$$

を `x` と `conj(y)` に適用すると、第二座標は

$$
b(c+d)+a(-d)+b(-d)=bc-ad
$$

となる。したがって本 theorem は

$$
(x\overline y)_{\varphi}=bc-ad
$$

を Lean の座標式として公開している。

第一座標を与える 0217 と合わせると、

$$
x\overline y
=
\bigl(a(c+d)-bd\bigr)
+
\bigl(bc-ad\bigr)\varphi
$$

という有理化分子の完全な座標表示が揃う。

## 証明全体での役割

GoldenEuclidean 層では、非零 `y` に対する商を

$$
\frac{x}{y}=\frac{x\overline y}{N(y)}
$$

として有理化し、その二座標を最近接整数へ丸めて Euclidean quotient を作る。

0216 が分子 `x * conjugate(y)` を `GoldenInt` として固定し、0217 と 0218 がその二座標を整数多項式へ展開する。直後の 0219 `goldenQuotientCoords` はこの二座標を `goldenNorm y` で割り、`GoldenRat = ℚ × ℚ` 上の商を定義する。

さらに後段の `goldenRemainder_norm_rat_identity` では、`goldenQuotientNumerator_fst` と本 theorem が同時に rewrite され、元の座標 `x.fst`, `x.snd` を quotient coordinates から復元する二本の恒等式 `hx1`, `hx2` の証明に使われる。したがって本 theorem は単なる表示補題ではなく、Euclidean remainder の norm contraction を代数的に展開するための直接の入力である。

## 直接依存する定義・補題

直接依存は次の通り。

- `GoldenInt`
- 0216 `goldenQuotientNumerator`
- 0163 `goldenConj`
- 0124 `goldenMul`
- `ring` tactic
- 上流の座標 simp API

証明は 0217 と同じ構造であり、概念的には

$$
\texttt{goldenQuotientNumerator}
+\texttt{goldenConj}
+\texttt{goldenMul}
\longrightarrow
\text{第二座標の整数多項式}
$$

という展開である。

## 証明の流れ

```lean
simp [goldenQuotientNumerator, goldenMul, goldenConj]
ring
```

1. `goldenQuotientNumerator x y` を `goldenMul x (goldenConj y)` へ展開する。
2. `goldenConj y` を座標 `⟨y.fst + y.snd, -y.snd⟩` へ展開する。
3. `goldenMul` の第二座標公式を展開する。
4. `simp` で射影・符号・基本整数演算を整理する。
5. 残った多項式恒等式を `ring` で正規化し、

$$
x.snd\cdot y.fst-x.fst\cdot y.snd
$$

へ閉じる。

## Lean 固有の処理

本 proof では `ext` は不要である。目標が `GoldenInt` 全体の等式ではなく、すでに `.snd : ℤ` の等式だからである。

`simp [goldenQuotientNumerator, goldenMul, goldenConj]` は raw API を一気に展開し、`GoldenInt.snd` 射影を整数式へ落とす。その後 `ring` が交換・結合・分配・符号処理を含む多項式正規化を担当する。

ここで結果が

```lean
x.snd * y.fst - x.fst * y.snd
```

という行列式型の交差項になるのは数学的にも興味深い。これは基底 `1,φ` における有理化分子の第二成分であり、後続の quotient reconstruction では分母 `N(y)` と組み合わされる。

## 冗長・重複箇所

0217 `goldenQuotientNumerator_fst` と 0218 は完全に対をなす二本の projection theorem であり、proof も同一パターンである。

このため API-level には多少の重複がある。たとえば、

```lean
(goldenQuotientNumerator x y).fst = ... ∧
(goldenQuotientNumerator x y).snd = ...
```

という pair theorem にまとめる設計も可能である。

ただし後続では第一座標・第二座標を別々の rewrite として使うため、個別 theorem の方が `rw` / `simp` で扱いやすい。特に `goldenRemainder_norm_rat_identity` では二本を同時に指定できるので、現行 API は実用上自然である。

## 最適化候補

1. **0217/0218 を pair theorem から導出する**
   - 内部で一度だけ座標展開し、projection theorem を corollary とする。

2. **標準乗法記法へ寄せる**
   - `goldenQuotientNumerator` を `x * goldenConj y` で定義し、raw `goldenMul` 露出を減らす。

3. **quotient numerator を専用 structure にする**
   - `fst` / `snd` の意味を numerator real-coordinate / phi-coordinate として名前付き field にする案。ただし現状の `GoldenInt` 再利用の方が軽量。

4. **一般二次環へ抽象化する**
   - `θ²=pθ+q` に対する共役・ノルム・有理化分子の一般公式を構成し、golden case を特殊化する。

局所 proof 自体は `simp; ring` で十分短く、最適化余地は主に API 設計側にある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が直接必要とする主な Mathlib 表面は、

- 整数環演算
- `simp`
- `ring`

である。

`GoldenInt`, `goldenMul`, `goldenConj`, `goldenQuotientNumerator` は project 内上流定義である。宣言単独なら `Mathlib` 全体より小さい import で足りる可能性が高いが、`GoldenEuclidean.lean` 全体では rationals、round、absolute value、`field_simp`、`nlinarith`、Euclidean-domain API などを利用するため、module 単位の最小 import はかなり広くなる。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。候補は次の通り。

- A: 現行 `simp [defs]; ring`
- B: 手計算した第二座標式を `rfl` 近傍まで definitionally 合わせる実装
- C: 0217/0218 を一つの pair theorem として証明
- D: `RingEquiv` と norm/conjugation の抽象 API から quotient numerator 座標を導出
- E: 一般 quadratic order の formula を特殊化

比較軸は proof 長、raw definition 依存、rewrite usability、一般化可能性、後続 `field_simp` proof での使いやすさである。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

正本 source では 0217 の直後に本 theorem が置かれ、その直後に `goldenQuotientCoords` が続く。また後段の `goldenRemainder_norm_rat_identity` が 0217 と 0218 を同時に使用している。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0219 `goldenQuotientCoords`** である。

```lean
def goldenQuotientCoords (x y : GoldenInt) : GoldenRat :=
  (((goldenQuotientNumerator x y).fst : ℚ) / goldenNorm y,
    ((goldenQuotientNumerator x y).snd : ℚ) / goldenNorm y)
```

0217 と 0218 で `x * conjugate(y)` の整数座標が揃ったので、0219 ではそれぞれを `N(y)` で割り、実際の有理 quotient coordinates を構成する。ここから最近接整数丸め `goldenQuotient` と remainder 構築へ進む。
