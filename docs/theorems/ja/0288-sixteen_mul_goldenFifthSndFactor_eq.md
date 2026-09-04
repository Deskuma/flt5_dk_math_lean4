# 0288 — `sixteen_mul_goldenFifthSndFactor_eq`

## 宣言種別

これは **`theorem`** である。

zero-sector inversion で導入した対角座標 `X = 2*r+s` を用いて、黄金整数の 5 乗の第二座標に現れる四次因子 `goldenFifthSndFactor r s` を、平方完成に近い正定値型の四次式へ書き換える恒等式である。

## Lean の型

```lean
/-- Exact diagonalization of the quartic second-coordinate factor. -/
theorem sixteen_mul_goldenFifthSndFactor_eq (r s : ℤ) :
    16 * goldenFifthSndFactor r s =
      zeroSectorX r s ^ 4 +
        10 * zeroSectorX r s ^ 2 * s ^ 2 +
        5 * s ^ 4 := by
  unfold goldenFifthSndFactor zeroSectorX
  ring
```

Lean 上では任意の整数 `r s : ℤ` に対する無条件の多項式恒等式である。

`X := zeroSectorX r s = 2*r+s` と書けば、数学的主張は

$$
16H(r,s)=X^4+10X^2s^2+5s^4
$$

である。ここで

$$
H(r,s)=\texttt{goldenFifthSndFactor}(r,s)
$$

である。

正本コード中の `goldenFifthSndFactor` を展開すると

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4
$$

であり、したがって本定理は

$$
16(r^4+2r^3s+4r^2s^2+3rs^3+s^4)
=(2r+s)^4+10(2r+s)^2s^2+5s^4
$$

という純粋な整数多項式恒等式である。

## 数学的意味

左辺の `goldenFifthSndFactor` は `r,s` に対して非対称に見える四次式である。一方、右辺は新しい座標

$$
X=2r+s
$$

を使うことで

$$
X^4+10X^2s^2+5s^4
$$

という、すべて偶数次数の項だけからなる形へ変換される。

これが source docstring のいう **exact diagonalization** である。

厳密には二次形式の通常の「対角化」と同一概念ではないが、混合項を `X` へ吸収し、`X^4`, `X^2s^2`, `s^4` の三項へ整理しているため、後続の非負性・平方差分解に非常に適した形になる。

特に右辺の各項は整数上で非負であるため、直後の theorem `goldenFifthSndFactor_nonneg` では本恒等式から

$$
0\le H(r,s)
$$

を導ける。

## 証明全体での役割

0282–0287 では

$$
X=2r+s,
\qquad
U=X^2+5s^2,
\qquad
W=4d^5,
$$

$$
A=U-W,
\qquad
B=U+W,
\qquad
Q=5^5c^8
$$

という inversion 用の座標と補助量を定義した。

本 theorem 0288 は、それらのうち最初の座標 `X` が単なる記号導入ではなく、元の quartic factor `H(r,s)` を構造化できる座標であることを初めて証明する。

`SignedGoldenZeroSectorInversion.lean` の章コメントでは、zero-sector の tenth-power split とこの diagonal quartic identity から最終的に

$$
A B=4Q^5
$$

を得る設計が明記されている。

したがって本 theorem は、**zero-sector arithmetic で残った四次因子を inversion geometry に翻訳する最初の実質的な橋** である。

## 直接依存する定義・補題

直接依存は小さい。

### `goldenFifthSndFactor`

左辺の四次因子である。正本で使われている展開形は

$$
r^4+2r^3s+4r^2s^2+3rs^3+s^4.
$$

本証明では `unfold goldenFifthSndFactor` によりその定義を直接展開する。

### `zeroSectorX`

0282 で導入された定義

```lean
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s
```

である。本証明でも `unfold zeroSectorX` により `2*r+s` へ戻す。

### `ring`

DkMath 固有 lemma ではないが、証明を完結させる Mathlib tactic である。両辺を可換環上の正規形へ展開・比較して恒等式を閉じる。

`zeroSectorU`, `zeroSectorW`, `zeroSectorA`, `zeroSectorB`, `zeroSectorQ` は本 theorem の型・証明には直接現れない。

## 証明の流れ

証明は二段階だけである。

```lean
unfold goldenFifthSndFactor zeroSectorX
ring
```

1. `unfold` で `goldenFifthSndFactor` と `zeroSectorX` の定義を展開する。
2. 目標を整数係数の多項式恒等式にする。
3. `ring` が両辺を同じ正規形へ変換し、等式を証明する。

人手で展開すれば右辺は

$$
(2r+s)^4+10(2r+s)^2s^2+5s^4
$$

から

$$
16r^4+32r^3s+64r^2s^2+48rs^3+16s^4
$$

となり、これは

$$
16(r^4+2r^3s+4r^2s^2+3rs^3+s^4)
$$

に一致する。

## Lean 固有の処理

本 theorem は `ℤ` 内で完結しており、`Nat` からの coercion、`natAbs`、可除性 API、coprimality API は使わない。

Lean 固有のポイントは `unfold` と `ring` の組み合わせである。

`ring` は定義名を自動的にすべて展開するわけではないため、先に

```lean
unfold goldenFifthSndFactor zeroSectorX
```

として純粋な環式にする。以後は `ring` が冪・加法・乗法を正規化する。

この証明は computational proof に近く、前提仮定を一切必要としない。この点は後続の zero-sector candidate 固有の theorem と異なる。

## 冗長・重複箇所

証明本体にはほぼ冗長性がない。

```lean
unfold goldenFifthSndFactor zeroSectorX
ring
```

は、この種の多項式恒等式として最小級である。

ただし命題右辺で `zeroSectorX r s` を 2 回記述しているため、可読性だけを目的に

```lean
let X := zeroSectorX r s
```

とする書き方も可能である。しかしその場合は `let` 展開処理が増えるため、現行形の方が Lean 証明としては簡潔である。

## 最適化候補

### 1. 証明 tactic

現行 `unfold ...; ring` は十分に良い。`ring_nf` に置き換える必然性はない。

### 2. API としての形

後続で `16 * H = ...` ではなく `H = (...) / 16` を使いたくなる可能性はあるが、整数除算を導入すると divisibility 条件が必要になるため、現行の 16 倍恒等式の方が Lean 上は強く扱いやすい。

### 3. `zeroSectorU` との接続

`U = X^2+5s^2` なので、後続では本恒等式を `U` と結び付けた別形へ変換できる。もし同じ変形が何度も現れるなら専用 lemma を置く価値がある。ただし本 theorem 自体を `U` で書き換えると、直接の「非負な三項和」という特徴が見えにくくなるため、現在の形には独立の価値がある。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用している。

本 theorem が実際に必要とする主な機能は、整数環、自然数指数の冪、`ring` tactic、および依存定義 `goldenFifthSndFactor` / `zeroSectorX` である。

したがって `import Mathlib` は本 theorem 単独には広いと考えられる。ただしこの作業では Lean build を行わないため、元 module `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` の **実際の最小 import 集合は未検証** である。具体的な削減先は推測で断定しない。

## Comparator challenge 化の可否

**非常に適している。**

理由は、依存が `goldenFifthSndFactor` と `zeroSectorX` の定義だけで、核心が完全な多項式恒等式だからである。

challenge としては、例えば両定義を与えた上で

```lean
theorem challenge (r s : ℤ) :
    16 * goldenFifthSndFactor r s =
      zeroSectorX r s ^ 4 +
        10 * zeroSectorX r s ^ 2 * s ^ 2 +
        5 * s ^ 4 := by
  ...
```

を埋めさせればよい。

`ring` を知っていれば短く解ける一方、手展開でも検証可能であり、Comparator にとって「同じ恒等式を異なる proof style で比較する」教材として良い。

判定は **適する** である。

## PDF との対応

対象 branch に

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することは GitHub repository tree で確認した。

ただし GitHub コネクタの通常の UTF-8 ファイル取得では PDF binary 本文を解析可能な形で取得できないため、本 theorem と PDF の具体的ページ・節番号・文言の対応は **未確認** である。PDF 内の位置は推測せず、ここでは branch 上の Lean 正本と repository structure を根拠とする。

## 次に読むべき宣言

次は 0289 `goldenFifthSndFactor_nonneg` である。種別は **`theorem`**。

```lean
theorem goldenFifthSndFactor_nonneg (r s : ℤ) :
    0 ≤ goldenFifthSndFactor r s := by
  have hdiag : 0 ≤
      zeroSectorX r s ^ 4 +
        10 * zeroSectorX r s ^ 2 * s ^ 2 +
        5 * s ^ 4 := by
    positivity
  have hident := sixteen_mul_goldenFifthSndFactor_eq r s
  nlinarith
```

0288 で得た右辺が非負であることを `positivity` で示し、その恒等式から `nlinarith` によって

$$
0\le H(r,s)
$$

を導く。

したがって依存順では、0288 の algebraic diagonalization が 0289 で order-theoretic information へ変換される。