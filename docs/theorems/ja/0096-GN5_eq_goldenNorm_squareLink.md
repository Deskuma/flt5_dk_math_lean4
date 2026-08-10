# 0096 — `GN5_eq_goldenNorm_squareLink`

## Lean の型

```lean
theorem GN5_eq_goldenNorm_squareLink (g y : ℕ) :
    (GN5 g y : ℤ) =
      GoldenNorm
        (↑((g + y) ^ 2 + y ^ 2) : ℤ)
        (↑((g + y) * y) : ℤ) := by
  unfold GN5 GoldenNorm
  push_cast
  ring
```

## 数学的主張

自然数 `g, y` に対して、五次円分因子 `GN5 g y` を整数へ埋め込んだものが、endpoint-square 座標

$$
M=(g+y)^2+y^2,
\qquad
N=(g+y)y
$$

における黄金比型二次形式

$$
\mathrm{GoldenNorm}(M,N)=M^2+MN-N^2
$$

と一致することを主張する。すなわち

$$
\mathrm{GN5}(g,y)
=\mathrm{GoldenNorm}\bigl((g+y)^2+y^2,(g+y)y\bigr)
$$

である。

`GN5` の定義を展開すれば

$$
\mathrm{GN5}(g,y)
=g^4+5g^3y+10g^2y^2+10gy^3+5y^4,
$$

一方、右辺を展開しても同じ多項式になる。

## 証明全体での役割

0093 では黄金比型二次形式 `GoldenNorm` を導入し、0094 では `GN5` を square/cross form

$$
(g^2)^2+5g^2y(g+y)+5\bigl(y(g+y)\bigr)^2
$$

へ書き換え、0095 では

$$
g^2+2y(g+y)=(g+y)^2+y^2
$$

という座標変換を切り出した。

本定理は、それらの準備を最終的に一本へ束ねる bridge 本体である。proof graph 上では

$$
\mathrm{GN5}
\longrightarrow
\text{square/cross coordinates}
\longrightarrow
\text{endpoint-square coordinates}
\longrightarrow
\mathrm{GoldenNorm}
$$

という流れの到達点に位置する。

この theorem により、以降の証明は四次多項式 `GN5` の係数計算を直接扱わず、黄金比に対応する二次形式 `GoldenNorm` の算術へ移れる。standalone source では後続で本定理の対称形を使い、`GoldenNorm ... = (GN5 g y : ℤ)` として fifth-power 情報へ接続している。さらに signed square/golden exceptional の構成でも、`w-v` と `v` を代入して endpoint-square 座標から `GN5` へ戻す用途で再利用されている。

## 直接依存する定義・補題

直接依存する project-local 宣言は次の二つである。

1. `GN5 : ℕ → ℕ → ℕ`
2. `GoldenNorm : ℤ → ℤ → ℤ`

0094 `GN5_eq_square_cross_form` と 0095 `square_cross_coordinate_change` は数学的な導出を説明する中間補題だが、本 theorem の Lean 証明本文では直接呼ばれない。

Mathlib 側では主として次を利用する。

1. 自然数から整数への coercion。
2. `push_cast` による cast の押し込み。
3. `ring` による可換環上の多項式正規化。

## 証明の流れ

証明は三段階である。

```lean
unfold GN5 GoldenNorm
push_cast
ring
```

まず `GN5` と `GoldenNorm` を展開する。次に `push_cast` が自然数式から整数式への coercion を演算の内側へ押し込み、両辺を同じ `ℤ` 上の多項式として比較できる形にする。最後に `ring` が両辺を正規形へ落として一致を証明する。

数学的には、右辺

$$
\bigl((g+y)^2+y^2\bigr)^2
+\bigl((g+y)^2+y^2\bigr)(g+y)y
-\bigl((g+y)y\bigr)^2
$$

を展開すると `GN5 g y` の係数列 `1,5,10,10,5` が得られることの確認である。

## Lean 固有の処理

### 1. `ℕ` から `ℤ` への型境界

`GN5 g y` は `ℕ` 値だが、`GoldenNorm` は減法を含むため `ℤ` 上で定義されている。そのため theorem の左辺では `(GN5 g y : ℤ)` と明示的に cast する。

### 2. `push_cast`

`ring` に渡す前に、`↑((g+y)^2+y^2)` や `↑((g+y)y)` といった自然数式の cast を整数上の加法・乗法・冪へ分配する必要がある。`push_cast` がこの境界処理を担う。

### 3. `ring`

cast 後は整数上の純粋な多項式恒等式なので `ring` で閉じる。減法があるため、0094・0095 の自然数半環だけの `ring` よりも、ここでは整数環への移行が本質的である。

## 冗長・重複箇所

本 theorem の証明は 0094 と 0095 を直接利用せず、定義を再展開して `ring` で一括証明する。その意味では、0094・0095 が計算上は冗長に見える。

しかし 0094 は「四次式を square/cross 二次形式へ」、0095 は「square/cross から endpoint-square へ」という数学的意味を分離して見せる説明用補題であり、本 theorem はそれらを最終 API として束ねる役目を持つ。したがって、証明 term の最短化と proof graph の可読性が意図的に分離されていると見るのが自然である。

## 最適化候補

### 候補 A — 現状維持

最短かつ堅牢である。`unfold`、`push_cast`、`ring` だけで証明が閉じ、後続には意味の明確な一つの bridge API を公開できる。

### 候補 B — 0094・0095 を用いる構造的証明

0094 の square/cross form と 0095 の coordinate change を明示的に `rw` してから `GoldenNorm` へ到達する証明にすれば、説明と Lean proof の対応は強くなる。

一方で cast と書換えが増え、現行の三行証明より脆くなる可能性がある。

### 候補 C — endpoint 座標を helper 定義にする

`M(g,y)` と `N(g,y)` を named definitions にすれば、後続で繰り返される

```lean
((g + y) ^ 2 + y ^ 2)
((g + y) * y)
```

を短縮できる。実際、後続では同型の座標が複数回使われるため、再利用回数が増えるなら検討価値がある。

### 候補 D — Golden order の norm と統合する

後段で `GoldenNorm` が実際の黄金整数環の norm と対応付けられるなら、将来的には「多項式 bridge」と「代数的整数 norm bridge」の二層 API を整理できる。ただし本 theorem の軽量性を失わないことが重要である。

## 必要 Mathlib import と import 最適化候補

対象ブランチの generated standalone artifact は `import Mathlib` を使用している。

本 theorem 単体で直接必要なのは、自然数・整数の cast、可換環の基本演算、`push_cast`、`ring` である。したがって umbrella `Mathlib` は単独 theorem に対しては過大であり、cast tactic と ring tactic を提供する Mathlib module 群へ縮小できる可能性が高い。

ただし generated artifact では `SquareGoldenBridge.lean` の他宣言も同じ module に含まれ、後続には整数上の discriminant 恒等式などが続く。Lean build を行っていないため、具体的な最小 import 組合せは断定しない。

## Comparator challenge 化の可否

適している。比較軸は「短さ」と「数学的構造の露出」の違いになる。

候補は少なくとも次の三方式である。

1. 現行の `unfold; push_cast; ring`。
2. 0094・0095 を明示利用する staged rewrite 証明。
3. endpoint 座標 helper を導入してから一般的な quadratic-form identity として証明する方式。

評価基準は行数だけでなく、cast 処理の安定性、後続の再利用性、数学的意図の見えやすさ、Mathlib 更新への耐性が適切である。

## 既存資料との対応

形式的な最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` である。generated manifest は本定理を `DkMath/FLT/Five/SquareGoldenBridge.lean` 区間に置いている。

既存の日本語・英語 PDF については、今回 GitHub code search が upstream 502 を返し、対応する具体的ページ・節を確定できなかった。そのため PDF のページ番号や逐語的対応は推測で補っていない。

## 次に読むべき定理

standalone source で本定理の直後に置かれるのは

```lean
theorem four_mul_goldenNorm_eq_discriminant_five (m n : ℤ) :
    4 * GoldenNorm m n = (2 * m + n) ^ 2 - 5 * n ^ 2 := by
  unfold GoldenNorm
  ring
```

である。

次号では

$$
4\,\mathrm{GoldenNorm}(m,n)
=(2m+n)^2-5n^2
$$

という discriminant-five form への対角化を読む。これにより `GoldenNorm` が単なる二次形式ではなく、判別式 $5$ を持つ黄金比型構造であることが表面化する。