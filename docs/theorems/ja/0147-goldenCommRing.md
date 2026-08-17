# 0147 — `goldenCommRing`

## Lean の型

```lean
instance goldenCommRing : CommRing GoldenInt := by
  refine
    { goldenAddGroupWithOne with
      npow := fun n x => goldenPow x n
      npow_zero := by intro x; rfl
      npow_succ := by
        intro n x
        change goldenPow x (n + 1) = goldenMul (goldenPow x n) x
        rfl
      add_comm := ?_
      left_distrib := ?_
      right_distrib := ?_
      zero_mul := ?_
      mul_zero := ?_
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_
      mul_comm := ?_ } <;>
    intros <;> ext <;>
    simp <;> ring
```

これは theorem ではなく、`GoldenInt` に完全な可換環構造 `CommRing GoldenInt` を与える named `instance` である。0145 `goldenAddCommGroup` と 0146 `goldenAddGroupWithOne` で準備した加法・cast 側の構造を再利用し、`goldenMul` と `goldenPow` を標準乗法・自然数冪として整合させ、残る環法則を座標計算へ還元して証明する。

## 数学的主張・宣言の意味

`GoldenInt` は整数座標 `(a,b)` により

$$
a+b\varphi
$$

を表し、生成元は

$$
\varphi^2=\varphi+1
$$

という二次関係を満たすように `goldenMul` が定義されている。したがって

$$
(a+b\varphi)(c+d\varphi)
=(ac+bd)+(ad+bc+bd)\varphi
$$

である。

本 instance が主張しているのは、この明示的な加法・否定・減算・乗法・単位元・自然数冪が、可換環の全公理を満たすということである。すなわち `GoldenInt` は単なる整数 pair ではなく、Lean / Mathlib から通常の可換環として扱える。

数学的には、これは黄金整数環 $\mathbb Z[\varphi]$ の座標モデルが可換環であることに対応する。ただし、この宣言そのものは `AdjoinRoot` や商環との同型を構築しているわけではなく、あくまで明示座標演算に対して環法則を直接証明している。

## 証明全体での役割

これは `GoldenOrder` 層の重要な節目である。0145 までで可換加法群、0146 で自然数・整数 cast を備えた `AddGroupWithOne` が完成し、本 0147 で乗法・冪・分配法則・単位律・結合律・可換律を加えることで、

$$
\texttt{GoldenInt}
\longrightarrow
\texttt{CommRing GoldenInt}
$$

が成立する。

この instance 以降、後続コードは `goldenMul` の raw API だけでなく、Mathlib 標準の

```lean
x * y
x ^ n
x ∣ y
```

などを利用できる。実際、後続の `GoldenDivisibility` 層では explicit な `GoldenDivides` と通常の `d ∣ x` を結ぶ theorem が現れ、さらに `NoZeroDivisors`、Euclidean-domain 構造、gcd、第五冪因子分解へ進む。そのため `goldenCommRing` は、座標モデルを Mathlib の一般環論へ接続する中核 interface である。

## 直接依存する定義・補題

直接依存する主要要素は次の通りである。

- `GoldenInt`
- 0146 `goldenAddGroupWithOne`
- 0124 `goldenMul`
- 0125 `goldenPow`
- `GoldenInt.ext`
- 0133–0144 の各 `@[simp]` 座標 projection theorem
- Mathlib の `CommRing`
- `ring` tactic

特に乗法法則の座標証明は、0143 `golden_fst_mul` と 0144 `golden_snd_mul` により標準 `*` を整数多項式へ展開できることに依存する。加法・零元・単位元・否定・減算についても、それ以前に整備された simp API が `ext <;> simp` の基盤となる。

依存の大きな流れは

$$
\texttt{raw coordinate operations}
\longrightarrow
\texttt{projection simp lemmas}
\longrightarrow
\texttt{goldenAddCommGroup}
\longrightarrow
\texttt{goldenAddGroupWithOne}
\longrightarrow
\texttt{goldenCommRing}
$$

である。

## 証明・構築の流れ

証明は二段階に分かれる。

第一段階では、0146 の structure を再利用しつつ、冪演算を

```lean
npow := fun n x => goldenPow x n
```

として登録する。そして自然数冪の零指数・後者ステップを、`goldenPow` の再帰定義に直接対応させる。

```lean
npow_zero := by intro x; rfl
```

は

$$
x^0=1
$$

を definitionally 閉じる。

`npow_succ` では

```lean
change goldenPow x (n + 1) = goldenMul (goldenPow x n) x
rfl
```

と goal を raw API の形へ変更し、`goldenPow` の successor clause そのものに一致させる。

第二段階では、残る環法則

- `add_comm`
- `left_distrib`
- `right_distrib`
- `zero_mul`
- `mul_zero`
- `mul_assoc`
- `one_mul`
- `mul_one`
- `mul_comm`

を hole として置き、最後の

```lean
intros <;> ext <;>
simp <;> ring
```

で一括処理する。

`ext` により `GoldenInt` の等式を `fst` と `snd` の二つの整数等式へ分解し、`simp` が 0133–0144 の projection theorem を用いて座標式へ展開し、最後に `ring` が整数多項式恒等式として閉じる。

## Lean 固有の処理

最も重要なのは structure update と tactic pipeline の組合せである。

```lean
{ goldenAddGroupWithOne with ... }
```

により、0146 までに確立した加法群・`0`・`1`・cast の field を再利用し、本 instance では乗法側に必要な差分だけを追加する。これにより巨大な `CommRing` structure をゼロから再構築せずに済む。

また `change` は `npow_succ` の標準記法を raw recursive definition と同じ形に合わせるために使われる。この操作の後は `rfl` で閉じるため、自然数冪の整合性に追加の数学補題を要求しない。

最後の

```lean
intros <;> ext <;> simp <;> ring
```

はこの実装の設計思想をよく表している。抽象的な環法則を直接証明するのではなく、

$$
\text{GoldenInt equality}
\to
\text{coordinate equalities}
\to
\text{integer polynomial identities}
$$

へ順に落とす。

`ext` と `simp` が十分に強い API 境界を形成しているため、最後は `ring` が処理できる正規化された世界に到達する。

## 冗長・重複箇所

本 instance には、すでに 0145 で `AddCommGroup` として証明済みの `add_comm` を `CommRing` constructor 側で再び field として与えるように見える箇所がある。これは source が採用している Mathlib hierarchy / structure update の形に由来するもので、単純な数学的重複とは限らない。

また `left_distrib` と `right_distrib`、`zero_mul` と `mul_zero`、`one_mul` と `mul_one` は、可換乗法を先に利用できれば片側から導出できる数学的対称性を持つ。しかし structure 構築中には、まだ完成した `CommRing` instance 自体を自由に再利用できないため、各 field を座標計算で独立に閉じる現行方式は bootstrap 上わかりやすい。

さらに `simp <;> ring` により複数の法則が同一パターンで処理されるため、proof script の重複はかなり圧縮されている。

## 最適化候補

候補は次の通りである。

1. 現行の明示座標 `CommRing` construction を維持する。
2. `mul_comm` など先に得られる法則から左右対称な field を導出し、座標 `ring` 呼び出しを減らす。
3. 一般二次環

$$
\theta^2=p\theta+q
$$

の座標 `CommRing` constructor を抽象化し、黄金整数を $p=q=1$ として特殊化する。
4. `AdjoinRoot`、商環、quadratic algebra など Mathlib の一般構造を用いて環構造を構築し、座標モデルへの同型を通じて transport する。
5. `goldenPow` を独自再帰として持たず、`CommRing` 構築後の標準 `Pow` / `npow` と同一視する設計を検討する。

ただし 4 や 5 は abstraction を強める代わりに、現在の「座標式を見ればすべて追える」という監査可能性を失う可能性がある。FLT5 の証明 museum という目的では、現行の explicit construction は教育的価値が高い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は

```lean
import Mathlib
```

を使用している。

本 instance が直接利用する Mathlib 機能は、`CommRing` hierarchy、`ext` machinery、`simp`、そして `ring` tactic である。したがって 0146 までの単純な structure declaration よりは tactic 側の依存が明確に増えている。

一方で、本宣言だけのために `Mathlib` umbrella 全体が必要とは限らない。より細い algebra hierarchy import と ring-normalization tactic の import に分割できる可能性がある。ただし exact minimal import 名は Mathlib version に依存し、Lean build による確認が必要である。今回 Lean build は行わないため、具体的な最小 import 集合は確定しない。

## Comparator challenge 化の可否

非常に適している。これは小さな interface declaration ではなく、実装方針の差が downstream proof burden に直接現れる節目だからである。

比較候補としては、

- 現行の explicit coordinate + `ext` + `simp` + `ring`
- 一般 quadratic-coordinate ring の特殊化
- `AdjoinRoot` / quotient-based implementation
- 既存 quadratic algebra からの structure transport

が考えられる。

評価軸は、

- `CommRing` 構築に必要な proof 行数
- `rfl` で閉じる field 数
- simp 正規形の安定性
- downstream の divisibility / norm / Euclidean-domain 証明量
- representation の透明性
- Mathlib import の大きさ
- 一般化可能性

である。

特に「抽象構造を再利用すると短くなるが、座標レベルの可視性がどれだけ失われるか」を測る Comparator challenge として価値が高い。

## PDF・Lean source との対応

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。

形式的根拠は `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/GoldenOrder.lean` generated section である。そこでは 0146 `goldenAddGroupWithOne` の直後に本 `goldenCommRing` が置かれ、その直後に `goldenDoubleEmbedding` が続く。

本 instance の数学的意味は PDF の黄金整数環の叙述と整合するが、今回 PDF の具体的ページ・節を直接特定していないため、ページ番号は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
def goldenDoubleEmbedding (x : GoldenInt) : Zsqrtd 5 :=
  ⟨2 * x.fst + x.snd, x.snd⟩
```

である。

これは theorem ではなく `def` であり、黄金整数 $a+b\varphi$ を $\mathbb Z[\sqrt5]$ 側へ二倍して送る明示的な座標写像を定義する。0147 で `GoldenInt` の完全な可換環構造が完成した後、次はこの環を `Zsqrtd 5` の既存構造へ接続し、零因子排除や整域方向の議論へ進む。