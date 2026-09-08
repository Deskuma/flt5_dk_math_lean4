# 0353 — `golden_mul_phiInv_coords`

## 宣言種別

この宣言は **`theorem`** である。

```lean
theorem golden_mul_phiInv_coords (x : GoldenInt) :
    goldenMul x goldenPhiInv = ⟨x.snd - x.fst, x.fst⟩ := by
  ext <;> simp [goldenMul, goldenPhiInv]
  all_goals ring
```

## Lean の型

```lean
golden_mul_phiInv_coords
    (x : GoldenInt) :
    goldenMul x goldenPhiInv = ⟨x.snd - x.fst, x.fst⟩
```

`GoldenInt` は黄金整数環 $\mathbb Z[\varphi]$ の要素を二つの整数座標で表す型であり、

$$
x=a+b\varphi
$$

に対して `x.fst = a`、`x.snd = b` と読む。

前段 0348 で定義された

```lean
def goldenPhiInv : GoldenInt := ⟨-1, 1⟩
```

は

$$
\varphi^{-1}=\varphi-1
$$

を表す。本 theorem は、任意の黄金整数にこの `goldenPhiInv` を掛けたときの座標を完全に明示する。

## 数学的主張

$x=a+b\varphi$ とする。黄金比の関係

$$
\varphi^2=\varphi+1
$$

を用いると、

$$
(a+b\varphi)(\varphi-1)
=a\varphi-a+b\varphi^2-b\varphi
$$

であり、$\varphi^2=\varphi+1$ を代入して

$$
(a+b\varphi)(\varphi-1)
=b-a+a\varphi
$$

となる。

したがって座標変換は

$$
(a,b)\longmapsto(b-a,a)
$$

である。

Lean の右辺

```lean
⟨x.snd - x.fst, x.fst⟩
```

はこの変換をそのまま `GoldenInt` の constructor で表している。

0352 `golden_mul_phi_coords` の

$$
(a,b)\longmapsto(b,a+b)
$$

と対になっており、二つの線形変換は $\varphi$ と $\varphi^{-1}$ の作用を表す。

## 証明全体での役割

`GoldenUnitClassification` の目的は、任意の黄金整数 unit を $\varphi$ または $\varphi^{-1}$ で動かしながら座標 measure を厳密に減少させ、最終的に基底 unit へ到達させることである。

0352 は $\varphi$ を掛ける方向、本 theorem 0353 は $\varphi^{-1}$ を掛ける方向の座標公式を提供する。

この直後には

```lean
def goldenUnitMeasure (x : GoldenInt) : ℕ :=
  x.fst.natAbs + x.snd.natAbs
```

が定義され、さらに `goldenUnit_descent` では符号場合分けに応じて

```lean
let y := goldenMul x goldenPhiInv
```

と置いた branch で

```lean
rw [golden_mul_phiInv_coords]
```

を直接使用する。

これにより抽象的な黄金整数の乗法後の measure 比較が、

$$
|b-a|+|a|<|a|+|b|
$$

型の整数絶対値の不等式へ変換される。

したがって依存の流れは概略

```text
goldenPhiInv + goldenMul
          ↓
golden_mul_phiInv_coords
          ↓
goldenUnitMeasure
          ↓
goldenUnit_descent
          ↓
goldenUnitFifthClass_of_unit
          ↓
goldenUnitClassesModFifth
```

となる。

本 theorem は単なる計算補題ではなく、unit の代数的乗法を有限降下で扱える整数座標へ翻訳するための重要なインターフェースである。

## 直接依存する定義・補題

主要な直接依存は次の通りである。

- `GoldenInt` — 黄金整数 $a+b\varphi$ を整数座標で保持する型。
- `goldenMul` — $\varphi^2=\varphi+1$ を組み込んだ黄金整数の乗法。
- `goldenPhiInv` — `⟨-1,1⟩`、すなわち $\varphi-1$。
- `GoldenInt` の extensionality — `ext` で二座標の等式へ分解するために使用。
- 整数環の正規化 — 最後の `ring` が使用する。

`goldenMul` は

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

である。

`y = goldenPhiInv = ⟨-1,1⟩` を代入すると第一座標は

$$
a(-1)+b=b-a
$$

第二座標は

$$
a+b(-1)+b=a
$$

となる。

0349 `golden_phi_mul_inv` や 0350 `golden_inv_mul_phi` は数学的背景として $\varphi^{-1}$ 性を保証しているが、本 theorem の証明本文では直接参照されない。ここでは逆元則から座標を導くのではなく、`goldenMul` と `goldenPhiInv` を直接展開して計算している。

## 証明または構築の流れ

証明は

```lean
by
  ext <;> simp [goldenMul, goldenPhiInv]
  all_goals ring
```

である。

流れは次の通り。

1. `ext` が `GoldenInt` 同士の等式を `fst` と `snd` の二つの座標等式へ分解する。
2. `<;>` により、その各 subgoal に `simp [goldenMul, goldenPhiInv]` を適用する。
3. `simp` が `goldenMul` と `goldenPhiInv` を展開し、constructor projection、$0$、$1$、$-1$ などの基本簡約を進める。
4. 残った整数多項式等式を `all_goals ring` が正規化して閉じる。

概念的には Lean は

```text
fst:
  a * (-1) + b * 1 = b - a

snd:
  a * 1 + b * (-1) + b * 1 = a
```

を証明している。

## Lean 固有の処理

### `ext` による structure equality

`GoldenInt` は座標 structure なので、constructor 全体の等式を直接操作するより

```lean
ext
```

で field equality に分解する方が自然である。

0352 と同じ proof pattern であり、座標モデルを採用した利点がよく現れている。

### `simp` と `ring` の役割分担

ここで `simp` は定義展開と単位元・符号の簡約を担当し、`ring` は整数多項式として残る加減算の正規化を担当する。

特に右辺には

```lean
x.snd - x.fst
```

という減算が現れるため、0352 の加法だけの座標式より少し正規化が必要になる。`ring` は順序や divisibility を推論しているのではなく、可換環の恒等式として等式を閉じている。

### `all_goals ring`

`ext` が複数目標を生成するため、`all_goals ring` により残ったすべての座標目標に同じ `ring` tactic を適用している。

これは proof state の個数に依存せず二座標をまとめて処理できる Lean 固有の簡潔な書き方である。

## 冗長・重複箇所

0352 `golden_mul_phi_coords` と本 theorem は非常に対称的である。

$$
M_\varphi=
\begin{pmatrix}
0&1\\
1&1
\end{pmatrix},
\qquad
M_{\varphi^{-1}}=
\begin{pmatrix}
-1&1\\
1&0
\end{pmatrix}
$$

とすると、両 theorem はこれらの行列が座標ベクトル $(a,b)^T$ に作用することを述べている。

さらに

$$
M_\varphi M_{\varphi^{-1}}=I
$$

であるため、二つの theorem を「互いに逆な座標作用」という抽象 API にまとめることも可能である。

ただし現状の `goldenUnit_descent` は各 branch で具体的な `natAbs` 不等式を扱うため、現在の明示的座標式は非常に使いやすい。行列 abstraction を導入すると後続で再び座標へ戻す必要があり、局所的にはかえって冗長になる可能性がある。

## 最適化候補

現行証明はすでに短く、重大な冗長性はない。候補としては次が考えられる。

1. tactic を一行にまとめて `ext <;> simp [goldenMul, goldenPhiInv] <;> ring` と書ける可能性がある。
2. `simp` lemma の整備次第では `ring` 前の goal をさらに単純化できる可能性がある。
3. `[simp]` 属性を付ければ後続 `rw [golden_mul_phiInv_coords]` を自動化できる可能性がある。
4. 0352 と 0353 を unit-generator coordinate API としてまとめ、変換が互いに逆であることを別 theorem として与える余地がある。

ただし 3 は `goldenMul x goldenPhiInv` を常に constructor 座標へ展開する simp normal form を選ぶことになる。抽象的な乗法形を維持したい箇所では過剰展開になり得るため、後続全体への影響を確認せず属性を追加するべきではない。

1 も可読性上の差にすぎず、現行の `all_goals ring` は `simp` と代数正規化の段階が明確である。

## 必要 Mathlib import と import 最適化候補

生成 standalone `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem 自体が直接要求する機能は主として

- structure extensionality tactic `ext`
- simplifier `simp`
- 整数の加減乗算と符号に関する基礎 lemma
- ring normalization tactic `ring`
- 前段で定義済みの `GoldenInt`、`goldenMul`、`goldenPhiInv`

である。

`omega`、`nlinarith`、`norm_num` は本 theorem では使用しない。

したがって `Mathlib` 全体より小さな import 集合で成立する可能性は高い。ただし `ring` tactic の import、`GoldenInt` 周辺の実際の module dependency、生成前のプロジェクト module import を含めた **厳密な最小 import は Lean ビルドなしでは確認できない**。

今回は Lean ビルドを行わないため、具体的な最小 import 名は未確認とする。

## Comparator challenge 化の可否

**適している。難度は初中級。**

例えば次の challenge にできる。

```lean
example (x : GoldenInt) :
    goldenMul x goldenPhiInv = ⟨x.snd - x.fst, x.fst⟩ := by
  ?_
```

`goldenMul` と `goldenPhiInv` の定義を利用可能にしておけば、期待する小さな解は

```lean
ext <;> simp [goldenMul, goldenPhiInv]
all_goals ring
```

である。

評価点は

- structure equality を `ext` へ落とせるか
- `goldenPhiInv` を展開すべきと判断できるか
- `simp` と `ring` の役割を分離できるか
- 不要な `omega` や `nlinarith` に逃げず環恒等式として処理できるか
- $\varphi^{-1}$ の抽象的逆元証明ではなく coordinate computation が最短であることを見抜けるか

にある。

0352 とセットにすれば、$\varphi$ と $\varphi^{-1}$ の二つの座標作用を完成させる小さな Comparator challenge pair として特に適している。

## 次に読むべき宣言

次は **0354 `goldenUnitMeasure`** を読むべきである。宣言種別は **`def`**。

```lean
/-- Coordinate size used for the elementary unit descent. -/
def goldenUnitMeasure (x : GoldenInt) : ℕ :=
  x.fst.natAbs + x.snd.natAbs
```

数学的には

$$
\mu(a,b)=|a|+|b|
$$

という $\ell^1$ 型の整数座標 measure を定義する。

0352 と 0353 で得た二つの座標変換をこの measure に代入することで、後続の `goldenUnit_descent` は適切な符号 branch において

$$
\mu(x\varphi)<\mu(x)
$$

または

$$
\mu(x\varphi^{-1})<\mu(x)
$$

を証明する。ここから unit classification の有限降下が本格的に始まる。