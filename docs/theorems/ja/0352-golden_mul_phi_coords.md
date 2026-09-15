# 0352 — `golden_mul_phi_coords`

## 宣言種別

この宣言は **`theorem`** である。

```lean
theorem golden_mul_phi_coords (x : GoldenInt) :
    goldenMul x goldenPhi = ⟨x.snd, x.fst + x.snd⟩ := by
  ext <;> simp [goldenMul, goldenPhi]
```

## Lean の型

```lean
golden_mul_phi_coords
    (x : GoldenInt) :
    goldenMul x goldenPhi = ⟨x.snd, x.fst + x.snd⟩
```

`GoldenInt` は黄金整数環 $\mathbb Z[\varphi]$ の要素を整数座標

$$
x=a+b\varphi
$$

として保持するモデルであり、`x.fst = a`、`x.snd = b` に対応する。

`goldenPhi : GoldenInt` は

```lean
def goldenPhi : GoldenInt := ⟨0, 1⟩
```

であり、基底元 $\varphi$ を表す。

したがって本 theorem は、任意の黄金整数 $a+b\varphi$ に $\varphi$ を掛けたときの座標を明示する。

## 数学的主張

黄金比基底は

$$
\varphi^2=\varphi+1
$$

を満たす。そのため

$$
(a+b\varphi)\varphi
=a\varphi+b\varphi^2
$$

から

$$
(a+b\varphi)\varphi
=b+(a+b)\varphi
$$

を得る。

したがって座標変換は

$$
(a,b)\longmapsto(b,a+b)
$$

である。

Lean の右辺

```lean
⟨x.snd, x.fst + x.snd⟩
```

は、まさにこの変換を `GoldenInt` の座標として表したものである。

## 証明全体での役割

0351 `goldenUnit_phiInv` までで、$\varphi^{-1}=\varphi-1$ が unit であることが確定した。ここから `GoldenUnitClassification` は、任意の unit を $\varphi$ または $\varphi^{-1}$ で移動させながら座標 measure を減少させる descent に入る。

本 theorem は、その descent のうち $\varphi$ を掛ける側の座標公式を提供する。

後続の `goldenUnit_descent` では実際に

```lean
let y := goldenMul x goldenPhi
```

と置いたあと、measure 比較を行うために

```lean
rw [golden_mul_phi_coords]
```

として本 theorem を直接使用している。

したがって依存の流れは概略

```text
goldenMul + goldenPhi
        ↓
golden_mul_phi_coords
        ↓
goldenUnit_descent
        ↓
goldenUnitFifthClass_of_unit
        ↓
goldenUnitClassesModFifth
```

となる。

0352 は単なる便利な座標展開ではなく、unit classification の有限降下を整数座標上の不等式へ翻訳するための計算インターフェースである。

## 直接依存する定義・補題

本 theorem が直接参照する主要宣言は次の通りである。

- `GoldenInt` — 黄金整数を二つの整数座標で表す型。
- `goldenPhi` — 基底元 $\varphi$。定義は `⟨0,1⟩`。
- `goldenMul` — $\varphi^2=\varphi+1$ で簡約した黄金整数の乗法。

`goldenMul` の定義は

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

である。

ここに `y = goldenPhi = ⟨0,1⟩` を代入すると、第一座標は

$$
a\cdot 0+b\cdot 1=b
$$

第二座標は

$$
a\cdot 1+b\cdot 0+b\cdot 1=a+b
$$

となり、主張の右辺が得られる。

証明本文では別の数学補題を利用せず、これらの定義展開と整数環の簡約だけで閉じる。

## 証明または構築の流れ

証明は

```lean
by
  ext <;> simp [goldenMul, goldenPhi]
```

の一行である。

流れは次の通り。

1. `ext` により `GoldenInt` 同士の等式を座標ごとの等式へ分解する。
2. `<;>` により、生成されたすべての座標目標へ同じ `simp` を適用する。
3. `simp [goldenMul, goldenPhi]` が乗法と $\varphi$ の定義を展開する。
4. $0$、$1$ との整数演算を簡約し、各座標を反射的等式まで落とす。

概念的には Lean が

```text
fst coordinate:
  a * 0 + b * 1 = b

snd coordinate:
  a * 1 + b * 0 + b * 1 = a + b
```

を処理している。

## Lean 固有の処理

### `ext` による structure equality の分解

`GoldenInt` は複数 field を持つ座標 structure であるため、

```lean
ext
```

により

```lean
lhs.fst = rhs.fst
lhs.snd = rhs.snd
```

という field equality に分解できる。

この theorem では抽象的な環同値を使うより、座標 structure の extensionality を直接使う方が短い。

### `<;>` による全 subgoal への tactic 適用

```lean
ext <;> simp [...]
```

の `<;>` は、`ext` が生成したすべての subgoal に後続の `simp` を適用する。二座標とも同じ定義展開で解けるため適切な記法である。

### `simp` による closed coordinate simplification

ここで `simp` が担当するのは、未知の数学的事実の探索ではない。`goldenMul` と `goldenPhi` を展開し、整数環における $0$ と $1$ の単純化を行うだけである。

そのため本証明の核は自動化というより、正しい座標表現を定義したこと自体にある。

## 冗長・重複箇所

本 theorem 自身は短く、目立った冗長性はない。

ただし後続には対となる

```lean
theorem golden_mul_phiInv_coords (x : GoldenInt) :
    goldenMul x goldenPhiInv = ⟨x.snd - x.fst, x.fst⟩ := by
  ...
```

が存在する。両者は unit descent の二方向の座標変換を与えるため、数学的には一対の変換行列としてまとめる余地がある。

例えば

$$
M_\varphi=
\begin{pmatrix}
0&1\\
1&1
\end{pmatrix}
$$

と

$$
M_{\varphi^{-1}}=
\begin{pmatrix}
-1&1\\
1&0
\end{pmatrix}
$$

を導入すれば、二つの座標 theorem を行列作用として統一できる。

ただし現在の証明では後続の `omega` / `natAbs` 不等式へ具体座標を直接渡すことが重要であり、行列表現を挟むとむしろ proof term が重くなる可能性がある。したがってこれは局所的な短縮ではなく、将来の抽象化候補である。

## 最適化候補

現行証明は十分に小さい。考えられる候補は次の通りである。

1. `goldenMul` に関する既存 `[simp]` lemma が十分整備されているなら、展開指定をさらに減らせる可能性がある。
2. 本 theorem を `[simp]` lemma として登録すれば、後続で `rw [golden_mul_phi_coords]` と明示している箇所を自動簡約できる可能性がある。
3. ただし `[simp]` 化は `goldenMul x goldenPhi` を常に座標 constructor へ展開するため、抽象的な乗法形を保持したい証明では過剰展開になる可能性がある。
4. `golden_mul_phiInv_coords` と合わせて「unit generator multiplication の coordinate action」という小さな API として整理する余地がある。

2 は便利そうに見えるが、simp normal form をどう設計するかに関わるため、実際の後続 proof 全体をビルドして判断すべきである。

## 必要 Mathlib import と import 最適化候補

生成 standalone `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem 自身が直接必要とするのは主として

- structure extensionality を使う `ext`
- simplifier `simp`
- 整数の加法・乗法・$0$・$1$ に関する基礎 simp lemma
- 前段で定義された `GoldenInt`、`goldenMul`、`goldenPhi`

である。

`ring`、`omega`、`norm_num` は本 theorem では使用しない。

したがって theorem 単体では `Mathlib` 全体よりかなり小さな import で足りる可能性が高い。しかし `GoldenInt` の structure、整数環 instance、extensionality lemma、およびプロジェクト内モジュール境界まで含めた **厳密な最小 import は Lean ビルドなしでは確認できない**。

今回はビルドを行わないため、具体的な最小 import 名は未確認とする。

## Comparator challenge 化の可否

**適している。難度は初級から初中級。**

例えば次の goal を与えられる。

```lean
example (x : GoldenInt) :
    goldenMul x goldenPhi = ⟨x.snd, x.fst + x.snd⟩ := by
  ?_
```

`goldenMul` と `goldenPhi` の定義を利用可能にしておけば、期待解は

```lean
ext <;> simp [goldenMul, goldenPhi]
```

である。

challenge の評価点は

- structure equality を `ext` で分解できるか
- 定義展開が必要なことを認識できるか
- 不要な `ring` や大規模 automation を使わず `simp` で閉じられるか
- $\varphi^2=\varphi+1$ がすでに `goldenMul` の定義へ組み込まれていることを読めるか

にある。

より難しくするなら右辺を伏せて、乗算結果の座標自体を推定させる challenge にできる。ただし Comparator の通常形式では目標型が固定されるため、本 theorem そのものは小さく明快な micro challenge に向く。

## 次に読むべき宣言

次は **0353 `golden_mul_phiInv_coords`** を読むべきである。宣言種別は **`theorem`**。

```lean
theorem golden_mul_phiInv_coords (x : GoldenInt) :
    goldenMul x goldenPhiInv = ⟨x.snd - x.fst, x.fst⟩ := by
  ext <;> simp [goldenMul, goldenPhiInv]
```

数学的には

$$
(a+b\varphi)(\varphi-1)
=(b-a)+a\varphi
$$

であり、座標変換

$$
(a,b)\longmapsto(b-a,a)
$$

を与える。

0352 の

$$
(a,b)\longmapsto(b,a+b)
$$

と合わせると、$\varphi$ と $\varphi^{-1}$ による互いに逆向きの座標移動が揃う。後続の `goldenUnit_descent` は符号と大小関係に応じてこの二方向のどちらかを選び、`goldenUnitMeasure` を厳密に減少させる。