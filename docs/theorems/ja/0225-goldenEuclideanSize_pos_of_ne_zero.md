# 0225 — `goldenEuclideanSize_pos_of_ne_zero`

## Lean の型

```lean
theorem goldenEuclideanSize_pos_of_ne_zero {x : GoldenInt} (hx : x ≠ 0) :
    0 < goldenEuclideanSize x := by
  rw [goldenEuclideanSize, Int.natAbs_pos]
  exact goldenNorm_ne_zero_of_ne_zero hx
```

これは `theorem` であり、非零な黄金整数の Euclidean size が正の自然数になることを示す。

## 数学的主張

0224 で

$$
\operatorname{size}(x)=|N(x)|\in\mathbb N
$$

と定義した。ここで黄金ノルムは

$$
N(a+b\varphi)=a^2+ab-b^2\in\mathbb Z
$$

である。本 theorem の主張は

$$
x\neq0\Longrightarrow 0<|N(x)|.
$$

黄金整数環では 0215 `goldenNorm_ne_zero_of_ne_zero` により

$$
x\neq0\Longrightarrow N(x)\neq0
$$

が既に証明されている。したがって整数ノルムの自然数絶対値 `Int.natAbs` は正になり、Euclidean size が非零元上で厳密に正であることが従う。

## 証明全体での役割

0220–0223 で quotient / remainder と再構成則が整備され、0224 で Euclidean measure

$$
\operatorname{size}(x)=|N(x)|
$$

が定義された。本 theorem はその measure が非零元を `0` に潰さないことを保証する。

この正性は最終的な `EuclideanDomain GoldenInt` 構築で直接使われる。正本 source の `mul_left_not_lt` 証明では、非零 `b` に対して

```lean
have hbSize : 1 ≤ goldenEuclideanSize b :=
  goldenEuclideanSize_pos_of_ne_zero hb
```

とし、続く 0226 `goldenEuclideanSize_mul` と合わせて

$$
\operatorname{size}(a)
\le
\operatorname{size}(a)\operatorname{size}(b)
=
\operatorname{size}(ab)
$$

を得る。つまり 0225 は単なる sanity check ではなく、Euclidean relation が左乗法で不正に小さくならないことを支える基礎 certificate である。

また remainder の strict decrease を自然数 `<` として読む際にも、非零 divisor の size が少なくとも `1` であることが measure の離散性を保証する。

## 直接依存する定義・補題

直接依存は次の三つである。

- 0224 `goldenEuclideanSize`
- 0215 `goldenNorm_ne_zero_of_ne_zero`
- Mathlib の `Int.natAbs_pos`

概念的には

$$
x\neq0
\Longrightarrow
N(x)\neq0
\Longrightarrow
|N(x)|_{\mathbb N}>0
\Longrightarrow
\operatorname{size}(x)>0.
$$

黄金整数固有の重い部分は 0215 に既に封じ込められており、本 theorem は整数 API への軽い transport である。

## 証明の流れ

proof は二段階だけである。

```lean
rw [goldenEuclideanSize, Int.natAbs_pos]
```

まず `goldenEuclideanSize x` を `Int.natAbs (goldenNorm x)` に展開し、`Int.natAbs_pos` によって

```lean
0 < Int.natAbs (goldenNorm x)
```

を

```lean
goldenNorm x ≠ 0
```

へ書き換える。

次に

```lean
exact goldenNorm_ne_zero_of_ne_zero hx
```

で 0215 を適用し、仮定 `hx : x ≠ 0` から必要なノルム非零性を得て閉じる。

## Lean 固有の処理

`Int.natAbs_pos` は整数 `z` について、自然数値絶対値の正性と整数非零性を結ぶ theorem である。ここでは `rw` によって goal の形そのものを変更しているため、証明後半では `ℕ` の不等式を扱わず、`ℤ` の非零命題だけを示せばよい。

これは type boundary の扱いとしてきれいである。

- `goldenNorm x : ℤ`
- `Int.natAbs (goldenNorm x) : ℕ`
- `0 < goldenEuclideanSize x : Prop`

という三層を、既存 theorem だけで接続している。

また theorem の引数 `x` は implicit `{x : GoldenInt}` で、利用時には仮定 `hx` から推論される。そのため final instance では `goldenEuclideanSize_pos_of_ne_zero hb` のように `x` を明示せず呼べる。

## 冗長・重複箇所

数学的には 0215 と 0224 から即座に従う薄い wrapper theorem であり、新しい黄金整数算術を証明しているわけではない。

しかし API 上は有用である。最終 `EuclideanDomain` 構築は `goldenNorm x ≠ 0` ではなく自然数 measure の `0 < goldenEuclideanSize x` を必要とするため、この theorem が整数ノルム層と Euclidean measure 層の境界を一度だけ吸収する。

下流で毎回

```lean
rw [goldenEuclideanSize, Int.natAbs_pos]
exact goldenNorm_ne_zero_of_ne_zero ...
```

と書くより、named theorem として残す方が proof intent が明瞭である。

## 最適化候補

1. **現行 theorem を維持する**
   - 短く、依存も明瞭で、下流 API として読みやすい。

2. **`simpa [goldenEuclideanSize, Int.natAbs_pos]` 形式を試す**
   - 0215 を `using` で渡す一行 proof に圧縮できる可能性がある。
   - exact な elaboration は Lean build 未検証なので候補に留める。

3. **`goldenEuclideanSize_eq_zero_iff` を公開する**
   - `goldenEuclideanSize x = 0 ↔ x = 0` を用意すれば、正性・非零性の両方向を一つの API にまとめられる。

4. **Euclidean measure を一般の norm-to-natAbs helper から構成する**
   - 他の二次整数環にも展開するなら、`N(x) ≠ 0` から `natAbs N(x) > 0` を得る部分を一般化できる。

現行 proof は既に十分小さく、局所最適化の優先度は低い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が直接必要とする Mathlib 表面は主に

- `Int.natAbs_pos`
- 基本的な rewrite / equality machinery

である。

黄金整数固有の `goldenNorm_ne_zero_of_ne_zero` と `goldenEuclideanSize` は同一開発の上流宣言である。

宣言単独なら `Mathlib` 全体よりかなり小さい import で足りる可能性が高い。ただし `GoldenEuclidean.lean` 全体では `round`、有理数算術、`field_simp`、`nlinarith`、well-founded measure、Euclidean-domain 構築など広い API を使うため、実際の import 最適化は module 単位で測る必要がある。今回は Lean build を行わないため最小 import 集合は未検証である。

## Comparator challenge 化の可否

適している。小さい theorem なので proof-style の違いを比較しやすい。

候補は、

- A: 現行 `rw` + `exact`
- B: `simpa [...] using goldenNorm_ne_zero_of_ne_zero hx`
- C: `goldenEuclideanSize_eq_zero_iff` を先に作って自然数正性から導く
- D: 一般化した norm-measure helper を利用する

比較軸は proof term の短さ、型変換の可視性、下流での再利用性、一般化可能性、Mathlib theorem への依存深度である。

A は `ℤ → ℕ` の境界が最も明示的で、監査性が高い。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

正本 source では、

```lean
def goldenEuclideanSize (x : GoldenInt) : ℕ :=
  Int.natAbs (goldenNorm x)

theorem goldenEuclideanSize_pos_of_ne_zero {x : GoldenInt} (hx : x ≠ 0) :
    0 < goldenEuclideanSize x := by
  rw [goldenEuclideanSize, Int.natAbs_pos]
  exact goldenNorm_ne_zero_of_ne_zero hx

theorem goldenEuclideanSize_mul (x y : GoldenInt) :
  ...
```

という順序が確認できる。また final Euclidean-domain instance の `mul_left_not_lt` でも本 theorem が直接使用されている。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0226 `goldenEuclideanSize_mul`** である。

```lean
theorem goldenEuclideanSize_mul (x y : GoldenInt) :
    goldenEuclideanSize (goldenMul x y) =
      goldenEuclideanSize x * goldenEuclideanSize y := by
  change (goldenNorm (goldenMul x y)).natAbs =
    (goldenNorm x).natAbs * (goldenNorm y).natAbs
  rw [goldenNorm_mul, Int.natAbs_mul]
```

0225 が非零元上の measure の正性を確定したのに対し、0226 は

$$
\operatorname{size}(xy)=\operatorname{size}(x)\operatorname{size}(y)
$$

という乗法性を確立する。これらを合わせて最終 `EuclideanDomain` の measure law と左乗法に対する非減少性を支える段階へ進む。