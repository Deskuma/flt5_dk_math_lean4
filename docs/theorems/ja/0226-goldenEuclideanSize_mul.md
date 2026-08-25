# 0226 — `goldenEuclideanSize_mul`

## Lean の型

```lean
theorem goldenEuclideanSize_mul (x y : GoldenInt) :
    goldenEuclideanSize (goldenMul x y) =
      goldenEuclideanSize x * goldenEuclideanSize y := by
  change (goldenNorm (goldenMul x y)).natAbs =
    (goldenNorm x).natAbs * (goldenNorm y).natAbs
  rw [goldenNorm_mul, Int.natAbs_mul]
```

これは `theorem` であり、0224 で定義された自然数値 Euclidean size が黄金整数の乗法に対して乗法的であることを示す。

## 数学的主張

0224 では

$$
\operatorname{size}(x)=|N(x)|\in\mathbb N
$$

と定義した。0174 `goldenNorm_mul` により黄金ノルムは

$$
N(xy)=N(x)N(y)
$$

を満たす。したがって整数絶対値の乗法性から

$$
\operatorname{size}(xy)
=|N(xy)|
=|N(x)N(y)|
=|N(x)|\,|N(y)|
=\operatorname{size}(x)\operatorname{size}(y)
$$

となる。本 theorem はこの事実を `Int.natAbs` を用いた自然数値 measure に対して Lean 上で公開する。

## 証明全体での役割

0224–0226 は `GoldenInt` に Euclidean measure を与える block である。

- 0224 `goldenEuclideanSize` — `|N(x)|` を自然数値 size として定義する。
- 0225 `goldenEuclideanSize_pos_of_ne_zero` — 非零元では size が正であることを保証する。
- 0226 本 theorem — size が乗法的であることを保証する。

この二つの性質は、最終 `EuclideanDomain GoldenInt` instance の relation

```lean
r := fun a b => goldenEuclideanSize a < goldenEuclideanSize b
```

が乗法と整合することを示すために直接使われる。特に `mul_left_not_lt` では、非零 `b` に対して 0225 から

$$
1\le \operatorname{size}(b)
$$

を得て、本 theorem により

$$
\operatorname{size}(ab)
=\operatorname{size}(a)\operatorname{size}(b)
\ge \operatorname{size}(a)
$$

とすることで、左乗法後に measure が不正に小さくなることを排除する。

また後続では remainder の strict decrease

$$
\operatorname{size}(r)<\operatorname{size}(y)
$$

を証明するため、`goldenEuclideanSize` を最終的な比較尺度として固定する。0226 はこの尺度が黄金整数環の乗法構造と一致することを保証する基礎 theorem である。

## 直接依存する定義・補題

直接依存は次の通りである。

- 0224 `goldenEuclideanSize`
- 0174 `goldenNorm_mul`
- Mathlib の `Int.natAbs_mul`
- 0124 `goldenMul`

概念的な依存は

$$
N(xy)=N(x)N(y)
\Longrightarrow
|N(xy)|=|N(x)|\,|N(y)|
\Longrightarrow
\operatorname{size}(xy)=\operatorname{size}(x)\operatorname{size}(y)
$$

である。

黄金整数固有の代数的内容は 0174 に既に封じ込められており、本 theorem はそれを `ℤ` から `ℕ` の Euclidean measure へ transport する薄い層である。

## 証明の流れ

proof は二段階である。

まず

```lean
change (goldenNorm (goldenMul x y)).natAbs =
  (goldenNorm x).natAbs * (goldenNorm y).natAbs
```

によって `goldenEuclideanSize` の定義を展開した形へ goal を変更する。

次に

```lean
rw [goldenNorm_mul, Int.natAbs_mul]
```

で、

1. `goldenNorm_mul` により `goldenNorm (goldenMul x y)` を `goldenNorm x * goldenNorm y` へ書き換える。
2. `Int.natAbs_mul` により整数積の自然数絶対値を積へ分配する。

これで両辺が同一になり proof が閉じる。

## Lean 固有の処理

`change` が使われている点が重要である。goal の表面は `goldenEuclideanSize` だが、定義的には `Int.natAbs (goldenNorm ...)` なので、証明者は theorem rewrite が直接適用できる内部形を明示している。

この手法により、`unfold goldenEuclideanSize` を全体へ適用するよりも、証明意図を局所的に保てる。

また `Int.natAbs_mul` は値域が `ℕ` であるため、符号付きノルムの符号問題を完全に吸収する。黄金ノルムは `N(φ)=-1` のように負にもなりうるが、Euclidean measure ではその符号を捨てて乗法的な自然数尺度へ変換できる。

## 冗長・重複箇所

数学的には 0174 `goldenNorm_mul` と `Int.natAbs_mul` の直接合成なので、新しい黄金整数算術はほとんど含まない。

しかし API 上は重要な wrapper である。最終 Euclidean-domain 構築は `goldenNorm` ではなく `goldenEuclideanSize` を relation の measure として使うため、下流で毎回

```lean
rw [goldenEuclideanSize, goldenNorm_mul, Int.natAbs_mul]
```

と展開するより、本 theorem を named interface として持つ方が明瞭である。

0225 と同様、これは「整数ノルム層」と「自然数 Euclidean measure 層」の境界を吸収する theorem と解釈できる。

## 最適化候補

1. **現行 proof を維持する**
   - `change` + `rw` の二段階で依存が明瞭で、十分に短い。

2. **`simpa [goldenEuclideanSize] using congrArg Int.natAbs (goldenNorm_mul x y)` を試す**
   - ただし `Int.natAbs_mul` の正規化が追加で必要になるため、現行より簡潔とは限らない。Lean build 未検証の候補である。

3. **`goldenEuclideanSize` を multiplicative map として bundle する**
   - 後続で size の乗法性を頻繁に利用するなら `MonoidHom` 的 API にまとめる余地がある。

4. **ノルムから Euclidean measure を作る一般 helper を抽象化する**
   - 他の二次整数環でも `size = natAbs ∘ norm` を使うなら再利用価値がある。

現行 theorem は最終 instance の構築意図が読みやすく、局所的な最適化の優先度は低い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が直接必要とする Mathlib 表面は主に

- `Int.natAbs_mul`
- 基本的な definitional equality / `change`
- equality rewrite

である。

黄金整数固有の `goldenNorm_mul`、`goldenEuclideanSize`、`goldenMul` は同一開発の上流宣言である。

宣言単独なら `Mathlib` 全体より小さい import で足りる可能性が高い。ただし `GoldenEuclidean.lean` 全体では rational rounding、`field_simp`、`nlinarith`、well-founded measure、Euclidean-domain typeclass などを利用するため、実際の import 最適化は module 単位で測る必要がある。今回は Lean build を行わないため最小 import 集合は未検証である。

## Comparator challenge 化の可否

適している。比較候補は、

- A: 現行 `change` + `rw`
- B: `unfold goldenEuclideanSize` + `simp [goldenNorm_mul, Int.natAbs_mul]`
- C: `simpa` 中心の proof
- D: `goldenEuclideanSize` を multiplicative map として bundle し generic `map_mul` を使う設計

比較軸は proof term の短さ、定義展開の可視性、Mathlib 標準 API 再利用率、下流 instance 構築での読みやすさ、一般化可能性である。

現行 A は `ℤ` の norm から `ℕ` の measure への境界が最も明示的で、監査性が高い。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

正本 source では、

```lean
theorem goldenEuclideanSize_pos_of_ne_zero ...

theorem goldenEuclideanSize_mul (x y : GoldenInt) :
    goldenEuclideanSize (goldenMul x y) =
      goldenEuclideanSize x * goldenEuclideanSize y := by
  change (goldenNorm (goldenMul x y)).natAbs =
    (goldenNorm x).natAbs * (goldenNorm y).natAbs
  rw [goldenNorm_mul, Int.natAbs_mul]

private theorem goldenRemainder_norm_rat_identity ...
```

という順序を確認した。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0227 `goldenRemainder_norm_rat_identity`** である。これは `private theorem` である。

```lean
private theorem goldenRemainder_norm_rat_identity
    (x y : GoldenInt) (hy : y ≠ 0) :
    (goldenNorm (goldenRemainder x y) : ℚ) =
      (goldenNorm y : ℚ) *
        goldenRatNorm
          ((goldenQuotientCoords x y).1 - (goldenQuotient x y).fst,
           (goldenQuotientCoords x y).2 - (goldenQuotient x y).snd) := by
  ...
```

0224–0226 で Euclidean size の基礎性質が揃った後、0227 は remainder のノルムを

$$
N(r)=N(y)\,Q(\text{quotient rounding error})
$$

という有理数恒等式へ分解する。これが 0214 の fundamental-cell bound $|Q|<1$ と直接結合し、remainder の strict size decrease を導く中心的な橋となる。