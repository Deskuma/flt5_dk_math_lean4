# 0097 — `four_mul_goldenNorm_eq_discriminant_five`

## Lean の型

```lean
theorem four_mul_goldenNorm_eq_discriminant_five (m n : ℤ) :
    4 * GoldenNorm m n = (2 * m + n) ^ 2 - 5 * n ^ 2 := by
  unfold GoldenNorm
  ring
```

## 数学的主張

`GoldenNorm m n = m^2 + mn - n^2` に対して、

$$
4\,\mathrm{GoldenNorm}(m,n)=(2m+n)^2-5n^2
$$

が成り立つ。右辺を展開すると $4m^2+4mn-4n^2$ であり、左辺と一致する。これは二次形式を判別式 $5$ の対角形へ移す恒等式である。

## 証明全体での役割

0096 で `GN5` は endpoint-square 座標上の `GoldenNorm` と結ばれた。本 theorem はその `GoldenNorm` をさらに

$$
X^2-5Y^2
$$

型へ移し、黄金比型二次形式に判別式 $5$ が内在することを明示する。ソースの module comment でも、この diagonalization が elementary cyclotomic factorization から後続 `GoldenOrder` への algebraic bridge と説明されている。

## 直接依存する定義・補題

直接依存する project-local 宣言は `GoldenNorm : ℤ → ℤ → ℤ` のみ。0096 は証明本文では使われない。Mathlib 側では整数環の基本演算、冪、`ring` tactic を利用する。

## 証明の流れ

```lean
unfold GoldenNorm
ring
```

まず `GoldenNorm` を展開し、目標を

$$
4(m^2+mn-n^2)=(2m+n)^2-5n^2
$$

という整数上の多項式恒等式へ変える。あとは `ring` が正規化して閉じる。

## Lean 固有の処理

本 theorem は最初から `ℤ` 上なので、0096 のような `push_cast` は不要である。`unfold GoldenNorm` で named abstraction を開き、`ring` で減法を含む可換環上の恒等式を処理する。

## 冗長・重複箇所

証明自体は二行で冗長性はほぼない。ただし一般の二次形式 $ax^2+bxy+cy^2$ には

$$
4a(ax^2+bxy+cy^2)=(2ax+by)^2-(b^2-4ac)y^2
$$

という一般恒等式があり、本 theorem は $a=1,b=1,c=-1$、判別式 $5$ の特殊例である。複数の二次形式で同型計算が現れるなら一般化候補になる。

## 最適化候補

1. 現状維持。最短で依存も少ない。
2. 一般 binary quadratic discriminant identity を作り、本 theorem を特殊化する。
3. `2*m+n` を後続で頻用するなら discriminant coordinate helper を導入する。
4. 後段の `GoldenOrder` norm と接続する。ただし elementary algebra layer として本 theorem を残す価値は高い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用する。本 theorem 単体なら整数の commutative ring structure、冪、`ring` tactic が主な要件で、umbrella import は過大である可能性が高い。ただし同じ `SquareGoldenBridge.lean` 区間には `push_cast` や `norm_num` を使う theorem もあるため、module 全体の最小 import は Lean build なしには断定しない。

## Comparator challenge 化の可否

適している。比較候補は、現行の `unfold; ring`、`calc` で平方展開を露出する方式、一般 discriminant identity を先に証明して特殊化する方式。評価軸は行数、一般性、数学的説明力、依存数、後続再利用性である。

## 既存資料との対応

形式的な最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` であり、generated source marker から `DkMath/FLT/Five/SquareGoldenBridge.lean` 区間の定理と確認できる。

既存の日英 PDF については GitHub code search が今回 upstream 502 となり、具体的ページ・節番号は確定できなかった。推測では補っていない。

## 次に読むべき定理

直後は

```lean
theorem endpoint_square_discriminant (z y : ℤ) :
    (z ^ 2 + y ^ 2) ^ 2 - 4 * (z * y) ^ 2 =
      (z ^ 2 - y ^ 2) ^ 2 := by
  ring
```

である。0097 が黄金ノルム側の判別式 $5$ を露出するのに対し、次号は endpoint-square 座標が保持する独立な平方判別式を読む。