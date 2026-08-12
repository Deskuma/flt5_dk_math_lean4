# 0098 — `endpoint_square_discriminant`

## Lean の型

```lean
theorem endpoint_square_discriminant (z y : ℤ) :
    (z ^ 2 + y ^ 2) ^ 2 - 4 * (z * y) ^ 2 =
      (z ^ 2 - y ^ 2) ^ 2 := by
  ring
```

## 数学的主張

任意の整数 $z,y$ に対して、

$$
(z^2+y^2)^2-4(zy)^2=(z^2-y^2)^2
$$

が成り立つ。

左辺は、endpoint-square 座標

$$
M=z^2+y^2,\qquad N=zy
$$

に対する判別式型の量

$$
M^2-4N^2
$$

であり、それが完全平方

$$
(z^2-y^2)^2
$$

になることを示している。

これは差の平方の恒等式

$$
(a+b)^2-4ab=(a-b)^2
$$

へ $a=z^2$, $b=y^2$ を代入したものでもある。

## 証明全体での役割

0096 では `GN5` を endpoint-square 座標上の `GoldenNorm` へ移し、0097 では `GoldenNorm` を判別式 $5$ の形へ対角化した。本 theorem はそれとは独立に、同じ endpoint-square 座標が

$$
M^2-4N^2=(z^2-y^2)^2
$$

という完全平方の境界を保持することを記録する。

したがってこの区間では、一つの座標対 $(M,N)$ が同時に二種類の構造を持つ。

1. 黄金ノルム側：`GoldenNorm M N`。
2. square-world 側：$M^2-4N^2$ が完全平方。

この「同じ座標上で golden norm と square discriminant を同時に保存する」という構造が、直後の `SquareGoldenNormalForm.lean` における `BranchBSquareGoldenNormalForm` の設計へつながる。実際、後続 theorem `squareGolden_square_discriminant` は本 theorem を直接再利用している。

## 直接依存する定義・補題

project-local な定義・補題への直接依存はない。型として `ℤ`、整数の加法・減法・乗法・冪を用いるだけである。

証明上は Mathlib の `ring` tactic に依存する。

後続で直接本 theorem を利用する宣言として、`SquareGoldenNormalForm.lean` 区間の

```lean
theorem squareGolden_square_discriminant (z y : ℕ) :
    (SquareGoldenM z y) ^ 2 - 4 * (SquareGoldenN z y) ^ 2 =
      ((z : ℤ) ^ 2 - (y : ℤ) ^ 2) ^ 2 := by
  unfold SquareGoldenM SquareGoldenN
  exact endpoint_square_discriminant (z : ℤ) (y : ℤ)
```

が確認できる。

## 証明の流れ

証明は一行である。

```lean
ring
```

`ring` は両辺を整数上の多項式として正規化する。展開すれば、左辺は

$$
z^4+2z^2y^2+y^4-4z^2y^2
$$

となり、

$$
z^4-2z^2y^2+y^4
$$

へ整理される。右辺

$$
(z^2-y^2)^2
$$

も同じ正規形を持つため閉じる。

## Lean 固有の処理

本 theorem は最初から `ℤ` 上にあるため、自然数から整数への coercion を処理する `push_cast` は不要である。また project-local definition を `unfold` する必要もない。

`ring` を選んでいるため、減法を含む可換環上の恒等式として直接処理できる。`nlinarith` でも周辺仮定を用意すれば処理可能な場合はあるが、この theorem は純粋な恒等式なので `ring` が最も自然である。

Lean 上では `^ 2` が `Pow.pow` を通るが、`ring` が自然数指数の多項式として正規化するため、個別に `pow_two` へ書き換える必要はない。

## 冗長・重複箇所

数学的には一般恒等式

$$
(a+b)^2-4ab=(a-b)^2
$$

の特殊化なので、計算そのものには重複性がある。また後続の `squareGolden_square_discriminant` は `SquareGoldenM` と `SquareGoldenN` を展開した後、本 theorem をそのまま再利用する。

しかし本 theorem を独立して置くことで、`SquareGoldenM/N` という後続の named coordinates から切り離し、「endpoint-square 座標一般の恒等式」として再利用できる。したがって現状の重複は説明層と再利用層を分ける意図的なものと評価できる。

## 最適化候補

1. 現状維持。証明が一行で、意味のある名前を持つため十分に良い。
2. 一般補題 `(a+b)^2 - 4*a*b = (a-b)^2` を用意し、`a=z^2`, `b=y^2` を特殊化する。ただし本 theorem 単独では抽象化コストの方が大きい。
3. endpoint-square 座標を structure としてまとめ、`mass := z^2+y^2`、`cross := zy` と平方判別式を一体化する。後続でこの座標対を頻繁に受け渡すなら有力。
4. `squareGolden_square_discriminant` 側を `[simp]` 展開＋本 theorem の適用として保持し、同じ `ring` 計算を重複させない。現 source は既にこの方針を採用している。

## 必要 Mathlib import と import 最適化候補

対象 standalone artifact は `import Mathlib` を使用している。source manifest 上、本 theorem は `DkMath/FLT/Five/SquareGoldenBridge.lean` 区間に属する。

本 theorem 単体で直接必要なのは、整数の可換環構造、自然数冪、および `ring` tactic である。したがって umbrella `Mathlib` は単独 theorem に対しては過大である可能性が高い。候補として `Mathlib.Tactic.Ring` を中心とした縮小が考えられるが、分割元 module 全体には `push_cast` や `norm_num` を使う theorem もあるため、正確な最小 import 集合は Lean build を行わずには断定しない。

## Comparator challenge 化の可否

適している。ただし難度は基礎寄りである。

比較候補は次の三方式。

1. 現行の `ring` 一発。
2. 一般恒等式 `(a+b)^2-4ab=(a-b)^2` を証明して特殊化。
3. `rw [pow_two]` 等で展開し、`ring_nf` や局所的な書き換えで閉じる。

評価軸は、証明行数、数学的説明力、一般性、依存数、後続 `squareGolden_square_discriminant` への再利用性である。Comparator としては「最短の kernel-checked algebra」と「意味を露出した構造的 proof」の差を比較する教材になる。

## 既存資料との対応

形式的な最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` である。generated source marker により、本 theorem が `DkMath/FLT/Five/SquareGoldenBridge.lean` 区間に属し、その直後に `goldenNorm_eq_fifth_power_of_GN5`、続いて `SquareGoldenNormalForm.lean` が配置されていることを確認した。

既存の日英 PDF については、今回も GitHub code search が upstream 502 を返したため、具体的なページ・節番号を確認できなかった。PDF に関する対応位置は推測で補っていない。

## 次に読むべき定理

source 直後は

```lean
theorem goldenNorm_eq_fifth_power_of_GN5
    {g y b : ℕ} (hGN : GN5 g y = b ^ 5) :
    GoldenNorm
        (↑((g + y) ^ 2 + y ^ 2) : ℤ)
        (↑((g + y) * y) : ℤ) =
      (b : ℤ) ^ 5 := by
  calc
    GoldenNorm
        (↑((g + y) ^ 2 + y ^ 2) : ℤ)
        (↑((g + y) * y) : ℤ) =
        (GN5 g y : ℤ) := (GN5_eq_goldenNorm_squareLink g y).symm
    _ = ((b ^ 5 : ℕ) : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) hGN
    _ = (b : ℤ) ^ 5 := by norm_num
```

である。

本号が endpoint-square 座標に残る独立な完全平方境界を記録するのに対し、次号は `GN5 g y = b^5` という自然数上の fifth-power 情報を、同じ endpoint-square 座標上の `GoldenNorm = b^5` へ輸送する。これにより square-world と golden-norm world の同時保持に必要な二本のデータが揃う。