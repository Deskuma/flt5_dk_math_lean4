# 0209 — `GoldenRat`

## Lean の型

```lean
/-- Rational coordinates in the basis `1, phi`. -/
abbrev GoldenRat := ℚ × ℚ
```

これは theorem ではなく `abbrev` であり、黄金整数の基底 `1, φ` に関する有理座標を、単純な直積型 `ℚ × ℚ` として与える。

## 数学的主張・宣言の意味

`GoldenInt` が整数座標

$$
a+b\varphi,\qquad a,b\in\mathbb Z
$$

を表すのに対し、`GoldenRat` は同じ基底を使って

$$
u+v\varphi,\qquad u,v\in\mathbb Q
$$

を表す有理座標空間である。

ここで重要なのは、`GoldenRat` を新しい代数構造として構築しているのではなく、Euclidean division の中間計算に必要な quotient 座標だけを `ℚ × ℚ` で保持している点である。`abbrev` なので Lean から見れば本質的に `ℚ × ℚ` と同一であり、`.1` と `.2` による標準の直積射影をそのまま利用できる。

## 証明全体での役割

0208 `GoldenRelPrime` までで黄金整数の divisibility / unit / relative-primality API が整った。0209 から始まる `GoldenEuclidean.lean` は、それをさらに Mathlib の `EuclideanDomain` 構造へ持ち上げる段階である。

module 冒頭コメントでは、黄金整数 $x,y$ の有理 quotient を基底 `1,φ` の二座標で表し、その二座標を最寄りの整数へ丸めることで quotient candidate を作る、と説明されている。丸め誤差を

$$
|u|,|v|\le \frac12
$$

に入れた後、黄金ノルム二次形式

$$
u^2+uv-v^2
$$

が fundamental cell 上で

$$
\left|u^2+uv-v^2\right|\le \frac5{16}<1
$$

になることを使い、remainder の絶対ノルムが divisor より厳密に小さいことを証明する。

`GoldenRat` はこの proof の最初の型レベルの足場であり、整数環 `GoldenInt` と整数商の間に一時的な有理座標空間を置く。

## 直接依存する定義・補題

宣言そのものの直接依存は非常に小さい。

- 有理数型 `ℚ`
- 直積型 `Prod`
- `abbrev`

project-local theorem や tactic には依存しない。

ただし意味上は、`GoldenInt` が基底 `1,φ` の整数座標であることを前提としており、同じ座標系を `ℚ` へ拡張したものとして読む。

## 構築の流れ

構築は一行だけである。

```lean
abbrev GoldenRat := ℚ × ℚ
```

新しい constructor や coercion は作らず、既存の pair をそのまま再利用する。したがって後続では

```lean
x.1
x.2
```

によって第一・第二有理座標を直接参照できる。

## Lean 固有の処理

`abbrev` は通常の `def` より透明な別名として扱われる。`GoldenRat` を使って記述した theorem でも、必要に応じて Lean はこれを `ℚ × ℚ` として展開できる。

この設計により、`Prod` に既存の API、projection、equality、simp support を再利用でき、Euclidean division の補助座標のためだけに専用 `structure` を増やさずに済む。

一方で型安全性の観点では、任意の rational pair と「黄金基底の quotient 座標」を型で区別しない。ここでは proof-local な補助表現であるため、その軽量さを優先した設計と読める。

## 冗長・重複箇所

`GoldenRat` は `ℚ × ℚ` の単なる alias なので、論理的な表現力は増えていない。直接 `ℚ × ℚ` と書くことも可能である。

それでも専用名には意味がある。

- 座標が黄金基底 `1,φ` に関するものだと読み取れる。
- 後続の `goldenRatNorm` などに domain-specific な型名を与えられる。
- Euclidean division の rational-coordinate layer を `GoldenInt` の integer-coordinate layer と区別できる。

したがってこれは数学的冗長性ではなく、軽量な semantic alias としての冗長性である。

## 最適化候補

1. **現行 `abbrev` を維持する**
   - 最小の実装で、`Prod` API を完全に再利用できる。

2. **専用 `structure GoldenRat` を導入する**
   - `fst/snd` を意味のある field 名へ変更できるが、constructor / ext / coercion 等の API が増える。

3. **一般 quadratic-coordinate 型へ抽象化する**
   - `ℤ[φ]` だけでなく、一般の二次基底に対する Euclidean cell proof を再利用したい場合に有効。

4. **`GoldenInt` の scalar extension として構造化する**
   - module / tensor / quadratic algebra に寄せれば数学的には自然だが、この局所的 rounding proof には抽象化が重すぎる可能性が高い。

現行の目的は nearest-integer rounding と二次形式評価なので、`abbrev` は非常に合理的である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本宣言単独に必要なのは、実質的に `ℚ` と `Prod` の基本定義だけである。

ただし直後の `exists_int_near_rat` は `round` と `abs_sub_round`、その後は絶対値、不等式、`nlinarith`、整数・有理数 cast、Euclidean-domain 構築を使う。そのため `GoldenEuclidean.lean` 全体の最小 import は本宣言単独よりかなり広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 `abbrev GoldenRat := ℚ × ℚ`
- B: 専用 `structure GoldenRat` with named coordinates
- C: `GoldenInt` と共通の parametric coordinate structure
- D: quadratic-algebra / scalar-extension ベースの抽象表現

比較軸は、proof 行数、simp の容易さ、projection の可読性、型安全性、一般化可能性、Euclidean remainder proof の透明性である。

特に A と B の比較は、「proof-local な座標型に専用 structure を与える価値があるか」を測る小さな Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

source の module コメントでは、rational quotient の二座標を丸め、fundamental cell 上の golden norm bound `5/16 < 1` から strict remainder contraction を得て、最終的に `GoldenInt` を `EuclideanDomain` にする方針が明示されている。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 `abbrev` に対応する具体的な PDF ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0210 `goldenRatNorm`** である。

```lean
/-- The golden norm polynomial on rational coordinates. -/
def goldenRatNorm (x : GoldenRat) : ℚ :=
  x.1 ^ 2 + x.1 * x.2 - x.2 ^ 2
```

0209 が rational coordinate space を用意し、0210 は整数版 `goldenNorm` と同じ二次形式を `ℚ` 上へ拡張する。これが rounding error cell の収縮率を評価する中心量になる。