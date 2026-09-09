# 0361 — `golden_phi_four_mul_inv_five`

## 宣言種別

この宣言は **`private theorem`** である。

```lean
private theorem golden_phi_four_mul_inv_five :
    goldenPhi ^ 4 * goldenPhiInv ^ 5 = goldenPhiInv := by
  decide
```

`GoldenUnitFifthClass` を `φ⁻¹` 倍したとき、代表指数 `0` を `4` へ巻き戻すための有限 unit-class のラップアラウンド等式を認証する局所補題である。

## Lean の型

```lean
golden_phi_four_mul_inv_five :
  goldenPhi ^ 4 * goldenPhiInv ^ 5 = goldenPhiInv
```

引数を持たない具体的な `GoldenInt` 等式である。

`private` なので、この宣言名は `GoldenUnitClassification.lean` の外部 API として公開するためのものではなく、同一ソース単位内部の補助定理として使われる。

## 数学的主張

`goldenPhiInv` は黄金比 unit `φ` の積逆元を表し、既に

$$
\varphi\varphi^{-1}=1,
\qquad
\varphi^{-1}\varphi=1
$$

が証明されている。

したがって本定理の数学的内容は

$$
\varphi^4(\varphi^{-1})^5=\varphi^{-1}.
$$

指数だけを形式的に見ると

$$
\varphi^4\varphi^{-5}=\varphi^{-1},
$$

すなわち

$$
4-5=-1
$$

という恒等式である。

unit class を fifth powers で割った観点では、

$$
-1\equiv4\pmod5
$$

という剰余指数のラップアラウンドを、実際の `GoldenInt` 等式として固定している。

明示座標で確認すると

$$
\varphi^4=(2,3),
\qquad
(\varphi^{-1})^5=(-8,5),
$$

であり、黄金整数の乗法

$$
(a,b)(c,d)=(ac+bd,\ ad+bc+bd)
$$

を使えば

$$
(2,3)(-8,5)=(-1,1)=\varphi^{-1}
$$

となる。

## 証明全体での役割

0360 `GoldenUnitFifthClass` は

$$
x=\varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\}
$$

という 5 個の unit class を定義した。

この分類を 0359 `goldenUnit_descent` と接続するには、既に fifth class を持つ `x` に `φ` または `φ⁻¹` を掛けても、再び 5 個の代表のどれかへ戻せることを示す必要がある。

`φ⁻¹` 倍について指数 `i=1,2,3,4` なら単純に

$$
i\mapsto i-1
$$

とできる。しかし `i=0` では自然数指数に `-1` を直接置けない。

そこで

$$
\varphi^{-1}
=\varphi^4(\varphi^{-1})^5
$$

と書き、`φ⁻¹` の 5 乗を fifth-power base 側へ吸収する。

つまり

$$
\delta^5\varphi^{-1}
=\varphi^4(\varphi^{-1}\delta)^5
$$

として sector `0` を sector `4` へ戻す。この変形を次の `golden_sector_zero_mul_phiInv` が直接使用する。

本定理は、有限 class の循環

$$
0\xrightarrow{\times\varphi^{-1}}4
$$

を成立させるための最小の代数的認証である。

## 直接依存する定義・補題

本体で名前として直接現れるプロジェクト内宣言は次である。

- `goldenPhi : GoldenInt` — 黄金比 unit `φ`。
- `goldenPhiInv : GoldenInt` — `φ` の整数環内逆元。

また `^` と `*` は `GoldenInt` に与えられた通常の環演算を使用する。これらは explicit API の `goldenPow` / `goldenMul` と整合するよう構成されている。

数学的背景としては、先行する

- `golden_phi_mul_inv`,
- `golden_inv_mul_phi`,
- `goldenUnit_phiInv`,

が `goldenPhiInv` を真に `φ` の逆元として位置づける。ただしこの theorem の Lean 証明項はそれらを明示的には呼ばず、`decide` による具体計算で閉じている。

## 証明の流れ

証明は一行である。

```lean
by
  decide
```

### 1. 命題が完全に具体化されている

変数も仮定もなく、両辺は固定された `GoldenInt` 値である。

### 2. `GoldenInt` の等値判定を計算する

`GoldenInt` は整数座標を持つ具体型なので、等式は decidable である。

Lean は `goldenPhi`、`goldenPhiInv`、冪、乗法を評価し、最終的に左右の座標が一致することを決定手続きで確認する。

概念的には

```text
φ^4 = (2,3)
φInv^5 = (-8,5)
(2,3) * (-8,5) = (-1,1)
φInv = (-1,1)
```

という有限計算を kernel が確認していると読める。

## Lean 固有の処理

### `decide`

この theorem の特徴は、逆元法則を rewrite して代数的に証明するのではなく、命題の `Decidable` instance を使って閉じている点にある。

このような完全具体等式では `decide` は非常に強い。証明スクリプトを短く保ちつつ、結果は通常どおり Lean kernel によって検査される。

一方で、数学的構造として

$$
\varphi^4\varphi^{-5}=\varphi^{-1}
$$

であることはソースだけからは見えにくくなる。その意味で、この解説では `decide` の背後にある指数 mod 5 の意味を明示する価値がある。

### `private theorem`

この補題は後続の sector 遷移を実装するためだけの局所部品である。外部から再利用する一般 theorem ではないため `private` が妥当である。

## 冗長・重複箇所

証明自体に冗長性はほぼない。

ただし数学的には、既に

```lean
goldenPhi * goldenPhiInv = 1
goldenPhiInv * goldenPhi = 1
```

があるため、本定理を `pow` と逆元法則から導くこともできる。

例えば概念的には

$$
\varphi^4(\varphi^{-1})^5
=(\varphi\varphi^{-1})^4\varphi^{-1}
=\varphi^{-1}
$$

という証明が可能である。

現在の `decide` は最短だが、`goldenPhiInv` の逆元としての意味ではなく具体座標表現に依存する。この依存は意図的な実装選択と読める。

## 最適化候補

1. **現状維持** — 完全具体等式なので `by decide` は最小かつ頑健である可能性が高い。
2. **構造的証明へ置換** — `golden_phi_mul_inv` と冪演算の一般法則だけから導けば、`goldenPhi` / `goldenPhiInv` の座標実装が変わっても意味論的に追従しやすくなる。
3. **sector 遷移一般補題へ統合** — exponent modulo 5 を抽象化し、`i=0` の wrap-around を一般的な `Fin 5` の加減算として表せれば、この専用等式を隠せる可能性がある。ただし現在の explicit case split よりコードが重くなる可能性もある。

これらは設計候補であり、Lean ビルドを行っていないため置換後の成立性は未確認である。

## 必要 Mathlib import と import 最適化候補

生成 standalone `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem 単体で必要なのは、既に `GoldenInt` の ring instance、`goldenPhi`、`goldenPhiInv` が利用可能であることに加え、

- 自然数冪 `Pow`,
- 乗法 `Mul`,
- equality の `Decidable`,
- `decide`,

程度である。

したがって `Mathlib` 全体を直接要求する theorem ではない。実モジュール `GoldenUnitClassification.lean` の最小 import は、その前提となる golden-order API と tactic / decision infrastructure に絞れる可能性がある。

ただし厳密な最小 import 集合は Lean ビルドを行っていないため未確認である。

## Comparator challenge 化の可否

**非常に適している。**

challenge としては、定理文を固定して

```lean
private theorem golden_phi_four_mul_inv_five :
    goldenPhi ^ 4 * goldenPhiInv ^ 5 = goldenPhiInv := by
  ?_
```

とするだけでよい。

最短解は

```lean
decide
```

だが、Comparator の観点では次の二種類を比較できる。

- 具体座標計算による `decide` 解。
- 逆元法則と冪法則から導く構造的解。

小さな theorem なので CLI / Web Comparator の双方で扱いやすく、proof-term の簡潔さと抽象度の違いを見る micro challenge に向く。

## 次に読むべき宣言

次は **0362 `golden_sector_zero_mul_phiInv`**、種別は **`private theorem`** である。

```lean
private theorem golden_sector_zero_mul_phiInv (delta : GoldenInt) :
    (goldenPhi ^ 0 * delta ^ 5) * goldenPhiInv =
      goldenPhi ^ 4 * (goldenPhiInv * delta) ^ 5 := by
  rw [mul_pow]
  calc
    (goldenPhi ^ 0 * delta ^ 5) * goldenPhiInv =
        goldenPhiInv * delta ^ 5 := by ring
    _ = (goldenPhi ^ 4 * goldenPhiInv ^ 5) * delta ^ 5 := by
      rw [golden_phi_four_mul_inv_five]
    _ = goldenPhi ^ 4 * (goldenPhiInv ^ 5 * delta ^ 5) := by ring
```

0361 の具体 unit 等式を、任意の fifth-power base `delta` を含む sector 遷移

$$
\delta^5\varphi^{-1}
=\varphi^4(\varphi^{-1}\delta)^5
$$

へ持ち上げる補題である。ここで初めて sector `0 → 4` の wrap-around が `GoldenUnitFifthClass` の実際の witness 変換として完成する。
