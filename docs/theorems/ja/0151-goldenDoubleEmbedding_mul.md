# 0151 — `goldenDoubleEmbedding_mul`

## Lean の型

```lean
theorem goldenDoubleEmbedding_mul (x y : GoldenInt) :
    goldenDoubleEmbedding x * goldenDoubleEmbedding y =
      (2 : Zsqrtd 5) * goldenDoubleEmbedding (goldenMul x y) := by
  ext <;> simp [goldenDoubleEmbedding, goldenMul] <;> ring
```

これは theorem である。0148 `goldenDoubleEmbedding` が `GoldenInt` の積に対して通常の環準同型そのものではないことを、正確な係数付き乗法公式として記述する。

## 数学的主張・宣言の意味

`GoldenInt` の元を

$$
x=a+b\varphi,\qquad y=c+d\varphi,
$$

とし、$\varphi=(1+\sqrt5)/2$ と読む。0148 の doubled embedding を $E$ と書けば、

$$
E(a+b\varphi)=(2a+b)+b\sqrt5
$$

であり、これは本質的に $2x$ を $\mathbb Z[\sqrt5]$ の座標へ移したものである。

したがって

$$
E(x)E(y)=(2x)(2y)=4xy,
$$

一方で

$$
2E(xy)=2(2xy)=4xy.
$$

ゆえに本 theorem は

$$
E(x)E(y)=2E(xy)
$$

を表す。Lean では `xy` の黄金整数側の積を raw operation `goldenMul x y` として明示している。

これは `goldenDoubleEmbedding` が通常の `RingHom` ではなく、「倍化された埋め込み」であるために生じる補正係数 $2$ を正確に記録した式である。

## 証明全体での役割

本 theorem は、`GoldenInt` の零因子排除を `Zsqrtd 5` 側へ輸送するための中心的な橋である。

直後の

```lean
theorem GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero {x y : GoldenInt}
    (h : x * y = 0) : x = 0 ∨ y = 0 := by
```

では、まず本 theorem を rewrite して

$$
E(x)E(y)=0
$$

を得る。その後 `Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero` により

$$
E(x)=0\quad\text{or}\quad E(y)=0
$$

へ分解し、0150 `goldenDoubleEmbedding_injective` で `GoldenInt` 側の $x=0$ または $y=0$ に戻す。

したがって 0148–0151 の流れは

$$
\text{doubled embedding}
\longrightarrow
\text{nonsquare infrastructure}
\longrightarrow
\text{injectivity}
\longrightarrow
\text{multiplicative compatibility}
$$

であり、その直後に `GoldenInt` の `NoZeroDivisors` / `IsDomain` へ進む。

## 直接依存する定義・補題

直接依存する主要要素は次である。

- `GoldenInt`
- 0124 `goldenMul`
- 0148 `goldenDoubleEmbedding`
- `Zsqrtd 5` の乗法
- `Zsqrtd` の extensionality / 座標 simp API
- `ring` tactic

0149 `goldenFiveNonsquare` と 0150 `goldenDoubleEmbedding_injective` は本 theorem の証明そのものには直接使われない。ただし直後の零因子排除では、本 theorem と 0150 が組になって使われる。

## 証明・構築の流れ

証明は一行に圧縮されている。

```lean
ext <;> simp [goldenDoubleEmbedding, goldenMul] <;> ring
```

流れを分解すると次の通りである。

1. `ext` により `Zsqrtd 5` の等式を実部・虚部の二座標の等式へ落とす。
2. `simp [goldenDoubleEmbedding, goldenMul]` で doubled embedding と黄金整数積の定義を展開し、各座標を整数多項式へ変換する。
3. `ring` が残った可換環上の多項式恒等式を正規化して閉じる。

数学的な内容は $E(x)E(y)=2E(xy)$ だが、Lean では「二次整数環の等式 → 座標等式 → 整数多項式恒等式」という三段階に落としている。

## Lean 固有の処理

`ext` は `Zsqrtd 5` の extensionality を利用し、構造体等式を座標ごとの等式へ変換する。これにより、抽象的な二次整数環の乗法を直接操作せずに済む。

`simp` では `goldenDoubleEmbedding` と `goldenMul` の定義を明示的に unfold する。`Zsqrtd` 側の乗法座標は既存の simp lemma によって展開されるため、最後には `ℤ` 上の多項式等式だけが残る。

`ring` はその多項式恒等式を決定的に処理する。つまり、この theorem は深い自動探索を使うのではなく、定義展開と正規化で閉じる計算証明である。

また RHS の `(2 : Zsqrtd 5)` という型注釈は、自然数リテラル `2` を `Zsqrtd 5` の元として解釈させるための明示的な型固定である。

## 冗長・重複箇所

式の両辺には `goldenDoubleEmbedding` が現れ、さらに係数 `2` が補正として残るため、通常の ring homomorphism law

$$
f(xy)=f(x)f(y)
$$

より見た目は冗長である。しかしこれは 0148 が $x$ ではなく $2x$ を送る設計から必然的に生じるものであり、数学的な冗長ではない。

証明 script の `ext <;> simp [...] <;> ring` は、同種の座標恒等式で繰り返される可能性がある。将来的に doubled embedding 専用の補助 API を整備するなら、こうした定型証明を短縮できる余地はある。

## 最適化候補

主な候補は四つある。

1. 現行どおり、分母を払った doubled embedding を raw function として維持し、係数付き乗法 theorem を明示する。
2. `goldenDoubleEmbedding` の代わりに分数係数を許す対象環へ $x\mapsto x$ 自身を送る真の `RingHom` を構成する。
3. doubled embedding を加法準同型などの structure として包装し、乗法については `E(x)E(y)=2E(xy)` を専用 compatibility field / theorem として管理する。
4. `GoldenInt` を `AdjoinRoot` や quadratic algebra の既存構造として表現し、標準的な埋め込みから同様の恒等式を導く。

現行設計の利点は、すべて整数座標のまま進み、分母 $2$ を証明全体へ持ち込まないことである。零因子排除だけが目的なら、この単純な倍化方式は非常に効率がよい。

## 必要 Mathlib import と import 最適化候補

standalone source は `import Mathlib` を利用している。本 theorem が直接必要とする機能は、`Zsqrtd` の定義と乗法・extensionality、整数環の simp API、`ring` tactic、および上流の `GoldenInt` / `goldenMul` / `goldenDoubleEmbedding` である。

したがって modular source では `Mathlib` 全体より狭い import にできる可能性が高い。ただし `Zsqrtd` の正確な定義モジュールと `ring` tactic の最小 import の組合せは、今回 Lean build を行わないため未検証である。ここは import 最適化候補としての推測であり、確定事項ではない。

## Comparator challenge 化の可否

適している。比較対象として次の方式が考えられる。

- 現行の doubled embedding + 座標 `ext/simp/ring`
- 有理係数または二次体への真の `RingHom`
- `AdjoinRoot` / quadratic algebra ベースの標準埋め込み

比較軸は、零因子排除までに必要な補題数、分母処理の量、`rfl` / `simp` / `ring` の比率、typeclass burden、一般化可能性、証明の監査容易性である。

特に「真の準同型にするため抽象度を上げる」方式と、「係数 $2$ を一つ保持して整数座標の透明性を優先する」現行方式の trade-off を測る良い Comparator challenge になる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `GoldenOrder.lean` generated section である。source では 0150 `goldenDoubleEmbedding_injective` の直後に本 theorem があり、その直後に `GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero` が続く。

対象ブランチには日本語版・英語版 PDF も存在するが、本 theorem に対応する具体的ページ番号は今回直接特定していない。そのため PDF ページ番号・節番号は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
theorem GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero {x y : GoldenInt}
    (h : x * y = 0) : x = 0 ∨ y = 0 := by
  ...
```

である。

0151 までで、`GoldenInt` から `Zsqrtd 5` への doubled embedding について「単射」と「乗法互換性」が揃った。次はそれらを `Zsqrtd` 側の零積分解と組み合わせ、`GoldenInt` 自身に零因子がないことを具体的 theorem として引き戻す段階へ進む。
