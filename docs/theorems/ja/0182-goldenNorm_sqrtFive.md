# 0182 — `goldenNorm_sqrtFive`

## Lean の型

```lean
theorem goldenNorm_sqrtFive : goldenNorm goldenSqrtFive = -5 := by
  norm_num [goldenNorm, goldenSqrtFive]
```

これは `theorem` である。0177 で定義した `goldenSqrtFive : GoldenInt := ⟨-1, 2⟩` の黄金ノルムが `-5` であることを明示する。

## 数学的主張または宣言の意味

`GoldenInt` の座標 `⟨a,b⟩` を

$$
a+b\varphi
$$

と読む。黄金ノルムは 0164 で

```lean
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

と定義されている。0177 の

```lean
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩
```

を代入すると、

$$
N(2\varphi-1)=(-1)^2+(-1)\cdot2-2^2=1-2-4=-5.
$$

したがって theorem は

$$
N(\sqrt5)=-5
$$

に対応する。ここで `goldenSqrtFive` は実数としての平方根関数ではなく、黄金整数環の元 $2\varphi-1$ を表す明示座標要素である。

## 証明全体での役割

0181 `goldenSqrtFive_sq` は

$$
(2\varphi-1)^2=5
$$

を確定した。本 theorem は同じ ramified element のノルムが `-5` であることを与える。

この二本により、`goldenSqrtFive` が「平方すると 5 になる」だけでなく、「ノルムの絶対値が 5 である」ことも明示される。直後には

```lean
theorem goldenTau_eq_phi_mul_sqrtFive :
    goldenTau = goldenMul goldenPhi goldenSqrtFive := by
  decide
```

が続き、`goldenTau = 2+φ` が `φ * goldenSqrtFive` と結び付けられる。その後 `goldenNorm_tau : goldenNorm goldenTau = 5` が現れるため、0182 は norm-five ramification の符号付き側を担う theorem である。

## 直接依存する定義・補題

直接依存は次である。

- `GoldenInt`
- 0164 `goldenNorm`
- 0177 `goldenSqrtFive`
- Mathlib の整数数値正規化 tactic `norm_num`

数学的には 0181 `goldenSqrtFive_sq` と密接に関係するが、Lean proof は 0181 を使用せず、`goldenNorm` と `goldenSqrtFive` を直接展開して閉じている。

## 証明または構築の流れ

証明は

```lean
by
  norm_num [goldenNorm, goldenSqrtFive]
```

だけである。

展開すると、目標は実質的に

```text
(-1 : ℤ)^2 + (-1) * 2 - 2^2 = -5
```

という閉じた整数計算になる。`norm_num` が冪、積、加減算を正規化して証明を完了する。

## Lean 固有の処理

`norm_num [goldenNorm, goldenSqrtFive]` は二つの定義を unfold し、その後の具体的な整数算術を reflection ベースの数値正規化で処理する。

0181 が `by decide` を使って `GoldenInt` の具体的 equality を判定したのに対し、0182 は unfold 後の整数等式を `norm_num` で閉じる。どちらも closed computation だが、証明対象の型に応じて tactic を使い分けている。

## 冗長・重複箇所

数学的には、0181 の平方関係と一般的な norm の性質から 0182 を導出する設計も考えられる。しかし現行 source では、具体座標を直接評価する方が短い。

また 0167 `goldenNorm_phi`、0169 `goldenNorm_ofInt`、0182、後続の `goldenNorm_tau` は、いずれも具体的な代表元に `goldenNorm` を適用して `norm_num` で閉じる同型の proof pattern を持つ。これらは数学的重複というより、代表元ごとの closed certificate 群とみなせる。

## 最適化候補

1. 現行の `norm_num [goldenNorm, goldenSqrtFive]` を維持し、回帰テスト性を優先する。
2. 0181 `goldenSqrtFive_sq` と `golden_mul_conj`、共役の具体式を組み合わせ、構造的に導出する。
3. `goldenNorm` を multiplicative map として bundle し、ramified element のノルム計算を一般 theorem の特殊化にする。
4. `goldenSqrtFive` の性質を一つの structure / namespace にまとめ、平方・共役・ノルムを一括して公開する。
5. 一般二次環の discriminant element に対する norm theorem を抽象化し、`d=5` の特殊化として証明する。

現行方式は一般性は低いが、定義変更を直接検出できる小さな executable certificate として強い。

## 必要 Mathlib import と import 最適化候補

本 theorem が直接使用するのは既存の `GoldenInt` / `goldenNorm` / `goldenSqrtFive` と `norm_num` である。standalone artifact は `import Mathlib` を使用しているが、0182 単独のために Mathlib 全体が必要とは考えにくい。

最小 import 候補としては整数算術と `norm_num` tactic を供給するモジュール群、および上流の `GoldenOrder` 定義が要求する import が中心になる。ただし今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 削減は最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次である。

- concrete coordinates + `norm_num`
- 0181 の平方関係からの導出
- `golden_mul_conj` を経由する構造的証明
- bundled multiplicative norm の特殊化
- generic quadratic-order / discriminant theorem の特殊化

比較軸は proof term の小ささ、数学的説明力、定義変更への耐性、下流での再利用性、必要 import、一般化可能性である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `GoldenOrder` generated source である。source では 0181 `goldenSqrtFive_sq` の直後に本 theorem が置かれ、その次に 0183 `goldenTau_eq_phi_mul_sqrtFive` が続く。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし 0182 に対応する具体的 PDF ページ・節番号は直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は

```lean
theorem goldenTau_eq_phi_mul_sqrtFive :
    goldenTau = goldenMul goldenPhi goldenSqrtFive := by
  decide
```

である。

0178 で `goldenTau = 2+φ`、0177 で `goldenSqrtFive = 2φ-1` を定義した。0183 では

$$
2+\varphi=\varphi(2\varphi-1)
$$

を明示し、`tau` と ramified square-root element が単元 `φ` を介して associate であることへつながる。