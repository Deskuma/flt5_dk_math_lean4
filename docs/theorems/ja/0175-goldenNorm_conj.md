# 0175 — `goldenNorm_conj`

## Lean の型

```lean
/-- Conjugation preserves the golden norm. -/
theorem goldenNorm_conj (x : GoldenInt) :
    goldenNorm (goldenConj x) = goldenNorm x := by
  simp [goldenNorm, goldenConj]
  ring
```

これは `theorem` であり、黄金整数 `GoldenInt` の共役 `goldenConj` が整数値ノルム `goldenNorm` を保存することを示す。

## 数学的主張または宣言の意味

`GoldenInt` の元を

$$
x=a+b\varphi
$$

と読み、共役を

$$
\overline{\varphi}=1-\varphi
$$

で定めると、0163 `goldenConj` は

$$
(a,b)\longmapsto(a+b,-b)
$$

を実装している。また 0164 `goldenNorm` は

$$
N(a+b\varphi)=a^2+ab-b^2
$$

である。本 theorem は

$$
N(\overline{x})=N(x)
$$

を証明する。

実際、共役後の座標を代入すると

$$
N((a+b)-b\varphi)=(a+b)^2-(a+b)b-b^2=a^2+ab-b^2
$$

となる。二次拡大における norm が Galois 共役で不変である、という標準的な性質の明示座標版である。

## 証明全体での役割

0174 `goldenNorm_mul` が

$$
N(xy)=N(x)N(y)
$$

という乗法性を確立したのに対し、0175 は

$$
N(\overline{x})=N(x)
$$

という共役不変性を与える。これにより `goldenNorm` は黄金整数の乗法と二次対称性の両方に整合する不変量になる。

後続では、共役・積・ノルムを結ぶ `golden_mul_conj`、単元の norm 判定、整除と norm の対応、Euclidean-domain 構築へ進むため、本 theorem は共役側の基本 API として位置付けられる。

概念的には

```text
goldenConj
    │
    ▼
goldenNorm_conj
    │
    ├─ conjugate pair has same norm
    ├─ unit / divisibility arguments
    └─ quadratic-order symmetry
```

という役割を持つ。

## 直接依存する定義・補題

直接依存は次である。

- `GoldenInt`
- 0163 `goldenConj`
- 0164 `goldenNorm`
- `simp`
- `ring`

0170 `goldenConj_invol` や 0171 `goldenConj_mul` は数学的には密接だが、この proof では直接使用しない。0174 `goldenNorm_mul` も直前の重要 theorem だが、本 theorem の証明自体は独立した座標恒等式として閉じている。

## 証明または構築の流れ

proof は二段階である。

```lean
simp [goldenNorm, goldenConj]
ring
```

まず `goldenConj x` を座標 `⟨x.fst + x.snd, -x.snd⟩` へ展開し、それを `goldenNorm` の式へ代入する。

$x.fst=a$、$x.snd=b$ とすれば、左辺は

$$
(a+b)^2+(a+b)(-b)-(-b)^2
$$

となる。`simp` が射影、符号、定義展開を処理し、残った整数多項式恒等式を `ring` が正規化して閉じる。

## Lean 固有の処理

`goldenConj` と `goldenNorm` が明示座標定義なので、抽象的な ring automorphism や norm map を bundle しなくても、`simp` と `ring` だけで証明できる。

この proof は短く監査しやすい一方、「norm が共役で不変なのは norm が共役積から生じるから」という構造的理由は Lean の型構造としては表現していない。数学的構造より座標透明性を優先した実装である。

## 冗長・重複箇所

主な重複候補は、共役に関する law が個別 theorem として分散している点である。

- `goldenConj_invol`
- `goldenConj_mul`
- 後続の加法保存系
- `goldenNorm_conj`

これらは `goldenConj` を `RingEquiv GoldenInt GoldenInt` として bundle すれば、より体系的に管理できる可能性がある。

また `goldenNorm_conj` は座標展開で直接証明しているが、将来的に `golden_mul_conj` と共役の involution を基礎に norm を構造的に定義するなら、共役不変性は一般論から導ける可能性がある。

## 最適化候補

1. 現行の `simp [goldenNorm, goldenConj]; ring` を維持する。
2. `goldenConj` を `RingEquiv` として bundle し、共役保存則を共通 API に寄せる。
3. `goldenNorm` を `x * goldenConj x` の整数成分として構造化し、共役不変性を involution から導く。
4. `AdjoinRoot (X^2-X-1)` や一般 quadratic algebra の conjugation / norm API を再利用する。
5. 既存の二変数 `GoldenNorm` 側に共役座標変換に対する不変性 theorem を置き、structure 版から再利用する。

局所 proof は既に短いため、最適化の主眼は抽象化と API 統合である。

## 必要 Mathlib import と import 最適化候補

本 theorem 自身が直接必要とするのは、整数算術、`simp`、`ring` tactic、および上流の `GoldenInt` / `goldenConj` / `goldenNorm` 定義である。

standalone artifact は `import Mathlib` を使用しているが、本 theorem 単独には過剰である可能性が高い。ただし `GoldenOrder` モジュール全体では `Zsqrtd`、`omega`、`norm_num`、`interval_cases`、各種 algebra typeclass を利用しているため、正確な最小 import は Lean build により module 全体で検証すべきである。今回は build を行わないため、具体的最小集合は未検証とする。

## Comparator challenge 化の可否

適している。

比較候補は、

- explicit coordinate expansion + `ring`
- `goldenConj` を `RingEquiv` 化した構造的 proof
- element-times-conjugate から norm を定義する proof
- `AdjoinRoot` / quadratic algebra の一般 theorem 再利用

である。

比較軸は proof の短さ、定義的透明性、再利用性、共役 law の重複削減、後続の unit / divisibility / Euclidean-domain proof の簡潔さである。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `GoldenOrder` generated source、および直前の 0174 文書が示す source 順である。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在することを確認した。ただし本 theorem に対応する具体的 PDF ページ・節番号は直接特定していないため推測しない。

## 次に読むべき宣言

`goldenNorm_conj` の直後に続く共役・ノルム関係の宣言を、次回必ずリポジトリ正本から再確認して選ぶ。近傍では element と conjugate の積を norm に結ぶ theorem が続くため、0175 で共役不変性を確立した後は

$$
x\overline{x}=N(x)
$$

型の関係へ進む段階になる。