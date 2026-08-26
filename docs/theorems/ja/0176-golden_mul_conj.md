# 0176 — `golden_mul_conj`

## Lean の型

```lean
/-- Multiplication by the conjugate embeds the norm. -/
theorem golden_mul_conj (x : GoldenInt) :
    goldenMul x (goldenConj x) = goldenOfInt (goldenNorm x) := by
  ext <;> simp [goldenMul, goldenConj, goldenOfInt, goldenNorm] <;> ring
```

これは `theorem` であり、黄金整数 `x` とその共役 `goldenConj x` の積が、整数値ノルム `goldenNorm x` を `goldenOfInt` で黄金整数環へ埋め込んだ元に一致することを示す。

## 数学的主張または宣言の意味

`GoldenInt` の元を

$$
x=a+b\varphi
$$

と書く。0163 `goldenConj` により

$$
\overline{x}=(a+b)-b\varphi,
$$

0164 `goldenNorm` により

$$
N(x)=a^2+ab-b^2
$$

である。本 theorem は

$$
x\overline{x}=N(x)
$$

を黄金整数環の内部で表現したものである。ただし右辺の整数 `N(x)` は `goldenOfInt` により

$$
N(x)\longmapsto N(x)+0\varphi
$$

と埋め込まれている。

座標で直接計算すると、第一座標は

$$
a(a+b)+b(-b)=a^2+ab-b^2=N(x),
$$

第二座標は

$$
a(-b)+b(a+b)+b(-b)=0
$$

となる。したがって積は正確に `⟨goldenNorm x, 0⟩` であり、`goldenOfInt (goldenNorm x)` に一致する。

## 証明全体での役割

0174 `goldenNorm_mul` は

$$
N(xy)=N(x)N(y),
$$

0175 `goldenNorm_conj` は

$$
N(\overline{x})=N(x)
$$

を確立した。0176 はそれらに続き、ノルムを元と共役の積そのものへ接続する。

これは黄金整数の算術で非常に重要な橋である。ノルムを単なる二次式ではなく、環内部の因子分解

$$
x\overline{x}=N(x)
$$

として使えるため、共役因子、単元、整除、ramification の議論へ直接移れる。

実際、同じ `GoldenOrder` source の後段では

```lean
theorem golden_tau_mul_conj :
    goldenMul goldenTau (goldenConj goldenTau) = goldenOfInt 5 := by
  rw [golden_mul_conj, goldenNorm_tau]
```

と、本 theorem を `goldenTau` に適用して `tau` とその共役の積を `5` に落としている。したがって 0176 は後続の norm-five ramifier 算術に直接使われる公開 API である。

## 直接依存する定義・補題

直接依存は次である。

- `GoldenInt`
- 0124 `goldenMul`
- 0162 `goldenOfInt`
- 0163 `goldenConj`
- 0164 `goldenNorm`
- `GoldenInt.ext`
- `simp`
- `ring`

0174 `goldenNorm_mul` や 0175 `goldenNorm_conj` は数学的には密接だが、この proof では直接呼び出していない。証明は raw 座標定義を完全に展開して閉じる独立した多項式恒等式である。

## 証明または構築の流れ

proof は一行の tactic chain で書かれている。

```lean
ext <;> simp [goldenMul, goldenConj, goldenOfInt, goldenNorm] <;> ring
```

流れは次の通りである。

1. `ext` で `GoldenInt` の等式を `fst` と `snd` の二座標へ分解する。
2. `simp` で `goldenMul`、`goldenConj`、`goldenOfInt`、`goldenNorm` を展開し、structure projection と符号を整理する。
3. 第一座標では `a^2+ab-b^2`、第二座標では `0` になる整数多項式恒等式が残る。
4. `ring` が両方を正規化して閉じる。

この proof は「共役積の第二座標が消え、第一座標だけに norm が残る」という数学をそのまま座標計算へ落としている。

## Lean 固有の処理

`ext` が使えるのは、上流で `GoldenInt.ext` が用意されているためである。これにより structure equality を直接 constructor equality で処理する必要がない。

また `goldenMul`、`goldenConj`、`goldenNorm` がすべて explicit coordinate definitions なので、抽象的な `RingHom`、`RingEquiv`、quadratic norm API を介さずに `simp` と `ring` だけで証明できる。

一方、左辺は raw operation `goldenMul`、右辺は raw embedding `goldenOfInt` を用いている。0159 `golden_mul_eq` により `goldenMul x y = x * y` は標準乗法と定義的に接続されているが、本 theorem 自身は coordinate API 側の表現を保っている。

## 冗長・重複箇所

最大の構造的重複候補は、`goldenNorm` が最初から二次式

$$
a^2+ab-b^2
$$

として定義され、本 theorem で改めて

$$
x\overline{x}=N(x)
$$

との対応を証明している点である。

別設計では norm を「`x * conj x` の整数成分」として導入できるため、0176 は定義または一般補題に近い形になる。しかし現行設計は整数値 norm を早期から直接計算でき、0174 の乗法性や Euclidean 評価に使いやすい利点がある。

また共役に関して `goldenConj_invol`、`goldenConj_mul`、`goldenNorm_conj` が個別 theorem として存在する。`goldenConj` を `RingEquiv` として bundle すれば、0176 周辺の構造をより一般的な二次環 API に寄せられる可能性がある。

## 最適化候補

1. 現行の `ext <;> simp [...] <;> ring` を維持し、座標透明性を優先する。
2. 標準 notation 版

```lean
x * goldenConj x = (goldenOfInt (goldenNorm x))
```

を主 API にし、raw `goldenMul` 版を bridge とする。
3. `goldenOfInt a` と標準 integer cast `(a : GoldenInt)` の一致 theorem を整備し、右辺を標準 cast に寄せる。
4. `goldenConj` を `RingEquiv GoldenInt GoldenInt` として bundle する。
5. `goldenNorm` を multiplicative map として bundle し、element-times-conjugate law を一般 quadratic-order API として整理する。
6. `AdjoinRoot (X^2-X-1)` や quadratic algebra の既存 conjugation / norm machinery と比較する。

局所 proof は十分短いため、主な最適化対象は proof 長ではなく API の統一と抽象化である。

## 必要 Mathlib import と import 最適化候補

本 theorem が直接必要とするのは、上流の `GoldenInt` 関連定義、structure extensionality、整数多項式の簡約、および `ring` tactic である。

standalone artifact は `import Mathlib` を使用しているが、本 theorem 単独には広すぎる可能性が高い。ただし `GoldenOrder` module 全体では `Zsqrtd`、`omega`、`norm_num`、`interval_cases`、各種 algebra typeclass を利用している。今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、具体的な削減案は候補に留める。

## Comparator challenge 化の可否

適している。

比較候補は、

- explicit coordinate proof (`ext` + `simp` + `ring`)
- bundled `RingEquiv` conjugation を用いる構造的 proof
- norm を element-times-conjugate から定義する設計
- `AdjoinRoot` / quadratic algebra の一般 norm theorem を再利用する設計

である。

比較軸は、proof の短さ、定義的透明性、共役 law の重複、標準 notation との親和性、後続の unit / divisibility / ramification / Euclidean-domain proof の簡潔さである。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `GoldenOrder` generated source である。source 上では 0175 `goldenNorm_conj` の直後に本 theorem が置かれ、その次に `goldenSqrtFive` が続く。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在することを確認した。ただし、本 theorem に対応する具体的 PDF ページ・節番号は直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は

```lean
/-- The ramified square root `2*phi - 1` of five. -/
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩
```

である。

0176 までで `φ`、共役、ノルム、共役積の基本関係が揃った。次からは

$$
2\varphi-1=\sqrt5
$$

に対応する具体的な ramified element を導入し、平方が `5` になる関係、norm `-5`、さらに `tau=2+φ` との関係へ進む。