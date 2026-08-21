# 0174 — `goldenNorm_mul`

## Lean の型

```lean
/-- The golden norm is multiplicative. -/
theorem goldenNorm_mul (x y : GoldenInt) :
    goldenNorm (goldenMul x y) = goldenNorm x * goldenNorm y := by
  simp [goldenNorm, goldenMul]
  ring
```

これは `theorem` であり、黄金整数環 `GoldenInt` 上の明示ノルム `goldenNorm` が、明示乗法 `goldenMul` に関して乗法的であることを示す。

## 数学的主張または宣言の意味

`GoldenInt` の元を

$$
x=a+b\varphi,\qquad y=c+d\varphi
$$

と読む。ここで $\varphi^2=\varphi+1$ であり、

$$
N(a+b\varphi)=a^2+ab-b^2
$$

と定義されている。

`goldenMul` は

$$
xy=(ac+bd)+(ad+bc+bd)\varphi
$$

を座標として実装する。本 theorem は、この積に対して

$$
N(xy)=N(x)N(y)
$$

が成立することを証明する。

これは 0172–0173 のような representation bridge ではなく、`goldenNorm` が単なる整数値二次形式ではなく、環乗法と整合する **乗法的不変量** であることを確立する最初の本質的なノルム法則である。

## 証明全体での役割

この theorem は黄金整数を使った FLT5 の後半で中心的な橋になる。

直後の `goldenNorm_conj` や `golden_mul_conj` と組み合わせることで、共役とノルムの二次環構造が完成する。また次の `GoldenDivisibility.lean` では、黄金整数の整除

$$
d\mid x
$$

を整数ノルムの整除

$$
N(d)\mid N(x)
$$

へ送る theorem `goldenNorm_dvd_of_goldenDivides` が、本 theorem を直接 `rw [goldenNorm_mul]` して使用している。

さらに `goldenNorm_pow` の帰納法でも `goldenNorm_mul` が使われ、

$$
N(x^n)=N(x)^n
$$

が導かれる。単元判定でも、積が `1` になることからノルム積が `1` になることを取り出すために再利用される。

したがって本 theorem は概念的に

```text
GoldenInt の乗法
      │
      ▼
goldenNorm_mul
      │
      ├─ divisibility → integer divisibility
      ├─ powers → norm powers
      └─ units → norm ±1
```

という複数の下流ルートの基礎になっている。

## 直接依存する定義・補題

直接依存は次である。

- `GoldenInt`
- `goldenMul`
- `goldenNorm`
- 整数環上の多項式恒等式を閉じる `ring` tactic
- 定義展開と単純化に使われる `simp`

0172 `goldenNorm_eq_GoldenNorm` や 0173 `goldenNorm_eq_existing_GoldenNorm` は論理的には関連するが、本 proof では直接使用されない。

また共役 `goldenConj` もこの proof には使われない。すなわち現行実装は

$$
N(x)=x\overline{x}
$$

を経由して乗法性を証明するのではなく、座標式を直接展開して証明している。

## 証明または構築の流れ

proof は二段階である。

```lean
simp [goldenNorm, goldenMul]
ring
```

まず `goldenMul x y` を座標まで展開し、その積の第一座標・第二座標を `goldenNorm` の二次式へ代入する。

$x=(a,b)$、$y=(c,d)$ と略記すれば、左辺は

$$
(ac+bd)^2+(ac+bd)(ad+bc+bd)-(ad+bc+bd)^2
$$

へ展開される。

右辺は

$$
(a^2+ab-b^2)(c^2+cd-d^2)
$$

である。

`simp` は structure projection と定義展開を処理し、最終的に残るのは整数環上の多項式恒等式だけである。`ring` がその正規化を行って等式を閉じる。

概念的には

```text
N(goldenMul x y)
→ 座標積を展開
→ 整数多項式

N(x) * N(y)
→ ノルムを展開
→ 整数多項式

→ ring normal form が一致
```

という流れである。

## Lean 固有の処理

`ring` が有効なのは、`simp [goldenNorm, goldenMul]` の後に残る式が `ℤ` 上の可換環多項式になるからである。

この設計では、抽象的な quadratic-algebra norm API や ring homomorphism を構築せず、最も具体的な座標レベルまで降りて証明する。そのため proof は短い一方、乗法性の理由そのものは tactic の正規化に委ねられている。

また theorem の statement は raw API

```lean
goldenNorm (goldenMul x y)
```

を使っている。既に `golden_mul_eq` があるため、標準 notation 版

```lean
goldenNorm (x * y) = goldenNorm x * goldenNorm y
```

も容易に得られるはずだが、現行 source は explicit coordinate API を正本としている。

## 冗長・重複箇所

主な重複候補は二つある。

1. `goldenNorm_mul` が raw `goldenMul` に対して述べられている一方、`golden_mul_eq` により `goldenMul x y = x * y` が既に利用可能である。
2. 二次環の標準的な証明なら、共役の乗法性 `goldenConj_mul` と積-共役公式 `golden_mul_conj` からノルム乗法性を導く設計も可能である。

ただし source 順では `goldenNorm_mul` が `golden_mul_conj` より前に置かれているため、現行順序で後者から導くと依存順の組み替えが必要になる。

一方、後続の `goldenNorm_pow` や divisibility theorem がこの theorem を再利用しており、下流で乗法性を重複証明してはいない。この再利用は良好である。

## 最適化候補

候補は次である。

1. 現行どおり座標展開 + `ring` を維持する。
2. statement を標準 notation に寄せて

```lean
theorem goldenNorm_mul' (x y : GoldenInt) :
    goldenNorm (x * y) = goldenNorm x * goldenNorm y := by
  ...
```

とし、raw API 版を bridge として残す。
3. `goldenConj` を `RingEquiv` として bundle し、`x * conj x` から norm を定義して乗法性を構造的に得る。
4. 一般 quadratic norm abstraction を導入し、$X^2-X-1$ の quotient / `AdjoinRoot` 側の norm multiplicativity を再利用する。
5. `goldenNorm` を `GoldenNorm x.fst x.snd` の wrapper とし、既存 binary quadratic form 側で乗法性 theorem を共有する。

局所 proof の長さだけなら現行実装は既に非常に短い。最適化の焦点は proof 長ではなく、一般化可能性と API の一貫性である。

## 必要 Mathlib import と import 最適化候補

本 theorem が実際に使う tactic は `simp` と `ring` である。

したがって standalone の `import Mathlib` より狭い import を考えるなら、少なくとも整数基本構造、simp、ring normalization を提供する module が必要になる。

ただし `GoldenOrder.lean` 全体では `Zsqrtd`、`omega`、`norm_num`、`interval_cases`、algebra typeclass 構築なども使われているため、実際の最小 import は module 全体で Lean build により確認すべきである。今回は Lean build を行わないため、具体的な最小 import 集合は未検証とする。

## Comparator challenge 化の可否

適している。

比較候補は、

- explicit coordinate expansion + `ring`
- `goldenConj_mul` と `golden_mul_conj` を利用する構造的 proof
- `RingHom` / `RingEquiv` と norm map を bundle した proof
- `AdjoinRoot (X^2-X-1)` あるいは quadratic algebra の一般 norm theorem を再利用する proof

である。

比較軸は、proof term の短さ、`simp` 依存度、定義的透明性、一般化可能性、後続の divisibility / unit / Euclidean-domain proof に対する API の使いやすさである。

現行方式は最も具体的で監査しやすく、一般化方式は理論構造を再利用しやすい。この trade-off を比較する良い Comparator challenge になる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `DkMath/FLT/Five/GoldenOrder.lean` generated section である。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在することを確認した。ただし、本 theorem に対応する具体的 PDF ページ・節番号は直接特定していないため推測しない。

## 次に読むべき宣言

Lean source 上で直後に置かれている宣言は

```lean
/-- Conjugation preserves the golden norm. -/
theorem goldenNorm_conj (x : GoldenInt) :
    goldenNorm (goldenConj x) = goldenNorm x := by
  simp [goldenNorm, goldenConj]
  ring
```

である。

したがって依存順の次は **0175 `goldenNorm_conj`** とする。

0174 で乗法性 $N(xy)=N(x)N(y)$ を確立したあと、0175 では二次共役がノルムを保存する

$$
N(\overline{x})=N(x)
$$

という第二の基本法則へ進む。
