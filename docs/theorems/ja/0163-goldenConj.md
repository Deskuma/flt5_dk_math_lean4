# 0163 — `goldenConj`

## Lean の型

```lean
/-- The nontrivial conjugation `a+b*φ |-> (a+b)-b*φ`, induced by `φ |-> 1-φ`. -/
def goldenConj (x : GoldenInt) : GoldenInt := ⟨x.fst + x.snd, -x.snd⟩
```

これは theorem ではなく `def` であり、黄金整数環 `GoldenInt` 上の非自明な共役写像を明示座標で定義する。

## 数学的主張または宣言の意味

`GoldenInt` の元を

$$
x=a+b\varphi
$$

と読み、生成元が

$$
\varphi^2=\varphi+1
$$

を満たすとする。この二次方程式のもう一つの根は

$$
\varphi'=1-\varphi
$$

なので、共役は

$$
a+b\varphi\longmapsto a+b(1-\varphi)
$$

である。整理すると

$$
a+b(1-\varphi)=(a+b)-b\varphi
$$

となるため、基底 `1, φ` に関する座標変換は

$$
(a,b)\longmapsto(a+b,-b)
$$

となる。Lean の実装

```lean
def goldenConj (x : GoldenInt) : GoldenInt :=
  ⟨x.fst + x.snd, -x.snd⟩
```

はこの変換をそのまま記述している。

## 証明全体での役割

0161 `goldenPhi` と 0162 `goldenOfInt` で黄金整数環の二本の基底方向が明示された後、0163 はその基底上の非自明な二次共役を導入する。

この共役は、直後の `goldenNorm` と組み合わせて黄金整数算術の中心になる。後続 source では、少なくとも次の性質が証明される。

- `goldenConj goldenPhi = goldenSub goldenOne goldenPhi`
- `goldenConj (goldenOfInt a) = goldenOfInt a`
- `goldenConj (goldenConj x) = x`
- `goldenConj (goldenMul x y) = goldenMul (goldenConj x) (goldenConj y)`
- `goldenNorm (goldenConj x) = goldenNorm x`
- `goldenMul x (goldenConj x) = goldenOfInt (goldenNorm x)`

さらに `GoldenDivisibility.lean` では加法・否定・減算・冪に対する共役の互換性も整備され、単元・ノルム・整除の議論へ使われる。したがって本定義は、単なる座標変換ではなく、後続のノルム乗法性・単元分類・Euclidean-domain 構築へ向かう対称性の入口である。

## 直接依存する定義・補題

直接依存は主に次の通りである。

- `GoldenInt`
- `GoldenInt.fst`
- `GoldenInt.snd`
- 整数加法
- 整数否定

構築自体に theorem は不要で、structure literal によって座標を直接指定する。

意味論上は 0161 `goldenPhi` と 0162 `goldenOfInt` が重要である。前者で非自明な基底元 `φ` を、後者で固定される整数部分を明示しているため、`goldenConj` が「整数を固定し `φ` を `1-φ` へ送る」写像として読める。

## 証明または構築の流れ

証明 script は存在しない。

```lean
def goldenConj (x : GoldenInt) : GoldenInt :=
  ⟨x.fst + x.snd, -x.snd⟩
```

という一行の構築である。

数学的には

$$
a+b\varphi
\longmapsto
(a+b)-b\varphi
$$

を実行している。第一座標へ第二座標を加え、第二座標の符号を反転するだけである。

## Lean 固有の処理

`GoldenInt` は二つの整数 field を持つ structure なので、expected type から `⟨x.fst + x.snd, -x.snd⟩` の constructor が推論される。

重要なのは、現時点の `goldenConj` は `RingHom` や `Equiv` として定義されていないことである。まず raw coordinate function として定義し、その後に

```lean
theorem goldenConj_invol ...
theorem goldenConj_mul ...
```

などを個別に証明する設計になっている。

この方式では、共役の座標意味論が完全に可視であり、`ext <;> simp [goldenConj]` や `ring` によって後続性質を直接検証できる。一方、一般 API から見れば、乗法・加法互換性や involution 性が theorem 群として分散するため、後で structure 化する余地はある。

## 冗長・重複箇所

`goldenConj` 自身の定義に冗長性はほぼない。ただし後続で

- `goldenConj_add`
- `goldenConj_neg`
- `goldenConj_sub`
- `goldenConj_mul`
- `goldenConj_pow`
- `goldenConj_invol`

など多数の互換性 theorem が個別に現れるため、抽象的には「共役は環自己同型で involution」という一つの構造を複数の theorem へ分解している。

これは冗長というより、explicit-coordinate formalization の監査性を優先した設計と解釈できる。FLT5 証明では各性質がどの座標計算から出ているかを追いやすい。

## 最適化候補

1. 現行どおり raw coordinate function を維持し、個別 theorem を積み上げる。
2. `goldenConj` の加法・乗法・単位元保存をまとめた `RingHom GoldenInt GoldenInt` を構成する。
3. involution 性まで含めて `GoldenInt ≃+* GoldenInt` として環自己同型を構成する。
4. 一般 quadratic-order abstraction を導入し、二次多項式の根交換から canonical conjugation を生成する。
5. `AdjoinRoot` / quadratic algebra 系 infrastructure を利用し、既存の conjugation API と接続する。

現行定義は一行で座標作用が完全に見えるため、最適化の目的は行数削減ではなく、downstream theorem の再利用性と generic algebra API への接続をどこまで高めるかにある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 `goldenConj` 単独では、`GoldenInt` と整数加法・否定があれば十分で、高度な Mathlib theorem は直接必要ない。

一方 `GoldenOrder` module 全体では `Zsqrtd`、`ring`、`omega`、`norm_num`、typeclass hierarchy などを利用するため、真の最小 import 集合は module 全体で検証する必要がある。今回は Lean build を行わないため、import 削減は最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補として次の設計が考えられる。

- 現行の raw coordinate function
- `RingHom` として構成した共役
- `RingEquiv` として構成した involutive conjugation
- 一般 quadratic-order abstraction から自動生成する共役
- `AdjoinRoot` / quadratic algebra ベースの共役

比較軸は、座標透明性、`rfl` / `simp` で閉じる補題数、後続 `goldenNorm` theorem の証明量、generic algebra theorem の再利用性、import 依存、コード総量である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる generated `DkMath/FLT/Five/GoldenOrder.lean` section である。source では 0162 `goldenOfInt` の直後に本 `goldenConj` が置かれ、その次に `goldenNorm`、`golden_phi_sq`、`goldenConj_phi` が続く。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在することを確認した。ただし、この一行定義に対応する具体的 PDF ページは直接特定していないため、ページ番号は推測しない。

## 次に読むべき宣言

依存順の次は 0164 `goldenNorm` である。

```lean
/-- The integral norm `N(a+b*φ)=a^2+a*b-b^2`. -/
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

0163 の共役によって `a+bφ` とその共役が揃ったため、次はその積に対応する二次形式

$$
N(a+b\varphi)=a^2+ab-b^2
$$

を明示し、乗法性・共役不変性・単元判定へ進む。