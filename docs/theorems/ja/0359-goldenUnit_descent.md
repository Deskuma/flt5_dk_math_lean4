# 0359 — `goldenUnit_descent`

## 宣言種別

この宣言は **`theorem`** である。

`GoldenUnitClassification.lean` における unit 分類の中心となる strict descent 定理であり、0352〜0358 で準備した逆元、座標変換、自然数 measure、符号別順序補題を一つに束ねる。

```lean
/-- Every non-base golden unit can be shortened by one multiplication by `phi`
or its integral inverse. -/
theorem goldenUnit_descent {x : GoldenInt} (hx : GoldenUnit x)
    (hlarge : 1 < goldenUnitMeasure x) :
    ∃ y : GoldenInt,
      GoldenUnit y ∧
      goldenUnitMeasure y < goldenUnitMeasure x ∧
      (x = goldenMul y goldenPhi ∨
        x = goldenMul y goldenPhiInv) := by
  have hn : x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2 = 1 ∨
      x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2 = -1 := by
    simpa [goldenNorm] using goldenNorm_eq_one_or_neg_one_of_unit hx
  have ha0 : x.fst ≠ 0 := by
    intro ha
    have hb2 : x.snd ^ 2 = 1 := by
      rcases hn with hn | hn
      · rw [ha] at hn
        norm_num at hn
        nlinarith [sq_nonneg x.snd]
      · rw [ha] at hn
        norm_num at hn ⊢
        exact hn
    have hb : x.snd = 1 ∨ x.snd = -1 := sq_eq_one_iff.mp hb2
    rcases hb with hb | hb <;> simp [goldenUnitMeasure, ha, hb] at hlarge
  have hb0 : x.snd ≠ 0 := by
    intro hb
    have ha2 : x.fst ^ 2 = 1 := by
      rcases hn with hn | hn
      · simpa [hb] using hn
      · simp [hb] at hn
        nlinarith [sq_nonneg x.fst]
    have ha : x.fst = 1 ∨ x.fst = -1 := sq_eq_one_iff.mp ha2
    rcases ha with ha | ha <;> simp [goldenUnitMeasure, ha, hb] at hlarge
  rcases lt_or_gt_of_ne ha0 with ha | ha <;>
    rcases lt_or_gt_of_ne hb0 with hb | hb
  · -- both coordinates are negative
    have hord : -x.fst ≤ -x.snd := by
      apply unit_order_pos_pos (a := -x.fst) (b := -x.snd) <;> try omega
      simpa only [neg_sq, neg_mul_neg] using hn
    let y := goldenMul x goldenPhiInv
    refine ⟨y, goldenUnit_mul hx goldenUnit_phiInv, ?_, ?_⟩
    · dsimp [y]
      change goldenUnitMeasure (goldenMul x goldenPhiInv) < goldenUnitMeasure x
      rw [golden_mul_phiInv_coords]
      simp only [goldenUnitMeasure]
      have hba : x.snd - x.fst ≤ 0 := by omega
      have h1 := Int.natAbs_of_nonneg (show 0 ≤ x.fst - x.snd by omega)
      rw [show (x.snd - x.fst).natAbs = (x.fst - x.snd).natAbs by
        rw [show x.snd - x.fst = -(x.fst - x.snd) by ring, Int.natAbs_neg]]
      have h2 := Int.natAbs_of_nonneg (show 0 ≤ -x.fst by omega)
      rw [show x.fst.natAbs = (-x.fst).natAbs by rw [Int.natAbs_neg]]
      omega
    · left
      dsimp [y]
      rw [mul_assoc, show goldenPhiInv * goldenPhi = 1 by exact golden_inv_mul_phi]
      simp
  · -- negative, positive
    have hord : x.snd ≤ -x.fst := by
      have h := unit_order_pos_neg (a := -x.fst) (b := -x.snd)
        (by omega) (by omega) (by simpa only [neg_sq, neg_mul_neg] using hn)
      omega
    let y := goldenMul x goldenPhi
    refine ⟨y, goldenUnit_mul hx goldenUnit_phi, ?_, ?_⟩
    · dsimp [y]
      change goldenUnitMeasure (goldenMul x goldenPhi) < goldenUnitMeasure x
      rw [golden_mul_phi_coords]
      simp only [goldenUnitMeasure]
      have h1 := Int.natAbs_of_nonneg hb.le
      have h2 := Int.natAbs_of_nonneg (show 0 ≤ -(x.fst + x.snd) by omega)
      rw [show (x.fst + x.snd).natAbs = (-(x.fst + x.snd)).natAbs by
        rw [Int.natAbs_neg]]
      have h3 := Int.natAbs_of_nonneg (show 0 ≤ -x.fst by omega)
      rw [show x.fst.natAbs = (-x.fst).natAbs by rw [Int.natAbs_neg]]
      omega
    · right
      dsimp [y]
      rw [mul_assoc, show goldenPhi * goldenPhiInv = 1 by exact golden_phi_mul_inv]
      simp
  · -- positive, negative
    have hord : -x.snd ≤ x.fst := unit_order_pos_neg ha hb hn
    let y := goldenMul x goldenPhi
    refine ⟨y, goldenUnit_mul hx goldenUnit_phi, ?_, ?_⟩
    · dsimp [y]
      change goldenUnitMeasure (goldenMul x goldenPhi) < goldenUnitMeasure x
      rw [golden_mul_phi_coords]
      simp only [goldenUnitMeasure]
      have h1 := Int.natAbs_of_nonneg (show 0 ≤ -x.snd by omega)
      rw [show x.snd.natAbs = (-x.snd).natAbs by rw [Int.natAbs_neg]]
      have h2 := Int.natAbs_of_nonneg (show 0 ≤ x.fst + x.snd by omega)
      have h3 := Int.natAbs_of_nonneg ha.le
      omega
    · right
      dsimp [y]
      rw [mul_assoc, show goldenPhi * goldenPhiInv = 1 by exact golden_phi_mul_inv]
      simp
  · -- both coordinates are positive
    have hord : x.fst ≤ x.snd := unit_order_pos_pos ha hb hn
    let y := goldenMul x goldenPhiInv
    refine ⟨y, goldenUnit_mul hx goldenUnit_phiInv, ?_, ?_⟩
    · dsimp [y]
      change goldenUnitMeasure (goldenMul x goldenPhiInv) < goldenUnitMeasure x
      rw [golden_mul_phiInv_coords]
      simp only [goldenUnitMeasure]
      have h1 := Int.natAbs_of_nonneg (sub_nonneg.mpr hord)
      have h2 := Int.natAbs_of_nonneg ha.le
      have h3 := Int.natAbs_of_nonneg hb.le
      omega
    · left
      dsimp [y]
      rw [mul_assoc, show goldenPhiInv * goldenPhi = 1 by exact golden_inv_mul_phi]
      simp
```

## Lean の型

```lean
goldenUnit_descent {x : GoldenInt}
    (hx : GoldenUnit x)
    (hlarge : 1 < goldenUnitMeasure x) :
  ∃ y : GoldenInt,
    GoldenUnit y ∧
    goldenUnitMeasure y < goldenUnitMeasure x ∧
    (x = goldenMul y goldenPhi ∨
      x = goldenMul y goldenPhiInv)
```

入力は黄金整数 `x` と、

- `hx : GoldenUnit x` — `x` が unit であること、
- `hlarge : 1 < goldenUnitMeasure x` — `x` が measure 1 の基底 unit ではないこと、

である。

出力は、より小さい unit `y` の存在であり、

$$
\mu(y)<\mu(x),
$$

かつ元の `x` が

$$
x=y\varphi
$$

または

$$
x=y\varphi^{-1}
$$

のどちらか一手で復元できることまで保持する。

ここで

$$
\mu(a+b\varphi)=|a|+|b|
$$

である。

## 数学的主張

黄金整数

$$
x=a+b\varphi
$$

が unit なら、そのノルムは

$$
N(x)=a^2+ab-b^2=\pm1.
$$

さらに $\mu(x)>1$ なら、$a,b$ のどちらも 0 ではない。したがって座標平面の四象限のいずれかにあり、ノルム条件から 0357・0358 の順序補題を使って、次のどちらかを選べる。

$$
y=x\varphi
$$

または

$$
y=x\varphi^{-1}.
$$

この選択は単なる unit の付け替えではなく、座標 measure を厳密に小さくするよう符号ごとに決められる。

座標変換は 0352・0353 により

$$
(a,b)\xmapsto{\cdot\varphi}(b,a+b),
$$

$$
(a,b)\xmapsto{\cdot\varphi^{-1}}(b-a,a)
$$

である。

四象限で適切な変換を選ぶと、変換後の絶対値和が元より必ず小さくなる。これが自然数上の strict descent を与える。

## 証明全体での役割

この定理は `GoldenUnitClassification.lean` の核心である。

後続 `goldenUnitFifthClass_of_unit` は `goldenUnitMeasure x` に対する `Nat.strong_induction_on` を行い、

- measure 1 なら 0356 `goldenUnit_measure_one_cases` で `±1, ±φ` に分類し、
- measure が 1 より大きければ本定理で `y` へ降下し、帰納法を `y` に適用する、

という二段構成を取る。

本定理の出力が単に「小さい unit が存在する」ではなく、

```lean
x = goldenMul y goldenPhi ∨
x = goldenMul y goldenPhiInv
```

という再構成式を含むのが重要である。帰納的に `y` の fifth-power unit class が分かったあと、その class を `φ` または `φ⁻¹` の一手だけ進めて `x` の class へ戻せる。

したがって本定理は、

$$
\text{unit norm }\pm1
\longrightarrow
\text{符号別順序制約}
\longrightarrow
\text{strict coordinate descent}
\longrightarrow
\text{有限 unit class 分類}
$$

を接続する中核 bridge である。

## 直接依存する定義・補題

プロジェクト内で直接・本質的に使うものは次である。

- `GoldenInt` — 黄金整数の座標型。
- `GoldenUnit` — 二側逆元を持つことを表す unit predicate。
- `goldenNorm` —
  $$
  a^2+ab-b^2
  $$
  の黄金ノルム。
- `goldenNorm_eq_one_or_neg_one_of_unit` — unit なら norm が $\pm1$。
- `goldenUnitMeasure` — $|a|+|b|$。
- `unit_order_pos_pos` — 同符号正領域で $a\le b$ を与える 0357。
- `unit_order_pos_neg` — 異符号領域で $-b\le a$ を与える 0358。
- `goldenPhi`, `goldenPhiInv` — 降下に使う unit とその積分逆元。
- `goldenUnit_phi`, `goldenUnit_phiInv` — それらが unit である証明。
- `goldenUnit_mul` — unit の積が unit。
- `golden_mul_phi_coords` — $(a,b)\mapsto(b,a+b)$。
- `golden_mul_phiInv_coords` — $(a,b)\mapsto(b-a,a)$。
- `golden_phi_mul_inv`, `golden_inv_mul_phi` — 両方向の逆元等式。

Mathlib 側では、

- `sq_eq_one_iff`,
- `lt_or_gt_of_ne`,
- `Int.natAbs_of_nonneg`, `Int.natAbs_neg`,
- `omega`, `nlinarith`, `norm_num`, `simp`, `ring`,

が主要な道具である。

## 証明または構築の流れ

### 1. unit の norm を座標二次形式へ展開する

最初に

```lean
have hn : x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2 = 1 ∨
    x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2 = -1 := by
  simpa [goldenNorm] using goldenNorm_eq_one_or_neg_one_of_unit hx
```

として、抽象的な unit 条件を整数座標の二次方程式へ落とす。

### 2. 座標 0 を排除する

`x.fst = 0` と仮定すると norm 条件から

$$
x.snd^2=1
$$

となり、`x.snd = ±1`。すると measure は 1 となって `hlarge` と矛盾する。

同様に `x.snd = 0` なら

$$
x.fst^2=1
$$

となり、やはり measure 1 で矛盾する。

したがって

$$
a\ne0,\qquad b\ne0
$$

が得られる。

この段階により四象限分解が完全になる。

### 3. 四象限へ分ける

```lean
rcases lt_or_gt_of_ne ha0 with ha | ha <;>
  rcases lt_or_gt_of_ne hb0 with hb | hb
```

で、

1. $a<0,b<0$
2. $a<0,b>0$
3. $a>0,b<0$
4. $a>0,b>0$

の四枝を生成する。

### 4. 負・負枝

0357 を $(-a,-b)$ へ適用し、

$$
-a\le-b
$$

を得る。ここでは

$$
y=x\varphi^{-1}
$$

を選ぶ。

座標は

$$
y=(b-a)+a\varphi.
$$

符号と順序制約を使って `natAbs` を外すと、新 measure は元より厳密に小さい。

unit 性は

```lean
goldenUnit_mul hx goldenUnit_phiInv
```

で保持される。

最後に

$$
y\varphi=x\varphi^{-1}\varphi=x
$$

を `golden_inv_mul_phi` で示し、再構成式の左枝

```lean
x = goldenMul y goldenPhi
```

を返す。

### 5. 負・正枝

符号反転して 0358 を適用し、

$$
b\le-a
$$

を得る。

ここでは

$$
y=x\varphi
$$

を選び、

$$
y=b+(a+b)\varphi.
$$

$b>0$ かつ $a+b\le0$ なので

$$
\mu(y)=b-(a+b)=-a.
$$

一方

$$
\mu(x)=-a+b,
$$

で $b>0$ より

$$
\mu(y)<\mu(x).
$$

再構成は

$$
y\varphi^{-1}=x
$$

なので右枝を返す。

### 6. 正・負枝

0358 をそのまま使って

$$
-b\le a
$$

を得る。

再び

$$
y=x\varphi
$$

を選ぶ。今度は $a+b\ge0$ なので

$$
\mu(y)=-b+(a+b)=a,
$$

$$
\mu(x)=a-b.
$$

$b<0$ より strict decrease が得られる。

再構成は同じく `golden_phi_mul_inv` による右枝である。

### 7. 正・正枝

0357 から

$$
a\le b
$$

を得る。

ここでは

$$
y=x\varphi^{-1}
$$

を選び、

$$
y=(b-a)+a\varphi.
$$

両座標が非負なので

$$
\mu(y)=(b-a)+a=b,
$$

元は

$$
\mu(x)=a+b.
$$

$a>0$ より

$$
\mu(y)<\mu(x).
$$

再構成は `golden_inv_mul_phi` により左枝となる。

## Lean 固有の処理

### `sq_eq_one_iff`

座標が 0 の場合、norm 条件から得た `x.snd ^ 2 = 1` または `x.fst ^ 2 = 1` を、整数の具体的な二択 `= 1 ∨ = -1` へ変換する。

これにより `simp [goldenUnitMeasure, ...] at hlarge` で measure 1 と `hlarge` の矛盾を直接閉じられる。

### `lt_or_gt_of_ne`

座標非零を、線形順序上の「負または正」へ変換する。二座標へ連続適用することで、四象限を機械的に漏れなく列挙している。

### `Int.natAbs_of_nonneg` と `Int.natAbs_neg`

`goldenUnitMeasure` は自然数値なので、整数不等式を直接 `omega` に渡すだけでは絶対値を扱いにくい。各枝で符号を確定したあと、`natAbs` を非負整数表現へ書き換えてから `omega` に strict inequality を解かせている。

### `let y := ...` と `dsimp [y]`

各枝で降下先を具体的に固定し、存在量 `y` の witness としてそのまま返す。`dsimp [y]` で witness の定義を展開したあと、0352 / 0353 の座標公式へ書き換える。

### 再構成式での `mul_assoc`

`y=xφ^{-1}` または `y=xφ` から元の `x` を復元するには、積を結合し直して

$$
\varphi^{-1}\varphi=1,
\qquad
\varphi\varphi^{-1}=1
$$

を使う必要がある。そのため `mul_assoc` と 0349・0350 の逆元定理が明示的に使われる。

## 冗長・重複箇所

四象限の各枝は、

1. 順序補題を得る、
2. `y := x * φ` または `x * φInv` を置く、
3. `goldenUnit_mul` で unit 性を示す、
4. 座標公式で measure を展開する、
5. `natAbs` を符号に従って消す、
6. `omega` で strict decrease、
7. 逆元等式で再構成、

というほぼ同じ骨格を持つ。

特に負・正枝と正・負枝は `φ` を使う点で非常に近く、負・負枝と正・正枝は `φInv` を使う点で対応している。

一方、この明示的な四象限分解は「どの符号領域でどちらの unit を掛けるか」をコード上で直接読める利点が大きい。単純な短縮だけを目的に共通化すると、数学的な降下幾何が見えにくくなる可能性がある。

## 最適化候補

1. 四象限ごとの measure 計算を、符号付き `natAbs` 補題として切り出し、`goldenUnit_descent` 本体を短くする余地がある。
2. 正負反転対称性を使い、負・負 / 正・正、負・正 / 正・負をそれぞれ共通補題化できる可能性がある。
3. 0357・0358 と本定理の符号処理を一体化した「norm $\pm1$ unit に対する contraction direction」の補題を作れば、四象限の局所推論を隠蔽できる。
4. `natAbs` の多数の書き換えを、`abs` や符号付き線形 measure の中間補題で整理できる可能性がある。
5. 再構成の二枝は `golden_phi_mul_inv` / `golden_inv_mul_phi` を使う共通 cancellation 補題へまとめられる可能性がある。

ただし、これらは設計上の候補であり、今回 Lean ビルドを行っていないため、置換後の証明がそのまま成立するかは未確認である。

## 必要 Mathlib import と import 最適化候補

生成 standalone `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本定理が Mathlib から実際に利用する主要機能は、

- 整数 `ℤ` と線形順序、
- `Int.natAbs`, `Int.natAbs_of_nonneg`, `Int.natAbs_neg`,
- `sq_eq_one_iff`, `sq_nonneg`,
- `lt_or_gt_of_ne`,
- `omega`,
- `nlinarith`,
- `norm_num`,
- `simp`,
- `ring`,

である。

したがって宣言単体の Comparator 用最小環境では `Mathlib` 全体よりかなり狭い import に縮小できる可能性がある。少なくとも tactic 側では `Mathlib.Tactic.Omega`, `Mathlib.Tactic.Nlinarith`, `Mathlib.Tactic.Ring`, `Mathlib.Tactic.NormNum` 相当が候補になる。

ただし `GoldenInt`、unit API、`natAbs` 補題などの依存を含めた **厳密な最小 import 集合は未確認** である。

## Comparator challenge 化の可否

 **可能。難度は中級〜上級。**

本定理は単独の整数算術だけではなく、前段で構築された黄金整数 API を横断して使うため、0357・0358 より challenge として一段重い。

challenge 化するなら、少なくとも

- `GoldenInt`,
- `GoldenUnit`,
- `goldenNorm`,
- `goldenUnitMeasure`,
- `goldenPhi`, `goldenPhiInv`,
- 0352・0353 の座標公式、
- 0349・0350 の逆元公式、
- `goldenUnit_mul`, `goldenUnit_phi`, `goldenUnit_phiInv`,
- 0357・0358 の順序補題、

を前提として与え、

```lean
theorem goldenUnit_descent {x : GoldenInt} (hx : GoldenUnit x)
    (hlarge : 1 < goldenUnitMeasure x) :
    ∃ y : GoldenInt,
      GoldenUnit y ∧
      goldenUnitMeasure y < goldenUnitMeasure x ∧
      (x = goldenMul y goldenPhi ∨
        x = goldenMul y goldenPhiInv) := by
  ?_
```

を完成させる形がよい。

評価点は、

1. norm $\pm1$ から座標 0 を排除できるか、
2. 四象限を漏れなく分けられるか、
3. 各象限で `φ` / `φInv` の正しい方向を選べるか、
4. 0357・0358 を正しい符号変換で適用できるか、
5. `natAbs` を正しく消して strict decrease を示せるか、
6. inverse law で再構成式まで戻せるか、

である。

単なる tactic 探索ではなく、unit descent の数学的構造理解を測れる良い Comparator challenge になる。

## 次に読むべき宣言

次は 0360 `GoldenUnitFifthClass` である。宣言種別は **`def`**。

```lean
/-- Existence of `i < 5` and `delta` with `x = phi^i * delta^5`. -/
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

0359 までで「任意の非基底 unit は measure を一段下げられる」ことが確立した。0360 では、その降下を最終的に何へ分類するかを表す target predicate を定義する。

数学的には、任意の unit を fifth power を法として

$$
x=\varphi^i\delta^5,
\qquad 0\le i<5
$$

という 5 つの代表 class のいずれかへ送るための命題である。