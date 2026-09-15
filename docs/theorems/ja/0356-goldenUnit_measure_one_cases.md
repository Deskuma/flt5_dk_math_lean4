# 0356 — `goldenUnit_measure_one_cases`

## 宣言種別

この宣言は **`theorem`** である。

```lean
theorem goldenUnit_measure_one_cases {x : GoldenInt} (_hx : GoldenUnit x)
    (hm : goldenUnitMeasure x = 1) :
    x = goldenOne ∨ x = -goldenOne ∨
      x = goldenPhi ∨ x = -goldenPhi := by
  have hsum : x.fst.natAbs + x.snd.natAbs = 1 := hm
  have hcases :
      (x.fst.natAbs = 0 ∧ x.snd.natAbs = 1) ∨
      (x.fst.natAbs = 1 ∧ x.snd.natAbs = 0) := by omega
  rcases hcases with h | h
  · have ha0 : x.fst = 0 := Int.natAbs_eq_zero.mp h.1
    have hb : x.snd = 1 ∨ x.snd = -1 := by
      simpa using (Int.natAbs_eq_iff.mp h.2)
    rcases hb with hb | hb
    · right; right; left; ext <;> simp [goldenPhi, ha0, hb]
    · right; right; right; ext <;> simp [goldenPhi, ha0, hb]
  · have ha : x.fst = 1 ∨ x.fst = -1 := by
      simpa using (Int.natAbs_eq_iff.mp h.1)
    have hb0 : x.snd = 0 := Int.natAbs_eq_zero.mp h.2
    rcases ha with ha | ha
    · left; ext <;> simp [goldenOne, ha, hb0]
    · right; left; ext <;> simp [goldenOne, ha, hb0]
```

## Lean の型

```lean
goldenUnit_measure_one_cases {x : GoldenInt} (_hx : GoldenUnit x)
    (hm : goldenUnitMeasure x = 1) :
  x = goldenOne ∨ x = -goldenOne ∨
    x = goldenPhi ∨ x = -goldenPhi
```

任意の黄金整数 `x` について、`x` が unit であり、かつ座標 measure が 1 なら、`x` は `goldenOne`、`-goldenOne`、`goldenPhi`、`-goldenPhi` のいずれかであることを返す。

ただし重要な Lean 上の事実として、仮定 `_hx : GoldenUnit x` は証明本体では使用されていない。実際の分類は `hm : goldenUnitMeasure x = 1` だけから従う。

## 数学的主張

`GoldenInt` を

$$
x=a+b\varphi
$$

とし、0354 の measure

$$
\mu(x)=|a|+|b|
$$

を用いる。仮定

$$
\mu(x)=1
$$

から、非負整数の和が 1 なので

$$
(|a|,|b|)=(1,0)
\quad\text{または}\quad
(|a|,|b|)=(0,1)
$$

しかない。

前者なら

$$
a=\pm1,\qquad b=0,
$$

したがって

$$
x=\pm1.
$$

後者なら

$$
a=0,\qquad b=\pm1,
$$

したがって

$$
x=\pm\varphi.
$$

よって

$$
x\in\{1,-1,\varphi,-\varphi\}.
$$

これは黄金整数の unit 分類に固有の深い数論を使う主張ではなく、座標の $\ell^1$ measure が 1 である整数格子点の完全分類である。

## 証明全体での役割

この定理は `GoldenUnitClassification` の自然数 strong induction における **基底ケース分類** を担う。

0355 `goldenUnitMeasure_pos` が unit に対して

$$
0<\mu(x)
$$

を示したため、最小可能値は 1 である。本定理はその最小値に達したとき、候補が四つしかないことを確定する。

後続 `goldenUnitFifthClass_of_unit` では、`goldenUnitMeasure x = n` と置いて strong induction を行い、`n=1` の場合に本定理を直接呼び出す。その四分岐は、それぞれ

```text
1       → goldenUnitFifthClass_one
-1      → goldenUnitFifthClass_neg_one
phi     → goldenUnitFifthClass_phi
-phi    → goldenUnitFifthClass_neg_phi
```

へ接続される。

したがって流れは

```text
unit x
  ↓
0 < μ(x)                    -- 0355
  ↓
μ(x) = 1 なら四つの基底点 -- 0356
  ↓
μ(x) > 1 なら strict descent
  ↓
より小さい unit へ
  ↓
strong induction
```

となる。

## 直接依存する定義・補題

主要な直接依存は次の通りである。

- `GoldenInt` — 整数二座標で黄金整数を表す構造。
- `GoldenUnit` — 定理の仮定に現れる。ただし証明本体では `_hx` として未使用。
- `goldenUnitMeasure` — 0354。`x.fst.natAbs + x.snd.natAbs`。
- `goldenOne` — 座標 `⟨1, 0⟩` の黄金整数。
- `goldenPhi` — 座標 `⟨0, 1⟩` の黄金整数。
- `Int.natAbs_eq_zero` — `natAbs a = 0` から `a = 0` を得る。
- `Int.natAbs_eq_iff` — `natAbs a = 1` から `a = 1 ∨ a = -1` を得るために使う。
- `omega` — 非負整数二項の和が 1 である場合を二ケースへ分類する。
- `ext` — `GoldenInt` の等式を座標等式へ分解する。
- `simp` — `goldenOne`、`goldenPhi`、符号と座標値を展開して各等式を閉じる。

0355 `goldenUnitMeasure_pos` は論理的な前段として重要だが、本定理の直接依存ではない。本定理自身は `hm` だけから成立する。

## 証明の流れ

### 1. measure の等式を座標和として取り出す

```lean
have hsum : x.fst.natAbs + x.snd.natAbs = 1 := hm
```

`goldenUnitMeasure` は reducible な定義としてここでは Lean が型整合上展開できており、`hm` をそのまま `hsum` に使っている。

### 2. 絶対値の組を二ケースへ分類する

```lean
have hcases :
    (x.fst.natAbs = 0 ∧ x.snd.natAbs = 1) ∨
    (x.fst.natAbs = 1 ∧ x.snd.natAbs = 0) := by omega
```

ここが離散格子としての核心である。自然数 $A,B$ に対する

$$
A+B=1
$$

の解は

$$
(A,B)=(0,1),(1,0)
$$

しかない。

### 3. 第一座標が 0 の場合

```lean
have ha0 : x.fst = 0 := Int.natAbs_eq_zero.mp h.1
```

さらに `x.snd.natAbs = 1` から

```lean
have hb : x.snd = 1 ∨ x.snd = -1 := by
  simpa using (Int.natAbs_eq_iff.mp h.2)
```

を得る。二分岐を `ext` と `simp` で座標等式へ落とし、`goldenPhi` または `-goldenPhi` を得る。

### 4. 第二座標が 0 の場合

同様に

```lean
have ha : x.fst = 1 ∨ x.fst = -1 := by
  simpa using (Int.natAbs_eq_iff.mp h.1)
have hb0 : x.snd = 0 := Int.natAbs_eq_zero.mp h.2
```

として、`goldenOne` または `-goldenOne` を得る。

## Lean 固有の処理

### 未使用仮定 `_hx`

```lean
(_hx : GoldenUnit x)
```

という名前の先頭の `_` は、意図的に未使用であることを示している。Lean はこの仮定なしでも証明本体を受理できる構造になっている。

このため数学的により強い補題

```lean
goldenUnitMeasure x = 1 →
  x = goldenOne ∨ x = -goldenOne ∨
    x = goldenPhi ∨ x = -goldenPhi
```

が実際には成立している。

### `omega` の役割

`omega` は黄金整数のノルムや unit 性を処理しているのではない。単に自然数

```lean
A + B = 1
```

から二つの可能性を完全列挙している。

### `Int.natAbs_eq_iff`

絶対値 1 の整数を符号付きの二候補へ戻す箇所で、自然数 measure から整数座標へ情報を復元している。

### `ext <;> simp`

`GoldenInt` の equality を `.fst` と `.snd` に分解し、具体座標を計算する。四ケースはいずれも閉じた座標等式であるため、最後に数論的 reasoning は不要である。

## 冗長・重複箇所

最も明確な冗長性は `_hx : GoldenUnit x` が完全に未使用である点である。

この仮定は API 上、「unit の measure 1 基底ケース」という用途を明示するために残されている可能性がある。しかし論理的には不要であり、より一般的な格子補題として切り出せる。

また、二つの大分岐は

```text
natAbs coordinate = 0
natAbs other coordinate = 1
```

を整数座標へ戻して `ext <;> simp` するという同型の構造を持つため、補助補題を作れば圧縮可能である。ただし現在の証明は四候補を視覚的に明示しており、分類定理としては読みやすい。

## 最適化候補

候補は三つある。

1. `_hx` を除いた一般補題、たとえば `goldenUnitMeasure_eq_one_cases` を先に証明し、本定理をその薄い wrapper にする。
2. `hsum` は `hm` と実質同一なので、`omega` が定義展開を適切に扱えるなら直接 `hm` から `hcases` を作る。ただし現状の一行は意味を明確にするため残す価値がある。
3. `natAbs = 1` からの符号分岐を一般的な座標分類補助補題へ抽出する。ただし再利用がなければ過剰抽象化になる。

API 設計としては 1 が最も有力である。unit 固有の主張と、単なる整数格子の事実を分離できるためである。

## 必要 Mathlib import と import 最適化候補

生成 standalone `Flt5DkMath/FLT5StandAlone.lean` は全体として

```lean
import Mathlib
```

を使用している。

本定理が外部的に使う主な機能は、

- `Int.natAbs`
- `Int.natAbs_eq_zero`
- `Int.natAbs_eq_iff`
- `omega`
- structure extensionality
- `simp`

である。

プロジェクト側では `GoldenInt`、`GoldenUnit`、`goldenUnitMeasure`、`goldenOne`、`goldenPhi` の定義を提供する前段モジュールが必要である。

`import Mathlib` はこの宣言単独には広すぎる可能性が高い。ただし今回は Lean ビルドを行わないため、最小 Mathlib import の正確な集合は未確認である。特に `Int.natAbs_eq_iff` と `omega` を同時に提供する最小構成は実ビルドで検証すべきである。

## Comparator challenge 化の可否

**可能。難度は初級。**

特に良い micro challenge である。必要な発想はほぼ完全に局所的で、FLT5 の大域的背景を必要としない。

```lean
theorem goldenUnit_measure_one_cases {x : GoldenInt} (_hx : GoldenUnit x)
    (hm : goldenUnitMeasure x = 1) :
    x = goldenOne ∨ x = -goldenOne ∨
      x = goldenPhi ∨ x = -goldenPhi := by
  ?_
```

評価点は、

1. `_hx` が不要だと見抜けるか、
2. `A+B=1` を `omega` などで二ケースへ落とせるか、
3. `natAbs = 1` を `±1` に戻せるか、
4. structure equality を `ext` で閉じられるか、

である。

さらに難度を上げるなら `omega` を禁止して `Nat.add_eq_one` 系の標準補題探索を要求する版も作れる。

## 次に読むべき宣言

次は **0357 `unit_order_pos_pos`**。種別は **`private theorem`** である。

```lean
private theorem unit_order_pos_pos {a b : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) : a ≤ b := by
  by_contra h
  have hab : b + 1 ≤ a := by omega
  rcases hn with hn | hn <;> nlinarith [sq_nonneg (a - b)]
```

0356 までで measure 1 の基底ケースが閉じた。0357 からは measure が 1 より大きい unit を実際に縮めるため、黄金ノルム

$$
a^2+ab-b^2=\pm1
$$

と座標の符号から大小関係を導く局所補題群へ入る。`unit_order_pos_pos` は $a>0,b>0$ の象限で

$$
a\le b
$$

を強制し、後続 `goldenUnit_descent` で $arphi^{-1}$ を掛けた座標差 $b-a$ を非負に保ちながら measure を減少させるための準備となる。