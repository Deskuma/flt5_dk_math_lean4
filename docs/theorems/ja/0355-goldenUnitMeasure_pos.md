# 0355 — `goldenUnitMeasure_pos`

## 宣言種別

この宣言は **`theorem`** である。

```lean
theorem goldenUnitMeasure_pos {x : GoldenInt} (hx : GoldenUnit x) :
    0 < goldenUnitMeasure x := by
  have hn := goldenNorm_eq_one_or_neg_one_of_unit hx
  simp only [goldenUnitMeasure]
  by_contra h
  have hz : x.fst.natAbs + x.snd.natAbs = 0 := Nat.eq_zero_of_not_pos h
  have haf : x.fst.natAbs = 0 := by omega
  have hbf : x.snd.natAbs = 0 := by omega
  have ha : x.fst = 0 := Int.natAbs_eq_zero.mp haf
  have hb : x.snd = 0 := Int.natAbs_eq_zero.mp hbf
  rcases hn with hn | hn <;> simp [goldenNorm, ha, hb] at hn
```

## Lean の型

```lean
goldenUnitMeasure_pos {x : GoldenInt} (hx : GoldenUnit x) :
  0 < goldenUnitMeasure x
```

任意の黄金整数 `x` が unit であるという証明 `hx : GoldenUnit x` を受け取り、その座標 measure

$$
\mu(x)=|x.\mathrm{fst}|+|x.\mathrm{snd}|
$$

が正であることを返す。

## 数学的主張

`GoldenInt` を

$$
x=a+b\varphi
$$

と書くと、0354 で

$$
\mu(x)=|a|+|b|
$$

と定義した。本定理は、`x` が unit なら

$$
0<|a|+|b|
$$

であることを示す。

本質は単純である。もし

$$
|a|+|b|=0
$$

なら、自然数の非負性から

$$
a=0,\qquad b=0
$$

となり、`x` は零元である。しかし黄金整数の unit はノルムが $1$ または $-1$ でなければならず、零元のノルムは $0$ なので矛盾する。

したがって unit は座標原点に存在せず、自然数値 measure は必ず 1 以上になる。

## 証明全体での役割

この定理は `GoldenUnitClassification` における自然数降下の **下端保証** である。

後続の unit 分類では `goldenUnitMeasure x = n` と置き、`Nat.strong_induction_on` により $n$ 上で降下する。その際、unit に対して $n=0$ が起こらないことが必要であり、本定理が

$$
1\le \mu(x)
$$

を与える。

証明の流れは次のようになる。

```text
GoldenUnit x
    ↓
goldenNorm x = ±1
    ↓
x ≠ 0
    ↓
goldenUnitMeasure x ≠ 0
    ↓
0 < goldenUnitMeasure x
    ↓
measure = 1 を基底ケースにできる
    ↓
measure > 1 なら goldenUnit_descent で厳密減少
```

したがって、0354 が降下量そのものを定義したのに対し、0355 はその降下量の最小値を unit 上で制御する。

## 直接依存する定義・補題

主要な直接依存は次の通りである。

- `GoldenUnit` — `x` が黄金整数環の unit であることを表す述語。
- `goldenUnitMeasure` — 0354。`x.fst.natAbs + x.snd.natAbs`。
- `goldenNorm_eq_one_or_neg_one_of_unit` — unit の黄金ノルムが $1$ または $-1$ であることを与える。
- `goldenNorm` — 黄金整数の二次ノルム。
- `Nat.eq_zero_of_not_pos` — 自然数が正でないなら 0 であることを得る。
- `Int.natAbs_eq_zero` — `natAbs a = 0` と `a = 0` を結ぶ。
- `omega` — 自然数和が 0 なら各項も 0 であることを処理する。
- `simp` — 座標が 0 のとき `goldenNorm` が $0$ になることを計算し、$0=\pm1$ の矛盾を閉じる。

0352 `golden_mul_phi_coords` と 0353 `golden_mul_phiInv_coords` は本定理の直接依存ではない。それらは後続の strict descent で `goldenUnitMeasure` の減少を示すために使われる。

## 証明の流れ

### 1. unit のノルムを取り出す

```lean
have hn := goldenNorm_eq_one_or_neg_one_of_unit hx
```

ここで

```lean
hn : goldenNorm x = 1 ∨ goldenNorm x = -1
```

に相当する情報を得る。

### 2. measure を展開する

```lean
simp only [goldenUnitMeasure]
```

目標は

```lean
0 < x.fst.natAbs + x.snd.natAbs
```

になる。

### 3. 正でないと仮定する

```lean
by_contra h
```

自然数なので、正でないことから和が 0 だと分かる。

```lean
have hz : x.fst.natAbs + x.snd.natAbs = 0 :=
  Nat.eq_zero_of_not_pos h
```

### 4. 各座標の `natAbs` が 0 と示す

```lean
have haf : x.fst.natAbs = 0 := by omega
have hbf : x.snd.natAbs = 0 := by omega
```

自然数 $A,B$ について $A+B=0$ なら $A=B=0$ という部分を `omega` が処理する。

### 5. 整数座標そのものを 0 に戻す

```lean
have ha : x.fst = 0 := Int.natAbs_eq_zero.mp haf
have hb : x.snd = 0 := Int.natAbs_eq_zero.mp hbf
```

これで `x` が座標原点であることが分かる。

### 6. unit norm と矛盾させる

```lean
rcases hn with hn | hn <;> simp [goldenNorm, ha, hb] at hn
```

`goldenNorm ⟨0,0⟩ = 0` を計算し、二つの分岐

$$
0=1,
\qquad
0=-1
$$

をともに `simp` が排除する。

## Lean 固有の処理

### `by_contra` と自然数順序

紙上では「measure が 0 なら」と始めてもよいが、Lean の目標は `0 < ...` なので、コードは `by_contra h` で `¬ 0 < ...` を得た後、`Nat.eq_zero_of_not_pos` によって明示的に 0 へ変換している。

### `natAbs` から整数へ戻す

`goldenUnitMeasure` の値域を `ℕ` にしたため、降下には都合がよい一方、最終的に `goldenNorm` を計算するには整数座標へ戻す必要がある。そこで

```lean
Int.natAbs_eq_zero.mp
```

を使って

```text
natAbs coordinate = 0
        ↓
integer coordinate = 0
```

と橋渡しする。

### `omega` の役割

ここで `omega` が解いているのは黄金整数の代数ではない。単に

```lean
A + B = 0
```

という Presburger arithmetic 上の自然数問題から `A = 0` と `B = 0` を取り出している。

### 最後の `<;>`

```lean
rcases hn with hn | hn <;> simp [goldenNorm, ha, hb] at hn
```

は $+1$ と $-1$ の二分岐へ同じ `simp` を適用する Lean 的な圧縮である。

## 冗長・重複箇所

証明は短く、実質的な冗長性は少ない。ただし次の二点は整理候補になり得る。

1. `haf` と `hbf` はともに `hz` から `omega` で取り出しているため、和が 0 のときの一般補題や既存の `Nat.add_eq_zero_iff` 系 API が適合すれば一度の分解にまとめられる可能性がある。
2. unit から `x ≠ 0` を直接得る一般 API が既にあるなら、`goldenNorm_eq_one_or_neg_one_of_unit` を経由せず「unit は zero ではない」から measure positivity を示す別経路も考えられる。

ただし 2 は現行証明より必ず短いとは限らない。現在の証明は後段でも重要な `goldenNorm_eq_one_or_neg_one_of_unit` を使っており、黄金整数の局所理論として意味が明確である。

## 最適化候補

局所的には次の候補がある。

- `x.fst.natAbs + x.snd.natAbs = 0` の分解を、利用可能なら標準の加法ゼロ補題で置き換えて `omega` 呼び出しを減らす。
- `goldenUnitMeasure x = 0 ↔ x = 0` の一般補題を先に作る。すると本定理は「unit は 0 でない」との合成になる。
- 後続でも measure の非零性が何度も必要なら、`goldenUnitMeasure_ne_zero` を補助定理として切り出す。

一方、現在の証明は一度しか必要としない局所事実を過剰に抽象化していないという利点がある。したがって、ライブラリ全体で再利用が確認できない限り、現状のままでも十分に合理的である。

## 必要 Mathlib import と import 最適化候補

生成 standalone `Flt5DkMath/FLT5StandAlone.lean` は全体として

```lean
import Mathlib
```

を使用している。

本定理で外部的に必要となる機能は少なくとも、

- `Int.natAbs` と `Int.natAbs_eq_zero`
- 自然数の順序・加法
- `omega`
- `simp`

である。

さらに実モジュールとしては、プロジェクト側の `GoldenInt`、`GoldenUnit`、`goldenNorm`、`goldenNorm_eq_one_or_neg_one_of_unit`、`goldenUnitMeasure` を提供する前段モジュールが必要になる。

`import Mathlib` は本宣言単独には広すぎる可能性が高い。ただし今回は Lean ビルドを行わないため、具体的な最小 Mathlib module 名の集合までは確認しない。`Mathlib` を細分化する場合は `omega` と整数絶対値 API を含む import を実ビルドで検証する必要がある。

## Comparator challenge 化の可否

**可能。難度は初級から中級。**

良い challenge 形は、定義と unit norm theorem を与え、次の穴を埋めさせるものである。

```lean
theorem goldenUnitMeasure_pos {x : GoldenInt} (hx : GoldenUnit x) :
    0 < goldenUnitMeasure x := by
  ?_
```

必要な発想は、

1. unit なら norm が $\pm1$、
2. measure が正でないなら自然数なので 0、
3. 絶対値和が 0 なら両座標が 0、
4. 零座標の norm は 0、
5. $0\neq\pm1$、

という非常に明確な contradiction chain である。

Comparator では `omega` を使わせる版と、標準の加法ゼロ補題のみで証明させる版を分けると、算術 tactic 依存とライブラリ探索能力を比較できる。

## 次に読むべき宣言

次は **0356 `goldenUnit_measure_one_cases`**。種別は **`theorem`** である。

```lean
theorem goldenUnit_measure_one_cases {x : GoldenInt} (_hx : GoldenUnit x)
    (hm : goldenUnitMeasure x = 1) :
    x = goldenOne ∨ x = -goldenOne ∨
      x = goldenPhi ∨ x = -goldenPhi := by
  ...
```

0355 が unit の measure は 0 にならないことを示したので、次は最小値

$$
\mu(x)=1
$$

を完全分類する。整数二座標の絶対値和が 1 なら

$$
(|a|,|b|)=(1,0)\quad\text{または}\quad(0,1)
$$

しかなく、符号を戻すことで

$$
x\in\{1,-1,\varphi,-\varphi\}
$$

を得る。これが後続の strong induction における具体的な基底ケースとなる。