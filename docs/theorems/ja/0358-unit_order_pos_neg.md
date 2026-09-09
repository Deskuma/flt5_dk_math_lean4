# 0358 — `unit_order_pos_neg`

## 宣言種別

この宣言は **`private theorem`** である。

`GoldenUnitClassification.lean` 内部の補助定理であり、公開 API ではない。前項 0357 `unit_order_pos_pos` と対になる符号別の局所順序補題である。

```lean
private theorem unit_order_pos_neg {a b : ℤ}
    (ha : 0 < a) (hb : b < 0)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) : -b ≤ a := by
  by_contra h
  have hab : a + 1 ≤ -b := by omega
  rcases hn with hn | hn <;> nlinarith [sq_nonneg (a + b)]
```

## Lean の型

```lean
unit_order_pos_neg {a b : ℤ}
    (ha : 0 < a)
    (hb : b < 0)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) :
  -b ≤ a
```

正の整数 `a` と負の整数 `b` が黄金整数のノルムに現れる二次形式

$$
a^2+ab-b^2
$$

について値 $1$ または $-1$ を取るなら、負座標の絶対値は正座標を越えず、

$$
-b\le a
$$

となることを示す。

`b < 0` なので $-b=|b|$ であり、数学的には

$$
|b|\le a
$$

という符号付き座標の大小制約である。

## 数学的主張

黄金整数

$$
x=a+b\varphi
$$

に対応するノルム二次形式を

$$
Q(a,b)=a^2+ab-b^2
$$

と書く。この補題は

$$
a>0,\qquad b<0,\qquad Q(a,b)=\pm1
$$

から

$$
-b\le a
$$

を導く。

結論を否定すると

$$
a<-b.
$$

`a,b` は整数なので、これは一段強い

$$
a+1\le -b
$$

へ変換できる。この離散的な 1 ステップの余裕と $Q(a,b)=\pm1$ を合わせると矛盾する。

証明中で補助的に使われる平方非負性は

$$
(a+b)^2\ge0
$$

である。正・負領域では `a + b` が両座標の絶対値差を直接表すため、前項 0357 の `(a-b)^2` ではなく `(a+b)^2` が自然な補助量となる。

## 証明全体での役割

この定理は `goldenUnit_descent` の **異符号座標の二枝を成立させる順序制約** である。

後続の `goldenUnit_descent` は、unit `x` の座標の符号を四象限に分ける。そのうち

- `x.fst < 0 < x.snd` の枝では、符号を反転して本補題を適用する。
- `0 < x.fst` かつ `x.snd < 0` の枝では、本補題をそのまま適用する。

正本では後者で

```lean
have hord : -x.snd ≤ x.fst := unit_order_pos_neg ha hb hn
let y := goldenMul x goldenPhi
```

と使われる。

0352 `golden_mul_phi_coords` により

$$
(a,b)\xmapsto{\cdot\varphi}(b,a+b)
$$

である。ここで $a>0>b$ かつ $-b\le a$ なので

$$
a+b\ge0.
$$

したがって新しい measure は

$$
\mu((a+b\varphi)\varphi)
  =|b|+|a+b|
  =-b+(a+b)
  =a.
$$

元の measure は

$$
\mu(a+b\varphi)=a+(-b).
$$

$b<0$ なので $-b>0$、ゆえに

$$
a<a-b.
$$

これで measure が厳密に減少する。

つまり本補題は、黄金ノルムが $\pm1$ という代数的条件を、`goldenUnitMeasure` の自然数 strict descent に必要な符号付き大小関係へ変換する橋である。

## 直接依存する定義・補題

この `private theorem` は `GoldenInt` や `GoldenUnit` を型に含まず、整数算術だけへ局所化されている。

直接使うものは次である。

- `ℤ` — `a`, `b` の型。
- 整数順序と符号反転。
- `omega` — `¬ (-b ≤ a)` から整数の離散性を使って
  $$
  a+1\le -b
  $$
  を得る。
- `sq_nonneg (a + b)` —
  $$
  0\le(a+b)^2
  $$
  を供給する。
- `nlinarith` — ノルム $+1$ / $-1$ の各ケースと符号・順序条件を組み合わせて矛盾を閉じる。
- `rcases` — `hn` の二分岐を展開する。

概念上は、後続 `goldenUnit_descent` において `goldenNorm_eq_one_or_neg_one_of_unit hx` が `hn` の供給源となるが、本補題自身はそのプロジェクト固有 API に依存しない。

## 証明の流れ

### 1. 結論を否定する

```lean
by_contra h
```

目標 `-b ≤ a` を否定する。

### 2. 整数の離散順序を取り出す

```lean
have hab : a + 1 ≤ -b := by omega
```

整数では

$$
-b>a
$$

なら必ず

$$
a+1\le-b
$$

である。`omega` がこの格子 1 ステップを処理する。

### 3. ノルムの符号を二分する

```lean
rcases hn with hn | hn
```

これにより

$$
Q(a,b)=1
$$

または

$$
Q(a,b)=-1
$$

を個別に扱う。

### 4. 非線形算術で両方を排除する

```lean
nlinarith [sq_nonneg (a + b)]
```

`ha`, `hb`, `hab`, 各枝の `hn` と

$$
(a+b)^2\ge0
$$

を `nlinarith` に渡し、どちらのノルム値も仮定した順序と両立しないことを示す。

`<;>` により同じ処理が `hn` の両分岐に適用される。

## Lean 固有の処理

### `private theorem`

数学的には独立した整数二次形式の補題だが、現在の設計では `GoldenUnitClassification` の内部実装に限定されている。公開名前空間を増やさず、descent に必要な局所算術だけを切り出した形である。

### `omega` と `nlinarith` の分業

`omega` は整数の線形・離散順序、`nlinarith` は二次多項式関係を担当する。

特に

```lean
have hab : a + 1 ≤ -b := by omega
```

は、単なる実数不等式 `a < -b` より強い整数格子情報を抽出している。この 1 の差が $Q(a,b)=\pm1$ と衝突するため、証明上重要である。

### `sq_nonneg (a + b)`

異符号の場合、`a+b` は実質的に $a-|b|$ である。その平方の非負性を明示的に `nlinarith` へ与えることで、二次形式との比較を自動化している。

## 冗長・重複箇所

0357 `unit_order_pos_pos` と証明骨格はほぼ同型である。

0357 は

```lean
have hab : b + 1 ≤ a := by omega
rcases hn with hn | hn <;> nlinarith [sq_nonneg (a - b)]
```

0358 は

```lean
have hab : a + 1 ≤ -b := by omega
rcases hn with hn | hn <;> nlinarith [sq_nonneg (a + b)]
```

であり、違いは符号領域に対応する順序目標と平方補助量である。

この重複は一般化できる可能性がある一方、descent の四象限解析と直接対応するため、現在の二つの短い補題は読みやすい。

## 最適化候補

1. `unit_order_pos_pos` と `unit_order_pos_neg` を、符号変換後の共通二次形式補題へ統合できるか検討する。
2. 本補題は `GoldenInt` 非依存なので、他の黄金整数モジュールでも同じ順序事実を使うなら `private` を外して再利用 API にする余地がある。
3. `nlinarith` に渡す補助量を明示的な因数分解や下界補題へ置き換え、tactic 依存を減らすことも考えられる。
4. `goldenUnit_descent` 側の正負・負正の二枝も符号反転対称性をまとめられる可能性がある。

ただし、これらの置換が Lean 上でそのまま成立するかは今回ビルドしていないため未確認である。

## 必要 Mathlib import と import 最適化候補

生成 standalone `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本補題単独で中心となる機能は、

- 整数 `ℤ` とその線形順序、
- `omega`,
- `nlinarith`,
- `sq_nonneg`,

である。

したがって宣言単体では `import Mathlib` は広すぎる可能性が高く、`Mathlib.Tactic.Omega`、`Mathlib.Tactic.Nlinarith` と整数・順序・環の基礎 import へ縮小できる可能性がある。

ただし Lean ビルドを行っていないため、 **厳密な最小 import 集合は未確認** である。

## Comparator challenge 化の可否

 **可能。難度は初級〜中級。**

プロジェクト固有定義をすべて外したまま、次の小さな整数算術問題として独立できる。

```lean
private theorem unit_order_pos_neg {a b : ℤ}
    (ha : 0 < a) (hb : b < 0)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) : -b ≤ a := by
  ?_
```

Comparator では、

1. 否定から `a + 1 ≤ -b` を取り出せるか、
2. $+1/-1$ の disjunction を正しく分けられるか、
3. 必要な平方非負性として `(a+b)^2 ≥ 0` を発見できるか、
4. `omega` と `nlinarith` の適切な役割分担ができるか、

を測れる。

0357 と組にして「符号領域に応じて補助平方 `(a-b)^2` / `(a+b)^2` を選べるか」を問う challenge にすると、単独問題より構造理解を強く評価できる。

## 次に読むべき宣言

次は 0359 `goldenUnit_descent` である。宣言種別は **`theorem`**。

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
  ...
```

0357 と 0358 までで符号別順序補題が揃い、0359 ではそれらを四象限すべてへ適用して、`goldenPhi` または `goldenPhiInv` を一回掛けることで `goldenUnitMeasure` を厳密に減少させる本体の descent が構成される。