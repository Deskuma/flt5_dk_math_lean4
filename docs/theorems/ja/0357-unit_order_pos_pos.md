# 0357 — `unit_order_pos_pos`

## 宣言種別

この宣言は **`private theorem`** である。

`private` なので `GoldenUnitClassification.lean` の内部補助定理であり、モジュール外へ公開する API ではない。

```lean
private theorem unit_order_pos_pos {a b : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) : a ≤ b := by
  by_contra h
  have hab : b + 1 ≤ a := by omega
  rcases hn with hn | hn <;> nlinarith [sq_nonneg (a - b)]
```

## Lean の型

```lean
unit_order_pos_pos {a b : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) :
  a ≤ b
```

正の整数座標 `a`, `b` が、黄金整数のノルムに現れる二次形式

$$
a^2+ab-b^2
$$

について値 $1$ または $-1$ を取るなら、必ず

$$
a\le b
$$

であることを示す。

この補題自身は `GoldenInt` や `GoldenUnit` を引数に取らず、必要な算術条件だけを整数上へ切り出している。

## 数学的主張

黄金整数

$$
x=a+b\varphi
$$

のノルムは、この開発では座標上

$$
N(x)=a^2+ab-b^2
$$

として現れる。unit なら前段の結果から

$$
N(x)\in\{1,-1\}
$$

である。

本補題が扱うのは第一象限

$$
a>0,\qquad b>0
$$

である。この領域で $a>b$ と仮定すると、整数なので

$$
b+1\le a
$$

となる。この条件のもとでは二次形式 $a^2+ab-b^2$ は $\pm1$ にはなれず、矛盾する。したがって

$$
a\le b
$$

が強制される。

直観的には、黄金 unit の正・正座標は任意の方向へ伸びられるわけではなく、ノルム $\pm1$ という双曲線型の制約により `a` 側が `b` 側を越えられない、という局所的な順序制約である。

## 証明全体での役割

この補題は `GoldenUnitClassification` の **strict descent を成立させる符号別順序補題** の最初である。

直後には符号が異なる場合を扱う `unit_order_pos_neg` が続き、後段 `goldenUnit_descent` は座標の符号ごとに、`goldenPhi` または `goldenPhiInv` を掛けて measure を減らす。

実際に「両座標が正」の枝では、正本で次のように使われる。

```lean
have hord : x.fst ≤ x.snd := unit_order_pos_pos ha hb hn
let y := goldenMul x goldenPhiInv
refine ⟨y, goldenUnit_mul hx goldenUnit_phiInv, ?_, ?_⟩
```

0353 で得た座標公式

$$
(a,b)\xmapsto{\cdot\varphi^{-1}}(b-a,a)
$$

に対し、本補題の $a\le b$ により $b-a\ge0$ が保証される。そこで新しい measure は

$$
\mu((a+b\varphi)\varphi^{-1})
  =|b-a|+|a|
  =(b-a)+a
  =b.
$$

一方、元の measure は

$$
\mu(a+b\varphi)=a+b.
$$

$a>0$ なので

$$
b<a+b,
$$

ゆえに measure が厳密に減少する。

したがって本補題は単なる大小比較ではなく、0353 の座標変換を自然数 strong descent へ変換するための符号制御である。

## 直接依存する定義・補題

この `private theorem` は意図的に局所算術へ切り出されており、プロジェクト固有の定義を直接参照しない。

直接使うものは次である。

- `ℤ` — 座標 `a`, `b` の型。
- `omega` — `¬ a ≤ b` と整数順序から `b + 1 ≤ a` を得る。
- `sq_nonneg (a - b)` — 平方の非負性
  $$
  0\le(a-b)^2
  $$
  を `nlinarith` に供給する。
- `nlinarith` — ノルム値が $1$ の枝と $-1$ の枝を、それぞれ正値・順序条件と合わせて矛盾へ閉じる。
- `rcases` — `hn` の二つの可能性を分岐する。

概念上は `goldenNorm_eq_one_or_neg_one_of_unit` が後段でこの `hn` を供給するが、本補題の型には現れない。これは依存をよく分離した設計である。

## 証明の流れ

### 1. 結論を否定する

```lean
by_contra h
```

目標 `a ≤ b` を否定し、整数上で

```lean
h : ¬ a ≤ b
```

を得る。

### 2. 離散順序を一段強い形へ変換する

```lean
have hab : b + 1 ≤ a := by omega
```

整数では `a > b` が単に実数的な狭義不等式ではなく、少なくとも 1 の差を持つ。

$$
a>b
\quad\Longrightarrow\quad
b+1\le a.
$$

この「整数格子の 1 ステップ」を `omega` が抽出する。

### 3. ノルムの二ケースを分ける

```lean
rcases hn with hn | hn
```

これにより

$$
a^2+ab-b^2=1
$$

と

$$
a^2+ab-b^2=-1
$$

を別々に扱う。

### 4. 非線形算術で矛盾を閉じる

```lean
nlinarith [sq_nonneg (a - b)]
```

`ha`, `hb`, `hab`, 各枝の `hn` と

$$
(a-b)^2\ge0
$$

を組み合わせ、どちらの枝も不可能であることを示す。

`<;>` によって同じ `nlinarith` が両方の `hn` 分岐へ適用されるため、証明本体は非常に短い。

## Lean 固有の処理

### `private theorem`

この補題は namespace の公開 API を増やさず、`GoldenUnitClassification` 内部だけで利用される。数学的には独立した整数二次形式の補題だが、現在の設計では unit descent の実装詳細として扱われている。

### `omega` と `nlinarith` の役割分担

二つの tactic は異なる仕事をしている。

`omega` は整数の **離散線形順序** を扱い、

$$
\neg(a\le b)\Longrightarrow b+1\le a
$$

を作る。

一方 `nlinarith` は

$$
a^2,\ ab,\ b^2,\ (a-b)^2
$$

を含む **非線形多項式不等式** を処理する。

この分業により、整数の離散性と二次形式の非線形性をそれぞれ適切な tactic に任せている。

### `sq_nonneg`

`nlinarith` は多項式関係だけから必要な平方非負性を常に自動導入するわけではないため、

```lean
sq_nonneg (a - b)
```

を明示的に証拠として渡している。

## 冗長・重複箇所

証明そのものには目立った冗長性は少ない。

ただし後続には `unit_order_pos_neg` など、同じ二次形式

$$
a^2+ab-b^2=\pm1
$$

を符号領域ごとに扱う局所補題が並ぶ。これらは

1. 結論を否定する、
2. `omega` で整数の 1 ステップ差を得る、
3. `hn` を二分岐する、
4. `nlinarith` と平方非負性で閉じる、

という骨格を共有する可能性が高い。

一方、符号ごとに欲しい順序関係と descent で掛ける単元が異なるため、現状の小さな補題分割には可読性上の利点がある。

## 最適化候補

候補は次の通りである。

1. 正・正、正・負などの符号別補題に共通する非線形算術を、二次形式専用の一般補題へまとめられるか検討する。
2. `unit_order_pos_pos` は `GoldenInt` に依存しないため、もし他モジュールでも再利用するなら `private` を外し、黄金ノルム二次形式の汎用補題として配置する余地がある。
3. `sq_nonneg (a - b)` が本当に最小の補助不等式か、あるいはより直接的な因数分解・単調性補題で tactic 依存を減らせるか検討できる。

ただし 1 と 3 は Lean ビルドなしでは置換証明の成立を確認できないため、ここでは最適化候補に留める。

## 必要 Mathlib import と import 最適化候補

生成 standalone `Flt5DkMath/FLT5StandAlone.lean` は全体として

```lean
import Mathlib
```

を使用している。

本補題単独で必要になる主要機能は、

- 整数 `ℤ` とその線形順序、
- `omega`,
- `nlinarith`,
- `sq_nonneg`,

である。

したがって `import Mathlib` は宣言単体には広すぎる可能性が高い。`Mathlib.Tactic.Omega`、`Mathlib.Tactic.Nlinarith` と整数順序・環の基礎モジュールへ縮小できる可能性がある。

ただし今回は Lean ビルドを行わないため、 **厳密な最小 import 集合は未確認** である。

## Comparator challenge 化の可否

 **可能。難度は初級から中級。**

FLT5 全体を知らなくても、整数二次形式の局所問題として独立させやすい。

```lean
private theorem unit_order_pos_pos {a b : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) : a ≤ b := by
  ?_
```

Comparator で見るべき点は、

1. `by_contra` から整数の `b + 1 ≤ a` を取り出せるか、
2. `hn` の disjunction を正しく分解できるか、
3. 非線形算術に必要な `sq_nonneg` を発見できるか、
4. `omega` と `nlinarith` を役割分担させられるか、

である。

さらに tactic 制限版として `nlinarith` を使わず、二次形式の下界を明示的に導く challenge にすると、数学的構造をより強く問える。

## 次に読むべき宣言

次は 0358 `unit_order_pos_neg` である。宣言種別は **`private theorem`**。

```lean
private theorem unit_order_pos_neg {a b : ℤ}
    (ha : 0 < a) (hb : b < 0)
    (hn : a ^ 2 + a * b - b ^ 2 = 1 ∨
      a ^ 2 + a * b - b ^ 2 = -1) : -b ≤ a := by
  by_contra h
  have hab : a + 1 ≤ -b := by omega
  ...
```

0357 が正・正領域で $a\le b$ を与えたのに対し、0358 は正・負領域で

$$
-b\le a
$$

を与える。これにより `goldenUnit_descent` の次の符号枝で、どちらの単元作用を選べば measure が減少するかを制御する。
