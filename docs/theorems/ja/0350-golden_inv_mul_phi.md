# 0350 — `golden_inv_mul_phi`

## 宣言種別

この宣言は **`theorem`** である。

```lean
theorem golden_inv_mul_phi :
    goldenMul goldenPhiInv goldenPhi = goldenOne := by decide
```

## Lean の型

```lean
golden_inv_mul_phi :
  goldenMul goldenPhiInv goldenPhi = goldenOne
```

左辺は黄金整数環の具体的要素

```lean
goldenPhiInv : GoldenInt
goldenPhi    : GoldenInt
```

をこの順序で掛けたものであり、右辺は乗法単位元

```lean
goldenOne : GoldenInt
```

である。したがって、この theorem は `goldenPhiInv` が `goldenPhi` の左逆元であることを具体的な座標計算で証明する。

## 数学的主張

座標モデルでは

$$
goldenPhiInv = \varphi-1,
\qquad
goldenPhi = \varphi.
$$

黄金比の基本関係

$$
\varphi^2=\varphi+1
$$

から

$$
(\varphi-1)\varphi
=\varphi^2-\varphi
=1.
$$

よって数学的には

$$
\varphi^{-1}\varphi=1
$$

を確認している。

`GoldenInt` の座標を直接使えば

```lean
goldenPhiInv = ⟨-1, 1⟩
goldenPhi    = ⟨0, 1⟩
goldenOne    = ⟨1, 0⟩
```

である。黄金整数の乗法

$$
(a+b\varphi)(c+d\varphi)
=(ac+bd)+(ad+bc+bd)\varphi
$$

へ代入すると

$$
(-1+\varphi)(0+\varphi)
=1+0\varphi,
$$

となり、右辺はちょうど `goldenOne` である。

## 証明全体での役割

0348 `goldenPhiInv` では $\varphi-1$ に対応する具体的要素を定義し、0349 `golden_phi_mul_inv` で

$$
\varphi(\varphi-1)=1
$$

という一方向の逆元則を得た。本 theorem は積の順序を反転した

$$
(\varphi-1)\varphi=1
$$

を与え、`goldenPhiInv` が `goldenPhi` の両側逆元であることを完成させる。

依存の流れは

```text
goldenPhiInv
  → golden_phi_mul_inv
  → golden_inv_mul_phi
  → goldenUnit_phiInv
  → goldenUnit_descent
  → GoldenUnitFifthClass
```

である。

直後の `goldenUnit_phiInv` は `GoldenUnit goldenPhiInv` の witness として `goldenPhi` を選び、本 theorem と 0349 をそのまま二つの逆元証明として格納する。

```lean
theorem goldenUnit_phiInv : GoldenUnit goldenPhiInv := by
  exact ⟨goldenPhi, golden_inv_mul_phi, golden_phi_mul_inv⟩
```

さらに後続の `goldenUnit_descent` では `goldenPhiInv` を掛ける下降分岐の再構成時に

```lean
show goldenPhiInv * goldenPhi = 1 by exact golden_inv_mul_phi
```

が実際に用いられる。したがって、本 theorem は単なる対称形の補題ではなく、unit descent の可逆性を一方向から直接支える証明である。

## 直接依存する定義・補題

宣言本体が直接参照するプロジェクト宣言は次の四つである。

- `goldenMul` — `GoldenInt` 上の黄金整数乗法。
- `goldenPhiInv` — 0348 で定義した $\varphi-1$、座標 `⟨-1,1⟩`。
- `goldenPhi` — 基底元 $\varphi$、座標 `⟨0,1⟩`。
- `goldenOne` — 乗法単位元、座標 `⟨1,0⟩`。

証明本体は Lean の `decide` を直接使う。

0349 `golden_phi_mul_inv` は数学的には非常に近いが、本 theorem の証明項はそれを参照していない。現行コードでは左右それぞれを独立した閉計算として認証している。

数学的背景の $\varphi^2=\varphi+1$ は `goldenMul` の座標演算へ既に組み込まれているので、`golden_phi_sq` のような環等式を明示的に rewrite する必要はない。

## 証明の流れ

証明は一行である。

```lean
by decide
```

計算内容を展開して読むと、次の流れになる。

1. `goldenPhiInv` を `⟨-1,1⟩` に展開する。
2. `goldenPhi` を `⟨0,1⟩` に展開する。
3. `goldenMul` の定義で二座標を計算する。
4. 積が `⟨1,0⟩` になる。
5. `goldenOne` も `⟨1,0⟩` なので、構造体の等式が成立する。

目標は変数を含まない閉じた命題であり、整数演算と `GoldenInt` の等式が決定可能なので、`decide` が評価によって証明項を生成できる。

## Lean 固有の処理

### `by decide`

この theorem は `ring`、`norm_num`、`simp`、`ext` などを使わず、

```lean
by decide
```

だけで閉じる。

これは抽象的に「可換環では右逆元なら左逆元」と証明しているわけではない。`goldenPhiInv`、`goldenPhi`、`goldenOne` がすべて具体値で、`goldenMul` も計算可能なので、**具体的な `GoldenInt` の等式そのものを判定している**。

### 左右逆元を独立に計算する設計

0349 と 0350 は数学的には可換性から互いに導出できるが、Lean コードでは双方を `by decide` で独立に証明する。このため 0350 は 0349 への proof dependency を持たず、後続の `GoldenUnit` 構築へ二つの独立した閉計算 certificate を供給する。

### `goldenMul` と `*` の表記差

定理文は

```lean
goldenMul goldenPhiInv goldenPhi
```

という明示的関数を使う。一方、後続の descent では

```lean
goldenPhiInv * goldenPhi
```

という ring notation が現れる。前段で構成済みの ring instance によって両表現が接続され、後続では

```lean
show goldenPhiInv * goldenPhi = 1 by exact golden_inv_mul_phi
```

の形で本 theorem を利用できる。

## 冗長・重複箇所

0349

```lean
theorem golden_phi_mul_inv :
    goldenMul goldenPhi goldenPhiInv = goldenOne := by decide
```

と本 theorem は、因子の順序を交換しただけでほぼ同じ closed computation である。

`GoldenInt` の乗法可換性を利用すれば、一方を他方から導く設計も考えられる。概念的には

```lean
simpa [mul_comm] using golden_phi_mul_inv
```

のような短縮候補がある。

ただし現行の `by decide` も一語であり、可換性 lemma を依存に追加しない。したがってコード行数・依存の局所性・proof robustness の観点では、現行の重複は合理的でもある。

## 最適化候補

局所的には現行の

```lean
by decide
```

がすでにほぼ最小である。

設計上検討できる候補は次の通り。

1. 0349 と 0350 の片方だけを `decide` で証明し、もう片方を乗法可換性から導く。
2. 二つの inverse law を `[simp]` 候補として検討し、後続 descent の明示的な `show ... by exact ...` を簡略化できるか調べる。
3. `goldenUnit_phiInv` までを一つの unit-constructor API として整理し、左右逆元 lemma を局所補題化する案を検討する。
4. 後に `GoldenUnit` と Mathlib の `IsUnit` / `Units` が接続されるなら、逆元 certificate の置き場所を標準 unit API に寄せられるか検討する。

ただし、`[simp]` 化による rewrite set への影響や、可換性経由の証明が実際に既存依存を減らすかは Lean ビルドなしでは確認できない。よって以上は最適化 **候補** であり、現行実装の欠陥を意味しない。

## 必要 Mathlib import と import 最適化候補

リポジトリの生成 standalone `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem 自身が外部機構として直接必要とするものは主として

- `Decidable` / `decide`
- 整数 `ℤ` と具体的整数計算
- `GoldenInt` の decidable equality を成立させる基盤

であり、`ring`、`omega`、`norm_num` などの tactic は本証明では使わない。

ただし `GoldenInt`、`goldenMul`、ring instance などは前段のプロジェクト宣言に依存しており、standalone は元のモジュール境界を一つへ結合して `import Mathlib` で包んでいる。そのため、本 theorem だけを見て元モジュールの厳密な最小 Mathlib import 集合を確定することはできない。

今回は Lean ビルドを行わないため、細分化した import 候補は **未確認** とする。少なくとも、本 theorem の一行証明そのものが Mathlib 全体の tactic 群を要求しているわけではない。

## Comparator challenge 化の可否

**非常に適している。難度は初級。**

最小 challenge は

```lean
example :
    goldenMul goldenPhiInv goldenPhi = goldenOne := by
  ?_
```

であり、正本と同じ

```lean
decide
```

で閉じる。

Comparator challenge としては、solver が

- 目標が具体的な structure equality であること、
- すべての項が定義展開可能な閉じた値であること、
- 一般環論へ進まず `decide` を選べること

を認識できるかを見る小型課題になる。

0349 と対にして二つの向きの証明を与え、一方だけを穴にする challenge なら、「既知 theorem を可換性で再利用する」解と「独立に `decide` する」解の比較も可能である。

ただし数学的難度は低いので、大規模 Comparator の能力差を測る課題というより、定義展開・closed computation・局所的な証明戦略選択を評価する micro challenge に向く。

## 次に読むべき宣言

次は **0351 `goldenUnit_phiInv`** を読むべきである。宣言種別は **`theorem`**。

```lean
theorem goldenUnit_phiInv : GoldenUnit goldenPhiInv := by
  exact ⟨goldenPhi, golden_inv_mul_phi, golden_phi_mul_inv⟩
```

`GoldenUnit` は

```lean
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧
    goldenMul eta epsilon = goldenOne
```

という二側逆元の存在命題である。

0351 では witness に `goldenPhi` を選び、今回の

$$
(\varphi-1)\varphi=1
$$

と 0349 の

$$
\varphi(\varphi-1)=1
$$

を組み合わせて、`goldenPhiInv = \varphi-1` を正式な `GoldenUnit` certificate へ昇格させる。ここから unit descent の本体へ進む。
