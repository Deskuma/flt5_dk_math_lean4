# 0349 — `golden_phi_mul_inv`

## 宣言種別

この宣言は **`theorem`** である。

```lean
theorem golden_phi_mul_inv :
    goldenMul goldenPhi goldenPhiInv = goldenOne := by decide
```

## Lean の型

```lean
golden_phi_mul_inv :
  goldenMul goldenPhi goldenPhiInv = goldenOne
```

左辺は黄金整数環の具体的な二要素

```lean
goldenPhi    : GoldenInt
goldenPhiInv : GoldenInt
```

の積であり、右辺は乗法単位元

```lean
goldenOne : GoldenInt
```

である。したがって、この theorem は `goldenPhiInv` が `goldenPhi` の右逆元であることを証明する等式である。

## 数学的主張

座標モデルでは

$$
goldenPhi = \varphi,
\qquad
goldenPhiInv = \varphi-1.
$$

黄金比の関係

$$
\varphi^2=\varphi+1
$$

を使えば

$$
\varphi(\varphi-1)
=\varphi^2-\varphi
=1.
$$

よって数学的には

$$
\varphi\,\varphi^{-1}=1
$$

を確認している。

`GoldenInt` の座標を直接使うと、`goldenPhi = ⟨0,1⟩`、`goldenPhiInv = ⟨-1,1⟩` であり、黄金整数の乗法

$$
(a+b\varphi)(c+d\varphi)
=(ac+bd)+(ad+bc+bd)\varphi
$$

に代入して

$$
(0+\varphi)(-1+\varphi)
=1+0\varphi
$$

となる。右辺が `goldenOne = ⟨1,0⟩` である。

## 証明全体での役割

0348 `goldenPhiInv` は単に `⟨-1,1⟩` という環要素を定義しただけで、そこには逆元性の証明は含まれていなかった。本 theorem は、その要素が実際に `goldenPhi` を右から打ち消すことを認証する最初の verification theorem である。

流れは

```text
goldenPhiInv
  → golden_phi_mul_inv
  → golden_inv_mul_phi
  → goldenUnit_phiInv
  → goldenUnit_descent
  → goldenUnitFifthClass_of_unit
```

となる。

直後の `golden_inv_mul_phi` が反対向き

$$
\varphi^{-1}\varphi=1
$$

を証明し、両方の等式を使って `goldenUnit_phiInv` が `goldenPhiInv` を `GoldenUnit` として包装する。

さらに後続の `goldenUnit_descent` では、unit の座標符号に応じて `goldenPhi` または `goldenPhiInv` を掛けて measure を減少させる。その際、元の unit を再構成する式で

```lean
show goldenPhi * goldenPhiInv = 1 by exact golden_phi_mul_inv
```

が実際に使用される。したがってこの theorem は小さいが、unit descent の可逆性を保証する基礎証明である。

## 直接依存する定義・補題

宣言本体が直接参照するプロジェクト宣言は次の四つである。

- `goldenMul` — `GoldenInt` 上の黄金整数乗法
- `goldenPhi` — 基底元 $\varphi$、座標では `⟨0,1⟩`
- `goldenPhiInv` — 0348 で定義した $\varphi-1$、座標では `⟨-1,1⟩`
- `goldenOne` — 乗法単位元、座標では `⟨1,0⟩`

証明 tactic としては Lean の `decide` を直接使用する。

数学的背景としては `goldenMul` の定義が $\varphi^2=\varphi+1$ を座標演算へ組み込んでいるため、ここで `golden_phi_sq` を明示的に rewrite する必要はない。

## 証明の流れ

証明は一行である。

```lean
by decide
```

内部的には次の具体計算へ還元できる。

1. `goldenPhi` を `⟨0,1⟩` に展開する。
2. `goldenPhiInv` を `⟨-1,1⟩` に展開する。
3. `goldenMul` を展開して積の二座標を計算する。
4. 結果が `⟨1,0⟩` になる。
5. それが `goldenOne` の定義と一致するため、構造体の等式が成立する。

すべての値が閉じた整数式であり、命題の等式判定が計算可能なので、`decide` が証明項を生成できる。

## Lean 固有の処理

### `by decide`

この theorem の特徴は、`ring`、`norm_num`、`simp`、`ext` を一切書かず、決定可能命題の評価だけで閉じていることである。

```lean
by decide
```

は一般的な環論を証明しているのではなく、**完全に具体化された `GoldenInt` 同士の等式を計算して判定している**。

そのため、この証明が短いのは黄金整数環の一般定理が自動的に導出されたからではなく、`goldenPhi`、`goldenPhiInv`、`goldenOne` がすべて concrete data であり、`goldenMul` も計算可能な定義だからである。

### 定義展開による証明

この形は definitional reduction と decidable equality に強く依存する。もし `goldenPhiInv` を opaque な存在証明から選んだ値として定義していたなら、同じ `by decide` は成立しない可能性が高い。

0348 が `⟨-1,1⟩` を直接定義した設計が、ここで極めて短い verification proof を可能にしている。

### `goldenMul` と `*`

定理文ではあえて

```lean
goldenMul goldenPhi goldenPhiInv
```

と明示的な関数名を使っている。一方、後続証明では `goldenPhi * goldenPhiInv` という ring notation も使われる。両者は既存 instance / simp bridge により接続される。

## 冗長・重複箇所

直後には

```lean
theorem golden_inv_mul_phi :
    goldenMul goldenPhiInv goldenPhi = goldenOne := by decide
```

があり、本 theorem とほぼ左右を交換しただけの証明になっている。

数学的に `GoldenInt` の乗法可換性を既に利用できるなら、一方を他方と可換性から導くことも可能である。例えば概念的には

```lean
simpa [mul_comm] using golden_phi_mul_inv
```

のような方向が考えられる。

ただし現行の二つの `by decide` はそれぞれ独立な closed computation であり、非常に安定して短い。片方を可換性へ依存させると dependency が増えるため、重複削減が必ずしも改善とは限らない。

## 最適化候補

局所的には現行の

```lean
by decide
```

がほぼ最小であり、proof term の短縮余地はない。

検討できる候補は次の通りである。

1. `golden_phi_mul_inv` と `golden_inv_mul_phi` の片方だけを concrete computation で証明し、他方を可換性から導出する。
2. 両 theorem を `[simp]` lemma として扱うことで、後続の

   ```lean
   show goldenPhi * goldenPhiInv = 1 by exact golden_phi_mul_inv
   ```

   のような明示的 bridge を簡略化できる可能性を調べる。
3. `goldenPhiInv` を最終的に ring の `IsUnit` / `Units` API へ統合するなら、左右逆元 theorem の API 配置を整理する。

ただし `[simp]` 化が既存 rewrite set に与える影響や、可換性経由への変更が実際に簡潔になるかは Lean ビルドを行わずには確認できない。したがって、これらは **候補** であり、現行コードに問題があるという意味ではない。

## 必要 Mathlib import と import 最適化候補

リポジトリ内の生成 standalone `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem 単体で外部に必要な要素は、主として

- `Decidable` / `decide`
- 整数 `ℤ` と数値計算
- structure equality の決定可能性

であり、環 tactic は使用していない。

一方、`GoldenUnitClassification` セクションが依存する `GoldenInt`、ring instance、`goldenMul`、unit API は前段の多数のプロジェクト宣言を経由している。生成 artifact では module ごとの個別 import 行が除去され、standalone 全体を `import Mathlib` で包んでいるため、この theorem だけから元モジュールの厳密な最小 Mathlib import 集合を確定することはできない。

Lean ビルドを行っていないので、`Mathlib` の細分化候補は **未確認** である。ただし本証明が `decide` のみであることから、少なくとも `Mathlib` 全体をこの theorem 自身が要求しているわけではない。

## Comparator challenge 化の可否

**非常に適している。難度は初級。**

例えば次の穴埋めにできる。

```lean
example :
    goldenMul goldenPhi goldenPhiInv = goldenOne := by
  ?_
```

最短解は

```lean
exact of_decide_eq_true rfl
```

のような低水準形を探す必要はなく、正本と同じ

```lean
decide
```

で閉じる。

Comparator challenge として見ると、これは solver が

- concrete structure equality であること
- 定義展開可能であること
- `decide` が適切であること

を認識できるかを測れる。

より識別力を上げるなら、`goldenPhiInv` の定義自体も穴にして

```lean
def candidate : GoldenInt := ?_

example : goldenMul goldenPhi candidate = goldenOne := by
  ?_
```

とすれば、逆元座標の発見と verification の両方を課題にできる。

## 次に読むべき宣言

次は **0350 `golden_inv_mul_phi`** を読むべきである。宣言種別は **`theorem`**。

```lean
theorem golden_inv_mul_phi :
    goldenMul goldenPhiInv goldenPhi = goldenOne := by decide
```

0349 が

$$
\varphi(\varphi-1)=1
$$

を確認したのに対し、0350 は積の順序を反転した

$$
(\varphi-1)\varphi=1
$$

を確認する。

その次の `goldenUnit_phiInv` がこの二つの等式をまとめて `goldenPhiInv` の unit certificate を構築するため、0350 は unit 化の直前に必要なもう一方の inverse law である。
