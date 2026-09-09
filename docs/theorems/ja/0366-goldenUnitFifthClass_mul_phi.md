# 0366 — `goldenUnitFifthClass_mul_phi`

## 宣言種別

この宣言は **`theorem`** である。

```lean
theorem goldenUnitFifthClass_mul_phi {x : GoldenInt}
    (hx : GoldenUnitFifthClass x) :
    GoldenUnitFifthClass (goldenMul x goldenPhi) := by
  rcases hx with ⟨i, delta, hx⟩
  fin_cases i
  · refine ⟨⟨1, by decide⟩, delta, ?_⟩
    rw [hx]
    simp only [golden_mul_eq, golden_pow_eq]
    ring
  · refine ⟨⟨2, by decide⟩, delta, ?_⟩
    rw [hx]
    simp only [golden_mul_eq, golden_pow_eq]
    ring
  · refine ⟨⟨3, by decide⟩, delta, ?_⟩
    rw [hx]
    simp only [golden_mul_eq, golden_pow_eq]
    ring
  · refine ⟨⟨4, by decide⟩, delta, ?_⟩
    rw [hx]
    simp only [golden_mul_eq, golden_pow_eq]
    ring
  · refine ⟨⟨0, by decide⟩, goldenMul goldenPhi delta, ?_⟩
    rw [hx]
    simp only [golden_mul_eq, golden_pow_eq]
    ring
```

Lean 正本では本定理は `goldenUnitFifthClass_mul_phiInv` より先に置かれている。既存の解説列では `...mul_phiInv` とその後の基底ケースが先に文書化されていたため、本ファイルはその取りこぼしを補完するものである。

## Lean の型

```lean
goldenUnitFifthClass_mul_phi :
  {x : GoldenInt} →
  GoldenUnitFifthClass x →
  GoldenUnitFifthClass (goldenMul x goldenPhi)
```

`GoldenUnitFifthClass x` は

```lean
∃ i : Fin 5, ∃ delta : GoldenInt,
  x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

という存在命題である。したがって本定理は、`x` が five-sector 表現を持つなら、その `φ` 倍も five-sector 表現を持つことを示す。

## 数学的主張

仮定を

$$
x=\varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\}
$$

と読むと、本定理は

$$
x\varphi
$$

も同じ形式

$$
\varphi^j\gamma^5
$$

に書けることを示す。

sector 遷移は

$$
0\longmapsto1,
\qquad
1\longmapsto2,
\qquad
2\longmapsto3,
\qquad
3\longmapsto4,
\qquad
4\longmapsto0.
$$

すなわち指数だけを見れば

$$
i\longmapsto i+1\pmod 5
$$

である。

最初の四枝では fifth-power witness `delta` をそのまま保つ。最後の `4 → 0` だけは

$$
\varphi^4\delta^5\cdot\varphi
=\varphi^5\delta^5
=(\varphi\delta)^5
$$

とまとめるため、witness を

$$
\delta\longmapsto\varphi\delta
$$

へ更新する。

## 証明全体での役割

0359 `goldenUnit_descent` は、measure が 1 より大きい golden unit `x` から、より小さい golden unit `y` を得て、

$$
x=y\varphi
$$

または

$$
x=y\varphi^{-1}
$$

と復元できることを示す。

strong induction で全 unit を fifth class に分類するには、帰納法で得た `GoldenUnitFifthClass y` から `yφ` と `yφ⁻¹` の双方へ分類を戻せなければならない。

本定理はその `φ` 側を担当し、`goldenUnitFifthClass_mul_phiInv` が `φ⁻¹` 側を担当する。

後続 `goldenUnitFifthClass_of_unit` では、降下から得た復元式が `x = yφ` の枝で

```lean
exact goldenUnitFifthClass_mul_phi hyClass
```

と直接使用される。したがって本定理は、局所的な five-sector 算術と unit descent の strong induction を接続する主要な閉性補題である。

## 直接依存する定義・補題

プロジェクト側の主な直接依存は次である。

- `GoldenInt` — 黄金整数の座標型。
- `goldenPhi` — 黄金比 unit `φ`。
- `goldenMul` — 黄金整数の乗法。
- `goldenPow` — 黄金整数の冪。
- `GoldenUnitFifthClass` — `x = φ^i δ^5`, `i : Fin 5` という分類 predicate。
- `golden_mul_eq` — `goldenMul` と通常の `(*)` を結ぶ rewrite 用等式。
- `golden_pow_eq` — `goldenPow` と通常の `(^)` を結ぶ rewrite 用等式。

Lean / Mathlib 側では `rcases`, `fin_cases`, `refine`, `decide`, `rw`, `simp only`, `ring` を直接用いる。

`golden_sector_zero_mul_phiInv` や `golden_sector_succ_mul_phiInv` は本定理には依存しない。これらは逆方向の `φ⁻¹` 遷移専用である。

## 証明・構築の流れ

### 1. fifth-class witness を展開する

```lean
rcases hx with ⟨i, delta, hx⟩
```

で

- `i : Fin 5`
- `delta : GoldenInt`
- `hx : x = φ^i δ^5`

を取り出す。

### 2. `Fin 5` を完全列挙する

```lean
fin_cases i
```

により `i = 0,1,2,3,4` の五枝へ分ける。

これは数学上の

$$
i\mapsto i+1\pmod5
$$

を modular arithmetic の一般補題へ抽象化せず、五つの concrete case として実装する方針である。

### 3. `0 → 1`, `1 → 2`, `2 → 3`, `3 → 4`

最初の四枝では新しい sector をそれぞれ `1,2,3,4` とし、`delta` は変更しない。

例えば `i = 0` では

```lean
refine ⟨⟨1, by decide⟩, delta, ?_⟩
rw [hx]
simp only [golden_mul_eq, golden_pow_eq]
ring
```

である。

`rw [hx]` で `x` を既知の sector 表現へ置き換え、wrapper を `simp only` で通常の乗法・冪へ落とし、最後は可換環の恒等式として `ring` で閉じる。

### 4. `4 → 0` の wrap-around

最後の枝では

```lean
refine ⟨⟨0, by decide⟩, goldenMul goldenPhi delta, ?_⟩
```

を選ぶ。

これは

$$
\varphi^4\delta^5\varphi
=\varphi^5\delta^5
=(\varphi\delta)^5
$$

という fifth power への吸収を、そのまま existential witness として表現している。

この枝でも `rw`, `simp only`, `ring` の三段階で閉じる。

## Lean 固有の処理

### `fin_cases i`

`Fin 5` の全要素を完全列挙する。有限 sector の遷移表がコード上で明示されるため、監査性は高い。

### `⟨k, by decide⟩ : Fin 5`

新 sector の値 `k` と、その境界条件 `k < 5` を同時に構成する。`k` は閉じた具体数なので `decide` で十分である。

### `simp only [golden_mul_eq, golden_pow_eq]`

project 固有 wrapper のみを通常の ring 表現へ変換する。`only` により広い simp set への依存を避けている。

### `ring`

本定理の各枝は、sector と witness を選び終えれば純粋な可換環恒等式になる。特に `4 → 0` でも、`(φδ)^5 = φ^5δ^5` を含む展開を `ring` が処理する。

## 冗長・重複箇所

五枝すべてで

```lean
rw [hx]
simp only [golden_mul_eq, golden_pow_eq]
ring
```

が繰り返される。また最初の四枝は新 sector の数値以外ほぼ同型である。

一方、この重複によって

- sector 遷移表が一目で分かる。
- `Fin` の加算や剰余演算の補題が不要になる。
- 各枝の failure point が局所化される。

という利点があるため、必ずしも悪い冗長性ではない。

## 最適化候補

1. `i.val + 1 < 5` の通常枝と `i = 4` の wrap-around の二枝へまとめる。
2. `Fin 5` 上の cyclic successor を定義し、sector 遷移を一つの API にする。
3. `φ` 倍と `φ⁻¹` 倍の閉性を、符号付き unit step の一般定理として統合する。
4. `golden_mul_eq` / `golden_pow_eq` を局所 simp API として整備し、反復する `simp only` を短縮する。
5. 五枝の `rw; simp only; ring` を小さな補助 lemma へ抽出する。

ただし、これらは現行の五枝明示版より proof term や依存が単純になるとは限らない。Lean ビルドは禁止条件のため、最適化案の実コンパイル確認は行っていない。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は全体として

```lean
import Mathlib
```

を使用する。

本 theorem 単体で目立つ Mathlib 機能は

- `Fin 5`
- `fin_cases`
- `decide`
- `ring`
- `rw`
- `simp only`

である。

したがって `Mathlib` 全体は単体には広すぎる可能性が高い。候補として `Fin` の case tactic、ring normalization、基本 tactic 群を提供するより狭い import へ分解できる可能性があるが、正確な最小 import 集合は実ビルドなしには断定しない。

## Comparator challenge 化

 **可能であり、良い中級 micro challenge 候補** である。

課題としては `GoldenUnitFifthClass`, `goldenPhi`, `golden_mul_eq`, `golden_pow_eq` までを与え、

```lean
theorem challenge {x : GoldenInt}
    (hx : GoldenUnitFifthClass x) :
    GoldenUnitFifthClass (goldenMul x goldenPhi) := by
  ...
```

を完成させる形が適する。

評価点は

- existential witness の取り出しと再構成
- `Fin 5` の有限 case split
- wrap-around で witness を `φδ` に変更できるか
- project wrapper を ring expression へ変換できるか

である。

`ring` に任せる代数部分は重くないため、Comparator では「有限分類と witness 設計」を主眼にできる。

## 次に読むべき宣言

Lean 正本で直後に置かれる宣言は

```lean
theorem goldenUnitFifthClass_mul_phiInv ...
```

であり、これは既に `0364-goldenUnitFifthClass_mul_phiInv.md` として解説済みである。その次の `goldenUnitFifthClass_one` も 0365 で解説済みである。

したがって、 **次に未解説として読むべき宣言** は

```lean
private theorem goldenUnitFifthClass_neg_one :
    GoldenUnitFifthClass (-goldenOne) := by
  refine ⟨⟨0, by decide⟩, -goldenOne, ?_⟩
  decide
```

である。

これは measure `1` の四基底 unit のうち `-1` を sector `0` に登録する `private theorem` であり、後続 `goldenUnitFifthClass_of_unit` の基底ケースで直接使われる。