# 0370 `goldenUnitFifthClass_of_unit`

## 宣言種別

`theorem`

## Lean コード

```lean
/-- The direct coordinate descent classifies every golden unit modulo fifth powers. -/
theorem goldenUnitFifthClass_of_unit (x : GoldenInt) (hx : GoldenUnit x) :
    GoldenUnitFifthClass x := by
  generalize hm : goldenUnitMeasure x = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
      have hpos : 0 < n := by rw [← hm]; exact goldenUnitMeasure_pos hx
      rcases eq_or_lt_of_le (show 1 ≤ n by omega) with hn | hn
      · have hm1 : goldenUnitMeasure x = 1 := by omega
        rcases goldenUnit_measure_one_cases hx hm1 with h | h | h | h
        · simpa [h] using goldenUnitFifthClass_one
        · simpa [h] using goldenUnitFifthClass_neg_one
        · simpa [h] using goldenUnitFifthClass_phi
        · simpa [h] using goldenUnitFifthClass_neg_phi
      · obtain ⟨y, hy, hylt, hrec⟩ := goldenUnit_descent hx (by omega)
        have hyClass : GoldenUnitFifthClass y :=
          ih (goldenUnitMeasure y) (by omega) y hy rfl
        rcases hrec with hrec | hrec
        · rw [hrec]
          exact goldenUnitFifthClass_mul_phi hyClass
        · rw [hrec]
          exact goldenUnitFifthClass_mul_phiInv hyClass
```

## Lean の型

```lean
goldenUnitFifthClass_of_unit
  (x : GoldenInt)
  (hx : GoldenUnit x) :
  GoldenUnitFifthClass x
```

任意の黄金整数 `x` が `GoldenUnit` であるなら、`x` は fifth powers を法として `1, φ, φ², φ³, φ⁴` のいずれかの代表に属することを示す。

`GoldenUnitFifthClass x` の定義を展開すると、結論は

```lean
∃ i : Fin 5, ∃ delta : GoldenInt,
  x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

である。

数学的には

$$
x = \varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\}
$$

という表示がすべての黄金 unit に対して存在することを主張する。

## 数学的主張

黄金整数環の unit を fifth powers で割った剰余類は、`φ` の指数を法 5 で見た五つの class に縮約できる。

すなわち任意の unit $x$ に対し、ある $i\in\{0,1,2,3,4\}$ と黄金整数 $\delta$ が存在して

$$
x=\varphi^i\delta^5
$$

となる。

符号は 5 が奇数であるため

$$
(-\delta)^5=-\delta^5
$$

として fifth-power 側へ吸収できる。そのため代表元に `-1`, `-φ`, … を別途追加する必要はない。

この theorem の証明は unit 群の抽象的構造定理を直接呼ぶのではなく、整数座標上の measure と strict descent を使って構成的に分類を実現している。

## 証明全体での役割

これは `GoldenUnitClassification.lean` の中心定理である。

直前までに準備された要素は大きく三群に分かれる。

1. `goldenUnitMeasure` による正の自然数 measure。
2. measure が 1 のときの四つの終端 unit

$$
1,\quad -1,\quad \varphi,\quad -\varphi.
$$

3. measure が 1 より大きいとき、より小さい unit `y` へ降下し、元の `x` を

$$
x=y\varphi
$$

または

$$
x=y\varphi^{-1}
$$

として復元する strict descent。

今回の theorem はこれらを `Nat.strong_induction_on` で統合する。

さらに、既に証明済みの

```lean
goldenUnitFifthClass_mul_phi
goldenUnitFifthClass_mul_phiInv
```

によって、降下先 `y` の fifth class を元の `x` へ持ち上げる。

したがって、この theorem が成立すると直後の

```lean
theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

はほぼラッパーとして完成する。そこから stripped packet の unit factor を五つの sector に有限化する `SignedGoldenFiniteUnitSectorCore` へ接続される。

## 直接依存する定義・補題

### `GoldenUnitFifthClass`

結論の述語。

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

### `goldenUnitMeasure`

strong induction の measure。`x` 自身ではなく

```lean
goldenUnitMeasure x : ℕ
```

に対して帰納する。

### `goldenUnitMeasure_pos`

unit の measure が正であることを与える。

証明中では

```lean
have hpos : 0 < n := by
  rw [← hm]
  exact goldenUnitMeasure_pos hx
```

として、`n=0` を排除する。

### `goldenUnit_measure_one_cases`

measure が 1 の unit を

$$
1,-1,\varphi,-\varphi
$$

の四つへ分類する基底ケース定理。

### `goldenUnitFifthClass_one`

$$
1=\varphi^0 1^5
$$

を与える。

### `goldenUnitFifthClass_neg_one`

$$
-1=\varphi^0(-1)^5
$$

を与える。

### `goldenUnitFifthClass_phi`

$$
\varphi=\varphi^1 1^5
$$

を与える。

### `goldenUnitFifthClass_neg_phi`

$$
-\varphi=\varphi^1(-1)^5
$$

を与える。

### `goldenUnit_descent`

measure が 1 より大きい unit `x` から、より小さい unit `y` を構成する strict descent。

証明で必要な出力は概念的に

```lean
∃ y,
  GoldenUnit y ∧
  goldenUnitMeasure y < goldenUnitMeasure x ∧
  (x = goldenMul y goldenPhi ∨
   x = goldenMul y goldenPhiInv)
```

という形である。

### `goldenUnitFifthClass_mul_phi`

`y` が fifth class に属すれば `yφ` も fifth class に属することを示す。

sector は

$$
i\mapsto i+1\pmod 5
$$

と進む。

### `goldenUnitFifthClass_mul_phiInv`

`y` が fifth class に属すれば $y\varphi^{-1}$ も fifth class に属することを示す。

sector は

$$
i\mapsto i-1\pmod 5
$$

と進む。

### `Nat.strong_induction_on`

通常の `n → n+1` 型帰納法ではなく、任意の strictly smaller measure に帰納仮定を適用するために用いる。

## 証明の流れ

### 1. measure を新しい自然数 `n` として固定する

```lean
generalize hm : goldenUnitMeasure x = n
```

これにより goal 中の複雑な measure 式を自然数変数 `n` として扱えるようにする。

### 2. `n` に strong induction をかける

```lean
induction n using Nat.strong_induction_on generalizing x with
| h n ih =>
```

`generalizing x` が重要である。降下後には元と異なる unit `y` に帰納仮定を適用する必要があるため、`x` を固定したままでは足りない。

### 3. unit の measure が正であることを得る

```lean
have hpos : 0 < n := by
  rw [← hm]
  exact goldenUnitMeasure_pos hx
```

したがって

$$
1\le n
$$

である。

### 4. `n=1` と `1<n` に分ける

```lean
rcases eq_or_lt_of_le (show 1 ≤ n by omega) with hn | hn
```

これが基底ケースと descent case の境界である。

### 5. measure-one 基底を四分岐で閉じる

`n=1` なら

```lean
have hm1 : goldenUnitMeasure x = 1 := by omega
```

を得て、

```lean
rcases goldenUnit_measure_one_cases hx hm1 with h | h | h | h
```

で `x` を四つの具体 unit に分類する。

各分岐は既存の具体 fifth-class theorem を `simpa [h]` で転送するだけで閉じる。

### 6. measure が大きい場合は strict descent を行う

```lean
obtain ⟨y, hy, hylt, hrec⟩ :=
  goldenUnit_descent hx (by omega)
```

ここで

- `hy : GoldenUnit y`
- `hylt : goldenUnitMeasure y < goldenUnitMeasure x`
- `hrec` : `x` が `yφ` または `yφ⁻¹`

を得る。

### 7. 小さい `y` に帰納仮定を適用する

```lean
have hyClass : GoldenUnitFifthClass y :=
  ih (goldenUnitMeasure y) (by omega) y hy rfl
```

strong induction の核心はここである。

`hylt` と `hm` から

$$
goldenUnitMeasure(y)<n
$$

を `omega` で示し、帰納仮定を `y` に適用する。

### 8. `φ` または `φ⁻¹` を掛け戻して元の unit を回収する

最後に `hrec` を二分岐する。

```lean
rcases hrec with hrec | hrec
```

`x=yφ` なら

```lean
rw [hrec]
exact goldenUnitFifthClass_mul_phi hyClass
```

`x=yφ⁻¹` なら

```lean
rw [hrec]
exact goldenUnitFifthClass_mul_phiInv hyClass
```

で終了する。

数学的には「より小さい unit が five-sector 表示を持つなら、1 ステップの generator multiplication 後も five-sector 表示を持つ」という閉性を使って descent を逆向きに戻している。

## Lean 固有の処理

### `generalize ... = n`

measure 式を帰納変数へ変換するための Lean 上の管理である。数学では単に $n=m(x)$ と置く操作に対応する。

### `generalizing x`

この指定が無いと帰納仮定が最初の `x` に固定され、降下で得られる別の `y` に適用しにくい。

strong induction と dependent context を接続する重要な Lean 技法である。

### `omega`

この theorem では代数的な黄金整数計算ではなく、自然数 measure の順序関係の整理に使われる。

主な用途は

- `0<n` から `1≤n`
- `n=1` branch の measure 書換え
- `1<n` を descent の前提へ渡す
- `hylt` と `hm` から `measure y<n`

である。

### `simpa [h] using ...`

基底ケースでは、classification theorem が返す具体 equality `h` で `x` を置き換え、対応する private theorem の型と現在の goal を一致させる。

### `rfl` を measure equality として渡す

帰納仮定へ `y` を適用するとき、measure の一般化式として

```lean
rfl
```

を渡している。ここでは `goldenUnitMeasure y = goldenUnitMeasure y` という反射律で十分である。

## 冗長・重複箇所

証明本体は比較的短く、構造も明確である。

ただし基底ケースには

```lean
simpa [h] using goldenUnitFifthClass_one
simpa [h] using goldenUnitFifthClass_neg_one
simpa [h] using goldenUnitFifthClass_phi
simpa [h] using goldenUnitFifthClass_neg_phi
```

という四つのほぼ同型な行がある。

これは前段の `goldenUnit_measure_one_cases` 自体が四分岐を返す設計によるもので、局所的には重複している。

一方、この明示性によって「どの終端 unit がどの fifth-class witness で閉じるか」が非常に読みやすく、展示用コードとしては合理的である。

また descent の二分岐も

```lean
goldenUnitFifthClass_mul_phi
goldenUnitFifthClass_mul_phiInv
```

という対称形である。

## 最適化候補

### 1. measure-one classification と fifth-class classification の統合

`goldenUnit_measure_one_cases` が単なる equality classification ではなく、直接

```lean
goldenUnitMeasure x = 1 → GoldenUnitFifthClass x
```

を返す補題になれば、この theorem の四分岐は一行に圧縮できる。

ただし現在の equality classification は他用途にも再利用できるため、分離設計には利点がある。

### 2. descent の再構築を閉性 lemma に抽象化

概念的に

```lean
GoldenUnitFifthClass y →
(x = y * φ ∨ x = y * φ⁻¹) →
GoldenUnitFifthClass x
```

という補助 lemma を置けば最後の二分岐を局所的に隠せる。

ただし theorem の数学的流れは現状の方が露出しており、教育・展示には適している。

### 3. `omega` 依存の局所削減

順序関係は単純なので、`Nat.succ_le_iff`、rewrite、`exact` で一部を明示化できる可能性がある。ただしコード量は増える可能性が高い。

### 4. unit group の抽象構造による別証明

黄金整数環の unit 群が $\{\pm\varphi^k\}$ 型であることを既成の抽象群論として使えるなら、指数を mod 5 に落とすだけでより短い証明が得られる可能性がある。

しかし本開発の価値は coordinate descent により必要な分類を内部で証明している点にあるため、単純な短縮が必ずしも設計上の改善とは限らない。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

この theorem が直接利用する Mathlib 側の主要機能は概ね次である。

- `Nat.strong_induction_on`
- 自然数順序補題
- `omega` tactic
- `rcases` / `obtain` / `simpa` / `rw` など Lean / Mathlib の標準 tactic infrastructure

黄金整数、unit measure、descent、fifth-class 関係の宣言は開発内の既存定義・補題である。

import 縮小候補としては `Mathlib` 全体ではなく、自然数 strong induction、Presburger arithmetic の `omega`、および本開発の GoldenInt 関連 module に限定できる可能性が高い。

ただし今回は Lean ビルドを行わない条件なので、厳密な最小 import 集合は未確認であり、候補としてのみ記す。

## Comparator challenge 化の可否

**可能。中規模で非常に良い challenge 候補である。**

この theorem は単なる `ring` や `decide` の micro challenge と異なり、証明設計そのものを比較できる。

challenge としては以下を前提 API として与えるとよい。

```lean
GoldenUnitFifthClass
goldenUnitMeasure
goldenUnitMeasure_pos
goldenUnit_measure_one_cases
goldenUnit_descent
goldenUnitFifthClass_one
goldenUnitFifthClass_neg_one
goldenUnitFifthClass_phi
goldenUnitFifthClass_neg_phi
goldenUnitFifthClass_mul_phi
goldenUnitFifthClass_mul_phiInv
```

そして goal を

```lean
theorem challenge (x : GoldenInt) (hx : GoldenUnit x) :
  GoldenUnitFifthClass x
```

とする。

比較点は

- strong induction を選べるか
- measure を適切に一般化できるか
- `generalizing x` の必要性を理解できるか
- strict descent の `hylt` を帰納仮定へ接続できるか
- measure-one 四基底を正しく処理できるか
- `φ` / `φ⁻¹` の再構築を finite class closure へ結びつけられるか

である。

単純な tactic 探索より、帰納法の設計能力を評価する Comparator 向けの良い題材である。

## 技術的意味

この theorem の核心は **無限 unit 群を有限五 class へ圧縮する操作を strict descent で機械検証したこと** にある。

unit 自体は `φ` や `φ⁻¹` の反復によって無限に存在し得る。しかし fifth powers を法とすると、指数は 5 周期でしか区別する必要がない。

証明はこの直観を「unit 群の既知分類を引用する」のではなく、

$$
\text{measure decrease}
\;\Longrightarrow\;
\text{finite base cases}
\;\Longrightarrow\;
\text{sector transport}
$$

として実装している。

すなわち `goldenUnit_descent` が無限性を自然数の well-foundedness に押し込み、`goldenUnitFifthClass_mul_phi` と `goldenUnitFifthClass_mul_phiInv` が descent の逆向き再構築でも class が保存されることを保証する。

これにより「任意の unit」という無限対象が、後続の FLT5 sector arithmetic では

$$
0,1,2,3,4
$$

の有限五分岐だけで扱えるようになる。

FLT5 全体においては、代数的 factorization から得られる任意の unit `epsilon` を finite sector に落とすための決定的な橋である。

## 次に読むべき宣言

次は

```lean
/-- Every golden unit has a representative among five classes modulo fifth powers. -/
theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth := by
  intro epsilon hepsilon
  exact goldenUnitFifthClass_of_unit epsilon hepsilon
```

である。

今回の theorem を公開 contract `GoldenUnitClassesModFifth` の形へ包み直す短い bridge theorem であり、そこから `signedGoldenFiniteUnitSectorCore_of_unitClasses` が任意の stripped packet を五つの algebraic unit sector へ有限化する。