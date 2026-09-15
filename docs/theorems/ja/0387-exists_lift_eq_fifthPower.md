# 0387 `GoldenZeroSectorDescentPacket.exists_lift_eq_fifthPower`

## 宣言種別

`theorem`

`GoldenZeroSectorDescentPacket` namespace 内に置かれた、zero-sector infinite descent の re-entry を **純粋な第五冪** へ確定する中核定理である。

## Lean コード

```lean
/-- The re-entry element is an honest fifth power; all nonzero unit sectors die mod five. -/
theorem exists_lift_eq_fifthPower (p : GoldenZeroSectorDescentPacket) :
    ∃ gamma : GoldenInt,
      goldenZeroSectorLift p.base = goldenPow gamma 5 ∧
      goldenNorm gamma = (p.D : ℤ) := by
  have hmul :
      goldenMul (goldenZeroSectorLift p.base)
          (goldenConj (goldenZeroSectorLift p.base)) =
        goldenPow (goldenOfInt (p.D : ℤ)) 5 := by
    calc
      goldenMul (goldenZeroSectorLift p.base)
          (goldenConj (goldenZeroSectorLift p.base)) =
          goldenOfInt (goldenFifthSndFactor p.base.fst p.base.snd) :=
        goldenZeroSectorLift_mul_conj p.base
      _ = goldenOfInt ((p.D : ℤ) ^ 5) := by rw [p.H_eq]
      _ = goldenPow (goldenOfInt (p.D : ℤ)) 5 :=
        goldenOfInt_pow_five (p.D : ℤ)
  obtain ⟨epsilon, gamma, hepsilon, hfactor⟩ :=
    goldenCoprimeFactorOfFifthPower
      (goldenZeroSectorLift p.base)
      (goldenConj (goldenZeroSectorLift p.base))
      (goldenOfInt (p.D : ℤ)) p.lift_relPrime_conj hmul
  obtain ⟨i, delta, hdelta⟩ :=
    goldenUnitClassesModFifth epsilon hepsilon
  let theta := goldenMul delta gamma
  have hSector : goldenZeroSectorLift p.base =
      goldenMul (goldenPow goldenPhi i.val) (goldenPow theta 5) := by
    rw [hfactor, hdelta]
    simp only [theta, golden_mul_eq, golden_pow_eq, mul_pow]
    ring
  have hFiveAlpha : (5 : ℤ) ∣ (goldenZeroSectorLift p.base).snd := by
    rw [goldenZeroSectorLift_snd]
    rcases p.snd_eq with hs | hs
    · exact dvd_pow (by rw [hs]; exact dvd_mul_right 5 _)
        (by decide : 2 ≠ 0)
    · exact dvd_pow (by rw [hs]; exact dvd_neg.mpr (dvd_mul_right 5 _))
        (by decide : 2 ≠ 0)
  have hThetaNorm : ¬ (5 : ℤ) ∣ goldenNorm theta := by
    intro h5theta
    apply p.five_not_dvd_H
    rw [← goldenZeroSectorLift_norm p.base, hSector, goldenNorm_mul]
    apply dvd_mul_of_dvd_right
    change (5 : ℤ) ∣ goldenNorm (theta ^ 5)
    rw [goldenNorm_pow]
    exact dvd_pow h5theta (by decide : 5 ≠ 0)
  have hi : i = 0 := by
    by_contra hi
    exact hThetaNorm
      (five_dvd_norm_of_nonzero_goldenUnitSector hi hSector hFiveAlpha)
  subst i
  have hroot : goldenZeroSectorLift p.base = goldenPow theta 5 := by
    simpa [goldenPhi_pow_zero, golden_mul_eq] using hSector
  refine ⟨theta, hroot, ?_⟩
  have hn := congrArg goldenNorm hroot
  rw [goldenZeroSectorLift_norm, p.H_eq, golden_pow_eq,
    goldenNorm_pow] at hn
  exact (show Odd 5 by decide).pow_injective hn.symm
```

## Lean の型

概念的には次の型である。

```lean
GoldenZeroSectorDescentPacket.exists_lift_eq_fifthPower :
  (p : GoldenZeroSectorDescentPacket) →
  ∃ gamma : GoldenInt,
    goldenZeroSectorLift p.base = goldenPow gamma 5 ∧
    goldenNorm gamma = (p.D : ℤ)
```

入力は descent packet `p` 一つだけで、出力として黄金整数 `gamma` を構成し、同時に二つの性質を保証する。

1. quadratic re-entry element は `gamma` の第五冪そのものである。
2. `gamma` の golden norm は packet の自然数パラメータ `D` に一致する。

したがって単なる「unit を掛けた第五冪」ではなく、unit sector を完全に除去した **honest fifth power** を返す。

## 数学的主張

`p.base=(r,s)` とし、quadratic re-entry element を

$$
\alpha=T(r,s)=\operatorname{goldenZeroSectorLift}(r,s)
$$

と書く。

packet invariant には

$$
H(r,s)=D^5
$$

が含まれ、lift の norm identity により

$$
N(\alpha)=H(r,s)=D^5
$$

である。さらに共役との積は

$$
\alpha\overline{\alpha}=D^5
$$

に対応する。

0385 `lift_relPrime_conj` により `alpha` と `conj alpha` は黄金整数環で相対素なので、既存の fifth-power factorization により

$$
\alpha=\varepsilon\gamma^5
$$

と書ける。ここで `epsilon` は golden unit である。

unit classification modulo fifth powers を使うと、別の unit fifth power を `gamma` 側へ吸収して

$$
\alpha=\varphi^i\theta^5,
\qquad i\in\operatorname{Fin}5
$$

と正規化できる。

一方、lift の第二座標は

$$
\alpha_{\mathrm{snd}}=s^2
$$

であり、packet の

$$
s=\pm 5t^5
$$

から

$$
5\mid \alpha_{\mathrm{snd}}
$$

が従う。

もし `i ≠ 0` なら 0386 `five_dvd_norm_of_nonzero_goldenUnitSector` により

$$
5\mid N(\theta)
$$

となる。しかし `theta^5` は `alpha` の factor であり、その norm が 5 で割れるなら `H(r,s)` も 5 で割れてしまい、packet の 0381 `five_not_dvd_H` と矛盾する。

したがって

$$
i=0
$$

であり、

$$
\alpha=\theta^5
$$

が得られる。

最後に norm を取ると

$$
D^5=N(\alpha)=N(\theta)^5.
$$

指数 5 は奇数なので整数上で第五冪写像は単射であり、

$$
N(\theta)=D
$$

を得る。

## 証明全体での役割

この theorem は zero-sector descent における重要な **橋** である。

それ以前では packet から得られる情報は、

- lift とその共役が相対素
- lift の norm が第五冪
- unit classes modulo fifth powers は 5 sector に分類できる
- 非零 sector は 5-adic 条件と衝突する

という部品に分かれている。

0387 はこれらを一つに束ね、

$$
T(r,s)=\gamma^5
$$

という再帰可能な形を初めて確定する。

この形が得られることで、次の `fifthRoot_snd_factor_eq` は第五冪 `gamma^5` の第二座標を比較し、

$$
s^2
 = 5\,\gamma_{\mathrm{snd}}\,
   H(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}})
$$

という新しい積分解を取り出せる。そこから positivity、coprimality、power splitting、measure decrease が続き、最終的に strict descent packet が構成される。

したがって 0387 は、unit ambiguity を消して infinite descent を再始動可能にする theorem である。

## 直接依存する定義・補題

主な直接依存は次の通りである。

- `GoldenZeroSectorDescentPacket`
- `goldenZeroSectorLift`
- `goldenZeroSectorLift_mul_conj`
- `goldenZeroSectorLift_norm`
- `goldenConj`
- `goldenMul`
- `goldenPow`
- `goldenOfInt`
- `goldenOfInt_pow_five`
- `GoldenZeroSectorDescentPacket.H_eq`
- `GoldenZeroSectorDescentPacket.snd_eq`
- `GoldenZeroSectorDescentPacket.lift_relPrime_conj`
- `GoldenZeroSectorDescentPacket.five_not_dvd_H`
- `goldenCoprimeFactorOfFifthPower`
- `goldenUnitClassesModFifth`
- `goldenPhi`
- `goldenPhi_pow_zero`
- `goldenNorm_mul`
- `goldenNorm_pow`
- `five_dvd_norm_of_nonzero_goldenUnitSector`

Mathlib 側では少なくとも次の機能が証明本文に現れる。

- existential / tuple destructuring (`obtain`)
- `rw`
- `simp only` / `simpa`
- `ring`
- `dvd_pow`
- `dvd_neg.mpr`
- `dvd_mul_right`
- `dvd_mul_of_dvd_right`
- `congrArg`
- `Odd.pow_injective`
- `decide`

## 証明・構築の流れ

1. `hmul` で lift とその共役の積を第五冪として表す。

   `goldenZeroSectorLift_mul_conj` と `p.H_eq` をつなぎ、

   $$
   \alpha\overline\alpha=(D)^5
   $$

   を黄金整数の演算として作る。

2. `goldenCoprimeFactorOfFifthPower` を適用する。

   0385 の `p.lift_relPrime_conj` と `hmul` により、

   ```lean
   obtain ⟨epsilon, gamma, hepsilon, hfactor⟩ := ...
   ```

   として unit `epsilon`、第五冪底 `gamma`、unit 性、factorization を得る。

3. `goldenUnitClassesModFifth` で `epsilon` を 5 個の unit sector に分類する。

   $$
   \varepsilon=\varphi^i\delta^5.
   $$

4. `theta := delta * gamma` と定義し、二つの第五冪をまとめる。

   `hSector` で

   $$
   \alpha=\varphi^i\theta^5
   $$

   を得る。Lean では `simp only` と `ring` を使い、黄金整数の座標演算まで展開して正規化している。

5. `hFiveAlpha` で lift の第二座標が 5 で割れることを示す。

   `goldenZeroSectorLift_snd` により第二座標は `s^2`。`p.snd_eq` の正負二枝のどちらでも `5 ∣ s` なので `5 ∣ s^2` となる。

6. `hThetaNorm` で `5 ∤ N(theta)` を示す。

   仮に `5 ∣ N(theta)` とすると、`hSector` と norm multiplicativity から `5 ∣ N(alpha)`、すなわち `5 ∣ H(r,s)` が従い、`p.five_not_dvd_H` に反する。

7. unit-sector index が 0 であることを証明する。

   `i ≠ 0` を仮定すると 0386 により `5 ∣ N(theta)` が得られ、直前の `hThetaNorm` と矛盾する。

8. `subst i` して zero sector に固定し、`goldenPhi^0=1` を簡約して

   $$
   \alpha=\theta^5
   $$

   を得る。

9. 両辺に `goldenNorm` を適用する。

   packet invariant `H=D^5` と norm-of-power identity により

   $$
   D^5=N(\theta)^5
   $$

   を得る。

10. `Odd.pow_injective` を指数 5 に適用して

   $$
   N(\theta)=D
   $$

   を確定し、`theta` を witness として返す。

## Lean 固有の処理

### `obtain` による構造的分解

factorization theorem と unit classification theorem は複数の witness と証明を返すため、

```lean
obtain ⟨epsilon, gamma, hepsilon, hfactor⟩ := ...
obtain ⟨i, delta, hdelta⟩ := ...
```

で existential data を一度に展開している。

### `let theta := ...`

unit fifth-power 部分 `delta^5` を既存の `gamma^5` に吸収するため、新しい底

```lean
let theta := goldenMul delta gamma
```

を導入している。数学的な

$$
\delta^5\gamma^5=(\delta\gamma)^5
$$

を Lean で扱いやすい形へ固定する役割がある。

### `simp only [...]` と `ring`

`GoldenInt` の積・冪が抽象演算のままでは ring normalizer が直接処理しにくいため、

```lean
simp only [theta, golden_mul_eq, golden_pow_eq, mul_pow]
ring
```

で座標レベルの可換環式へ落としている。

### 符号付き `snd_eq` の処理

packet の第二座標は `+5t^5` と `-5t^5` の二枝を許す。可除性だけが必要なので、負枝では

```lean
dvd_neg.mpr
```

を使い、符号を消してから `dvd_pow` で平方へ上げる。

### `change` による表現合わせ

`hThetaNorm` では `theta` の Lean 表現と `goldenPow theta 5` の表現を合わせるため、

```lean
change (5 : ℤ) ∣ goldenNorm (theta ^ 5)
```

を使う。この箇所は `goldenPow` と通常の `^` の bridge が simplification によって見えているため成立している。

### `congrArg goldenNorm`

構造体等式 `hroot` から norm 等式だけを抽出するため、

```lean
have hn := congrArg goldenNorm hroot
```

と関数合同性を使う。以後は整数の第五冪等式へ完全に降りる。

### `Odd.pow_injective`

整数では偶数冪は符号を失うため一般には injective でない。指数 5 が奇数であることを

```lean
(show Odd 5 by decide)
```

で供給し、第五冪の単射性を正しく使っている。

## 冗長・重複箇所

`hFiveAlpha` の `p.snd_eq` 二枝は、符号が違うだけで同じ可除性を示している。`snd` 自身について既に

$$
5\mid s
$$

という packet API があれば、この case split は不要になる。

また `hThetaNorm` は「factorization の fifth-power 側の norm が 5 で割れるなら lift norm も 5 で割れる」という一般的な伝播であり、別 helper として独立させる余地がある。

一方 `hSector` の explicit `ring` は algebraic normalization の監査性が高く、museum 文脈では必ずしも冗長ではない。

## 最適化候補

1. **`five_dvd_lift_snd` helper**

   packet から直接

   ```lean
   (5 : ℤ) ∣ (goldenZeroSectorLift p.base).snd
   ```

   を返す補題を用意すれば、`exists_lift_eq_fifthPower` の中心論理から符号処理を分離できる。

2. **unit absorption lemma**

   `epsilon = phi^i * delta^5` と `alpha = epsilon * gamma^5` から

   ```lean
   alpha = phi^i * (delta * gamma)^5
   ```

   を返す一般 lemma を作れば、`simp only ...; ring` を隠蔽できる。

3. **sector exclusion theorem の統合**

   0386 と `hThetaNorm` の組を、packet 用の

   ```lean
   i = 0
   ```

   を直接返す theorem にまとめることもできる。ただし 0386 の packet-independent 性は再利用性が高いため、現在の分離も設計上よい。

4. **norm root extraction helper**

   `D^5 = N(theta)^5` から `N(theta)=D` を取り出す末尾は一般的なので、odd-power injectivity を包む小補題にできる。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用している。

今回の theorem 自体で直接必要となる Mathlib 機能は、可除性 API、`ring`、simplifier、整数の冪、`Odd.pow_injective`、有限的な decidability などである。プロジェクト固有の主要定理は同じ standalone 内の先行モジュール由来である。

import 最適化としては `Mathlib` 全体ではなく、実際に必要な algebra/divisibility/tactic 系モジュールへ縮小できる可能性がある。ただし本タスクでは Lean build を実行しないため、 **最小 import 集合は未検証** である。したがって具体的な最小 import 名を断定しない。

## Comparator challenge 化の可否

**可。しかも難度の異なる複数の challenge に分割しやすい。**

最も価値が高いのは次の三段階である。

1. `hmul` を構築し、相対素 factorization から `alpha = epsilon * gamma^5` を得る API-selection challenge。
2. unit classification と 0386 を使って `i = 0` を導く sector-exclusion challenge。
3. `congrArg goldenNorm` と odd-power injectivity から `N(theta)=D` を得る algebraic finishing challenge。

特に 2 は、複数の既存補題を正しい方向で接続する必要があり、単なる `ring` 問題ではないため Comparator 向きである。

一方、完全 theorem を単独 challenge にすると依存 API が多く、環境依存性が高い。challenge 化するなら先行宣言を固定した小型環境に切り出すのが望ましい。

## 次に読むべき宣言

次は

```lean
theorem fifthRoot_snd_factor_eq
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5) :
    p.base.snd ^ 2 =
      5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd := by
  have h := congrArg (fun x : GoldenInt => x.snd) hroot
  change (goldenZeroSectorLift p.base).snd =
    (goldenPow gamma 5).snd at h
  rw [goldenZeroSectorLift_snd, goldenPow_five_snd,
    goldenFifthSndPoly_eq] at h
  exact h
```

である。

0387 が re-entry element を

$$
T(r,s)=\gamma^5
$$

と確定したので、次はその **第二座標だけを射影** し、

$$
s^2
 = 5\,\gamma_{\mathrm{snd}}\,
   H(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}})
$$

という新しい product identity を得る。この等式が後続の positivity、coprimality、fifth-power splitting、strict measure decrease の入口となる。