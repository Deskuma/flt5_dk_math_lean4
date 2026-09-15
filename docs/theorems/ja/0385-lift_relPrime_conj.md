# 0385 `lift_relPrime_conj`

## 宣言種別

`theorem`

`GoldenZeroSectorDescentPacket` namespace 内で、quadratic re-entry element `goldenZeroSectorLift p.base` とその共役 `goldenConj (goldenZeroSectorLift p.base)` が `GoldenRelPrime` であることを示す。

## Lean コード

```lean
/-- The re-entry element and its conjugate have no nonunit common divisor. -/
theorem lift_relPrime_conj (p : GoldenZeroSectorDescentPacket) :
    GoldenRelPrime (goldenZeroSectorLift p.base)
      (goldenConj (goldenZeroSectorLift p.base)) := by
  intro z hzAlpha hzConj
  have hzDiff : GoldenDivides z
      (goldenZeroSectorLift p.base -
        goldenConj (goldenZeroSectorLift p.base)) :=
    goldenDivides_sub hzAlpha hzConj
  have hzNormAlpha : goldenNorm z ∣
      goldenNorm (goldenZeroSectorLift p.base) :=
    goldenNorm_dvd_of_goldenDivides hzAlpha
  have hzNormDiff : goldenNorm z ∣
      goldenNorm (goldenZeroSectorLift p.base -
        goldenConj (goldenZeroSectorLift p.base)) :=
    goldenNorm_dvd_of_goldenDivides hzDiff
  have hzD : (goldenNorm z).natAbs ∣ p.D ^ 5 := by
    apply Int.dvd_natCast.mp
    simpa [goldenZeroSectorLift_norm, p.H_eq] using hzNormAlpha
  have hzS : (goldenNorm z).natAbs ∣
      5 * p.base.snd.natAbs ^ 4 := by
    apply Int.dvd_natCast.mp
    have hpos : goldenNorm z ∣ (5 : ℤ) * p.base.snd ^ 4 := by
      apply Int.dvd_neg.mp
      convert hzNormDiff using 1
      rw [goldenNorm_sub_conj, goldenZeroSectorLift_snd]
      ring
    have habspow : abs p.base.snd ^ 4 = p.base.snd ^ 4 := by
      rw [← abs_pow]
      exact abs_of_nonneg (by positivity)
    simpa [Int.natCast_natAbs, habspow] using hpos
  have hD5 : Nat.Coprime (p.D ^ 5) 5 :=
    Nat.Coprime.pow_left 5
      ((show Nat.Prime 5 by norm_num).coprime_iff_not_dvd.mpr
        p.five_not_dvd_D).symm
  have hDS : Nat.Coprime (p.D ^ 5) (p.base.snd.natAbs ^ 4) :=
    (Nat.Coprime.pow_left 5 p.coprime_D_s).pow_right 4
  have hcop : Nat.Coprime (p.D ^ 5)
      (5 * p.base.snd.natAbs ^ 4) := hD5.mul_right hDS
  have hone : (goldenNorm z).natAbs = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hzD hzS
  apply goldenUnit_of_norm_eq_one_or_neg_one
  omega
```

## Lean の型

namespace を展開した概念的な型は

```lean
GoldenZeroSectorDescentPacket.lift_relPrime_conj :
  (p : GoldenZeroSectorDescentPacket) →
    GoldenRelPrime
      (goldenZeroSectorLift p.base)
      (goldenConj (goldenZeroSectorLift p.base))
```

である。

`GoldenRelPrime alpha beta` は、この証明の `intro z hzAlpha hzConj` から分かる通り、`alpha` と `beta` の双方を割る任意の黄金整数 `z` が unit であることを要求する相対素性 predicate である。

## 数学的主張

`p.base = (r,s)` とし、

$$
\alpha = T(r,s)=\operatorname{goldenZeroSectorLift}(r,s)
$$

と置く。今回示すのは

$$
\gcd_{\mathbb Z[\varphi]}(\alpha,\overline\alpha)=1
$$

に対応する statement である。ここで「1」は通常の整数 gcd そのものではなく、黄金整数環において共通因子が unit しか存在しないという意味である。

共通因子 `z` が存在すると仮定する。norm の可除性から

$$
|N(z)| \mid |N(\alpha)|.
$$

0380--0384 までに整備した packet invariant と

$$
N(\alpha)=H(r,s)=D^5
$$

を使うと

$$
|N(z)|\mid D^5.
$$

一方 `z` は `alpha` と `conj alpha` の双方を割るので差

$$
\alpha-\overline\alpha
$$

も割る。quadratic lift の第二座標は `s^2` であり、`goldenNorm_sub_conj` によってこの差の norm は符号を除けば

$$
5s^4
$$

となるため、

$$
|N(z)|\mid 5|s|^4
$$

も得る。

0382 `five_not_dvd_D` と 0384 `coprime_D_s` により

$$
\gcd(D^5,5|s|^4)=1.
$$

したがって両方を割る自然数 `|N(z)|` は

$$
|N(z)|=1
$$

しかあり得ない。よって

$$
N(z)=\pm1,
$$

したがって `z` は黄金整数環の unit である。

## 証明全体での役割

これは zero-sector descent における重要な環論 bridge である。

0382--0384 までは主に自然数上の情報

$$
5\nmid D,
\qquad
\gcd(D,|s|)=1
$$

を準備していた。今回その情報を、黄金整数環上の

$$
\operatorname{GoldenRelPrime}(T(r,s),\overline{T(r,s)})
$$

へ持ち上げる。

この相対素性は後続 `exists_lift_eq_fifthPower` が `goldenCoprimeFactorOfFifthPower` を適用するための直接の入力である。すでに 0375 `goldenZeroSectorLift_mul_conj` により

$$
T(r,s)\overline{T(r,s)}=D^5
$$

型の fifth-power product が得られているため、今回の相対素性が揃うことで

$$
T(r,s)=\varepsilon\gamma^5
$$

という「unit × fifth power」分解へ進める。

したがって 0385 は、算術的 coprimality preparation を黄金整数環の fifth-power factorization machinery に接続する境界 theorem である。

## 直接依存する定義・補題

プロジェクト内で直接使われる主な宣言は次である。

- `GoldenZeroSectorDescentPacket`
- `GoldenRelPrime`
- `GoldenDivides`
- `goldenZeroSectorLift`
- `goldenConj`
- `goldenDivides_sub`
- `goldenNorm`
- `goldenNorm_dvd_of_goldenDivides`
- `goldenZeroSectorLift_norm`
- `GoldenZeroSectorDescentPacket.H_eq`
- `goldenNorm_sub_conj`
- `goldenZeroSectorLift_snd`
- `GoldenZeroSectorDescentPacket.five_not_dvd_D`
- `GoldenZeroSectorDescentPacket.coprime_D_s`
- `goldenUnit_of_norm_eq_one_or_neg_one`

Mathlib 側で直接見える主な API は次である。

- `Int.dvd_natCast.mp`
- `Int.dvd_neg.mp`
- `Int.natCast_natAbs`
- `Nat.Prime.coprime_iff_not_dvd`
- `Nat.Coprime.pow_left`
- `Nat.Coprime.pow_right`
- `Nat.Coprime.mul_right`
- `Nat.eq_one_of_dvd_coprimes`
- `abs_pow`
- `abs_of_nonneg`
- `norm_num`
- `positivity`
- `ring`
- `omega`

## 証明・構築の流れ

1. `GoldenRelPrime` の定義に従い、共通因子 `z` と二つの可除性仮定を導入する。

   ```lean
   intro z hzAlpha hzConj
   ```

2. 共通因子は差も割る。

   ```lean
   have hzDiff := goldenDivides_sub hzAlpha hzConj
   ```

3. `GoldenDivides` を norm の整数可除性へ写す。

   ```lean
   have hzNormAlpha := goldenNorm_dvd_of_goldenDivides hzAlpha
   have hzNormDiff := goldenNorm_dvd_of_goldenDivides hzDiff
   ```

4. `N(alpha)=H(r,s)=D^5` を使って

   ```lean
   hzD : (goldenNorm z).natAbs ∣ p.D ^ 5
   ```

   を作る。

5. 差 `alpha - conj alpha` の norm を計算し、

   ```lean
   hzS : (goldenNorm z).natAbs ∣ 5 * p.base.snd.natAbs ^ 4
   ```

   を得る。

6. 0382 から

   ```lean
   hD5 : Nat.Coprime (p.D ^ 5) 5
   ```

   を作る。

7. 0384 から

   ```lean
   hDS : Nat.Coprime (p.D ^ 5) (p.base.snd.natAbs ^ 4)
   ```

   を作る。

8. 二つを `mul_right` で合成して

   ```lean
   hcop : Nat.Coprime (p.D ^ 5)
     (5 * p.base.snd.natAbs ^ 4)
   ```

   を得る。

9. `|N(z)|` が互いに素な二数の双方を割るので

   ```lean
   have hone : (goldenNorm z).natAbs = 1 :=
     Nat.eq_one_of_dvd_coprimes hcop hzD hzS
   ```

   と確定する。

10. `natAbs = 1` から `N(z)=±1` を `omega` で処理し、`goldenUnit_of_norm_eq_one_or_neg_one` によって `z` が unit であることを結論する。

## Lean 固有の処理

### `GoldenRelPrime` を predicate として直接展開する証明形

証明冒頭が

```lean
intro z hzAlpha hzConj
```

で始まる。つまり theorem は gcd object を構成するのではなく、任意の共通 divisor が unit であることを示す predicate style である。

### `GoldenDivides` から整数 norm 可除性への降下

`goldenNorm_dvd_of_goldenDivides` により、黄金整数環内の divisibility を `ℤ` の divisibility へ移す。ここが抽象環から通常算術へ降りる主要な型境界である。

### `Int.dvd_natCast.mp`

norm の可除性は整数上だが、最終的な coprimality argument は `Nat.Coprime` 上で行われる。そのため `natAbs` と natural cast を介して自然数 divisibility へ変換している。

### `convert ... using 1` と `ring`

差の norm から `5*s^4` を取り出す部分では、式が definitional equality では一致しないため

```lean
convert hzNormDiff using 1
rw [goldenNorm_sub_conj, goldenZeroSectorLift_snd]
ring
```

として代数的正規化を行っている。

### 絶対値と偶数冪

```lean
have habspow : abs p.base.snd ^ 4 = p.base.snd ^ 4 := by
  rw [← abs_pow]
  exact abs_of_nonneg (by positivity)
```

は、`s^4 ≥ 0` なので絶対値を除去できることを Lean に明示する処理である。

### coprimality の power transport

`Nat.Coprime.pow_left`, `.pow_right`, `.mul_right` により

$$
\gcd(D,|s|)=1
$$

と

$$
5\nmid D
$$

から、必要な

$$
\gcd(D^5,5|s|^4)=1
$$

を API 合成だけで構築している。

## 冗長・重複箇所

証明は長いが、数学的には「共通因子の norm が二つの互いに素な自然数を割るので 1」という一本の筋であり、各 `have` はその型変換を明示している。

冗長候補としては `hzD` と `hzS` の二つの `Int.dvd_natCast.mp` 周辺が挙げられる。golden norm divisibility を自然数 `natAbs` divisibility へ移す helper が複数箇所で必要なら、例えば

```lean
lemma natAbs_goldenNorm_dvd_of_goldenDivides ...
```

のような API に切り出す余地がある。

また `hD5`, `hDS`, `hcop` は packet の後続でも再利用されるなら packet-level lemma にまとめられる。しかし今回だけなら、局所 `have` の方が依存を露出せず読みやすい。

## 最適化候補

1. **norm divisibility の Nat 化を helper にする**

   `GoldenDivides → goldenNorm divisibility → natAbs divisibility` が他でも反復されるなら有効である。

2. **差の norm の専用補題を検討する**

   今回は

   ```lean
   goldenNorm_sub_conj
   goldenZeroSectorLift_snd
   ring
   ```

   を組み合わせている。zero-sector lift 専用に

   ```lean
   goldenNorm_lift_sub_conj :
     goldenNorm (T x - conj (T x)) = -(5 * x.snd ^ 4)
   ```

   相当を持てば本体は短くなる。ただし用途が単発なら現状の方が API 汚染が少ない。

3. **最終 unit 化は現状が適切**

   `natAbs N(z)=1` から `N(z)=±1` を直接 algebraic case split するより、`omega` と既存 `goldenUnit_of_norm_eq_one_or_neg_one` を使う方が短い。

4. **0382・0384 の packet API を維持する**

   `five_not_dvd_D` と `coprime_D_s` を theorem 内で再証明せず利用しているため、証明の階層化は良好である。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

今回の theorem が表面上必要とする Mathlib 機能は、整数・自然数の divisibility/coprimality、prime API、絶対値、power、`ring`, `norm_num`, `positivity`, `omega` である。

より狭い import へ分割できる可能性は高いが、この実行では Lean ビルドを行わないため、厳密な最小 Mathlib module 集合は確認していない。したがって最小 import 名を断定しない。

プロジェクト側では少なくとも `GoldenDivisibility` 系 API、golden norm/conjugation API、`SignedGoldenZeroSectorDescent` 内の packet と quadratic lift、0382・0384 が可視である必要がある。standalone manifest 上ではこれらの前段 module が順序付きで統合されている。

## Comparator challenge 化の可否

**非常に適している。**

0385 は単純な一行 API 適用ではなく、複数の表現層を横断するため、Comparator でかなり良い中規模 challenge になる。

評価点は次である。

- `GoldenRelPrime` の goal から任意の共通 divisor を導入できるか
- 共通 divisor が差も割ることを発見できるか
- `GoldenDivides` を norm divisibility へ落とせるか
- `H_eq` から `D^5` divisibility を構成できるか
- conjugate difference の norm を `5*s^4` へ正規化できるか
- `five_not_dvd_D` と `coprime_D_s` を power coprimality へ持ち上げられるか
- `Nat.eq_one_of_dvd_coprimes` を選択できるか
- norm `±1` から unit を閉じられるか

特に「黄金整数環 → 整数 norm → 自然数 coprimality → 黄金整数 unit」という往復があるため、単なる tactic benchmark よりも theorem/API selection benchmark として価値が高い。

challenge を小さくする場合は `hzD`, `hzS`, `hcop` を前提として与え、`Nat.eq_one_of_dvd_coprimes` から unit 化する終盤だけを測ることもできる。完全版の方が本 theorem の設計力をよく測れる。

## 次に読むべき宣言

次は `five_dvd_norm_of_nonzero_goldenUnitSector`、種別は `theorem` である。

```lean
theorem five_dvd_norm_of_nonzero_goldenUnitSector
    {alpha gamma : GoldenInt} {i : Fin 5}
    (hi : i ≠ 0)
    (hAlpha : alpha =
      goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5))
    (hFive : (5 : ℤ) ∣ alpha.snd) :
    (5 : ℤ) ∣ goldenNorm gamma := by
  ...
```

これは namespace `GoldenZeroSectorDescentPacket` を一度抜けた packet-independent theorem である。

0385 が re-entry element と共役の相対素性を確立したので、後続 `exists_lift_eq_fifthPower` は coprime fifth-power factorization により

$$
T(r,s)=\varphi^i\theta^5
$$

型の unit sector 表現へ進む。そこで `i≠0` の非零 sector なら、第二座標が 5 で割れることから

$$
5\mid N(\theta)
$$

を導くのが次 theorem の役割である。最終的に packet の `five_not_dvd_H` と衝突させて非零 unit sector を排除する準備になる。