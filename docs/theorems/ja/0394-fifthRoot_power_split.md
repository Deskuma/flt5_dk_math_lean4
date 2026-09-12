# 0394 `GoldenZeroSectorDescentPacket.fifthRoot_power_split`

## 宣言種別

`theorem`

`GoldenZeroSectorDescentPacket` namespace 内で、第五根 `gamma : GoldenInt` の第二座標と quartic factor を再び第五冪へ分離し、zero-sector descent の再帰形を回収する補題である。

## Lean コード

```lean
theorem fifthRoot_power_split
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5)
    (hnorm : goldenNorm gamma = (p.D : ℤ)) :
    ∃ u v : ℕ,
      0 < u ∧ 0 < v ∧
      gamma.snd = 5 * (u : ℤ) ^ 5 ∧
      goldenFifthSndFactor gamma.fst gamma.snd = (v : ℤ) ^ 5 := by
  have hn : 0 < gamma.snd := p.fifthRoot_snd_pos gamma hroot
  have hH : 0 < goldenFifthSndFactor gamma.fst gamma.snd :=
    p.fifthRoot_H_pos gamma hroot
  have hEq := p.fifthRoot_snd_factor_eq gamma hroot
  have hAbs := congrArg Int.natAbs hEq
  have hNatEq :
      p.base.snd.natAbs ^ 2 =
        5 * gamma.snd.natAbs *
          (goldenFifthSndFactor gamma.fst gamma.snd).natAbs := by
    simpa [Int.natAbs_pow, Int.natAbs_mul] using hAbs
  have hProduct :
      gamma.snd.natAbs *
          (goldenFifthSndFactor gamma.fst gamma.snd).natAbs =
        5 * (p.t ^ 2) ^ 5 := by
    apply Nat.mul_left_cancel (by norm_num : 0 < 5)
    calc
      5 * (gamma.snd.natAbs *
          (goldenFifthSndFactor gamma.fst gamma.snd).natAbs) =
          p.base.snd.natAbs ^ 2 := by
        rw [hNatEq]
        ring
      _ = (5 * p.t ^ 5) ^ 2 := by rw [p.snd_natAbs_eq]
      _ = 5 * (5 * (p.t ^ 2) ^ 5) := by ring
  have hFiveNotH :
      ¬ 5 ∣ (goldenFifthSndFactor gamma.fst gamma.snd).natAbs := by
    intro h
    exact p.fifthRoot_five_not_dvd_H gamma hnorm
      (Int.natCast_dvd.mpr h)
  have hFiveN : 5 ∣ gamma.snd.natAbs := by
    have hFiveProduct : 5 ∣
        gamma.snd.natAbs *
          (goldenFifthSndFactor gamma.fst gamma.snd).natAbs := by
      rw [hProduct]
      exact dvd_mul_right 5 _
    rcases (show Nat.Prime 5 by norm_num).dvd_mul.mp hFiveProduct with h | h
    · exact h
    · exact (hFiveNotH h).elim
  rcases hFiveN with ⟨n0, hn0⟩
  have hn0Eq :
      n0 * (goldenFifthSndFactor gamma.fst gamma.snd).natAbs =
        (p.t ^ 2) ^ 5 := by
    rw [hn0] at hProduct
    apply Nat.mul_left_cancel (by norm_num : 0 < 5)
    simpa [mul_assoc] using hProduct
  have hrootCoprime := p.fifthRoot_coprime_coords gamma hroot hnorm
  have hcopNH := coprime_natAbs_goldenFifthSndFactor_of_coprime
    gamma.fst gamma.snd hrootCoprime
  have hn0Dvd : n0 ∣ gamma.snd.natAbs := by
    rw [hn0]
    exact dvd_mul_left n0 5
  have hcopN0H : Nat.Coprime n0
      (goldenFifthSndFactor gamma.fst gamma.snd).natAbs :=
    hcopNH.of_dvd_left hn0Dvd
  have hunit : IsUnit (gcd n0
      (goldenFifthSndFactor gamma.fst gamma.snd).natAbs) := by
    simpa [gcd_eq_nat_gcd, Nat.Coprime, Nat.isUnit_iff] using hcopN0H
  obtain ⟨u, hu⟩ := exists_eq_pow_of_mul_eq_pow hunit hn0Eq
  have hunit' : IsUnit (gcd
      (goldenFifthSndFactor gamma.fst gamma.snd).natAbs n0) := by
    simpa [gcd_comm] using hunit
  obtain ⟨v, hv⟩ := exists_eq_pow_of_mul_eq_pow hunit'
    (by simpa [mul_comm] using hn0Eq)
  have huPos : 0 < u := by
    by_contra hu0
    have huZero : u = 0 := Nat.eq_zero_of_not_pos hu0
    have hnZero : gamma.snd.natAbs = 0 := by simp [hn0, hu, huZero]
    exact (Int.natAbs_ne_zero.mpr (ne_of_gt hn)) hnZero
  have hvPos : 0 < v := by
    by_contra hv0
    have hvZero : v = 0 := Nat.eq_zero_of_not_pos hv0
    have hHZero :
        (goldenFifthSndFactor gamma.fst gamma.snd).natAbs = 0 := by
      simp [hv, hvZero]
    exact (Int.natAbs_ne_zero.mpr (ne_of_gt hH)) hHZero
  refine ⟨u, v, huPos, hvPos, ?_, ?_⟩
  · have hcast : (gamma.snd.natAbs : ℤ) = 5 * (u : ℤ) ^ 5 := by
      exact_mod_cast (by rw [hn0, hu])
    rw [Int.ofNat_natAbs_of_nonneg hn.le] at hcast
    exact hcast
  · have hcast :
        ((goldenFifthSndFactor gamma.fst gamma.snd).natAbs : ℤ) =
          (v : ℤ) ^ 5 := by exact_mod_cast hv
    rw [Int.ofNat_natAbs_of_nonneg hH.le] at hcast
    exact hcast
```

## Lean の型

概念的には次の型である。

```lean
GoldenZeroSectorDescentPacket.fifthRoot_power_split :
  (p : GoldenZeroSectorDescentPacket) →
  (gamma : GoldenInt) →
  goldenZeroSectorLift p.base = goldenPow gamma 5 →
  goldenNorm gamma = (p.D : ℤ) →
  ∃ u v : ℕ,
    0 < u ∧ 0 < v ∧
    gamma.snd = 5 * (u : ℤ) ^ 5 ∧
    goldenFifthSndFactor gamma.fst gamma.snd = (v : ℤ) ^ 5
```

入力は descent packet `p`、第五根 `gamma`、第五冪等式 `hroot`、および norm 同定 `hnorm` である。出力は正の自然数 `u,v` と、第五根側での正確な冪分離

$$
\gamma_{\mathrm{snd}}=5u^5,
\qquad
H(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}})=v^5
$$

である。

## 数学的主張

以下

$$
b=\gamma_{\mathrm{snd}},
\qquad
H=H(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}}),
\qquad
s=p.base.snd
$$

と書く。0388 から

$$
s^2=5bH
$$

である。一方 packet には

$$
|s|=5t^5
$$

が保存されているので、絶対値を取れば

$$
|s|^2=5|b||H|
$$

かつ

$$
|s|^2=(5t^5)^2=25t^{10}.
$$

5 を一つ消去すると

$$
|b||H|=5(t^2)^5.
$$

0392 により $5\nmid H$ なので、素数 5 は必ず $|b|$ 側へ入る。したがって

$$
|b|=5n_0
$$

と書け、

$$
n_0|H|=(t^2)^5
$$

を得る。

0391 の座標 primitive 条件から既存補題 `coprime_natAbs_goldenFifthSndFactor_of_coprime` を通して

$$
\gcd(|b|,|H|)=1
$$

が得られるため、その約数 $n_0$ についても

$$
\gcd(n_0,|H|)=1.
$$

互いに素な二因子の積が第五冪なので、それぞれが第五冪であり、

$$
n_0=u^5,
\qquad
|H|=v^5.
$$

0389・0390 の正値性により絶対値を外して、最終的に

$$
b=5u^5,
\qquad
H=v^5
$$

を得る。

## 証明全体での役割

0393 `fifthRoot_measure_lt` が **strict decrease** を供給するのに対し、0394 は **recursive shape の保存** を担当する。

0387 で元 packet の quadratic lift から第五根 `gamma` を得た後、0388–0392 はその根が次世代の primitive zero-sector base として使えるための符号・coprimality・5-adic 条件を回収した。0394 はさらに積恒等式を

$$
5u^5\cdot v^5
$$

という packet 構築に直接使える形へ戻す。

すなわち infinite descent に必要な二条件

$$
\text{same structural invariants},
\qquad
\text{strictly smaller measure}
$$

のうち、0393 が後者、0394 が前者の主要な冪分離部分を完成させる。

## 直接依存する定義・補題

主要な直接依存は次の通りである。

- `GoldenZeroSectorDescentPacket`
- `GoldenInt`
- `goldenZeroSectorLift`
- `goldenPow`
- `goldenNorm`
- `goldenFifthSndFactor`
- `GoldenZeroSectorDescentPacket.fifthRoot_snd_pos`
- `GoldenZeroSectorDescentPacket.fifthRoot_H_pos`
- `GoldenZeroSectorDescentPacket.fifthRoot_snd_factor_eq`
- `GoldenZeroSectorDescentPacket.fifthRoot_five_not_dvd_H`
- `GoldenZeroSectorDescentPacket.fifthRoot_coprime_coords`
- `GoldenZeroSectorDescentPacket.snd_natAbs_eq`
- `coprime_natAbs_goldenFifthSndFactor_of_coprime`
- `exists_eq_pow_of_mul_eq_pow`
- `Int.natAbs_pow`
- `Int.natAbs_mul`
- `Int.natCast_dvd`
- `Int.ofNat_natAbs_of_nonneg`
- `Nat.Prime.dvd_mul`
- `Nat.Coprime.of_dvd_left`
- `Nat.mul_left_cancel`
- `gcd_eq_nat_gcd`

特に `exists_eq_pow_of_mul_eq_pow` が、互いに素な積が第五冪であることから各因子を第五冪へ分離する抽象的なエンジンである。

## 証明・構築の流れ

1. 0390 と 0389 から $b>0$ と $H>0$ を取得する。
2. 0388 の整数等式へ `Int.natAbs` を適用し、自然数等式 `hNatEq` を作る。
3. packet の `snd_natAbs_eq` を使い、
   $$
   |b||H|=5(t^2)^5
   $$
   という `hProduct` を得る。
4. 0392 を `Int.natCast_dvd` で自然数の非可除性へ移し、$5\nmid |H|$ を得る。
5. 5 の素性と `hProduct` により $5\mid |b|$ を強制し、$|b|=5n_0$ と置く。
6. 5 を cancellation して
   $$
   n_0|H|=(t^2)^5
   $$
   を得る。
7. 0391 から quartic factor との coprimality を取得し、その左因子を $n_0$ へ縮める。
8. gcd が unit である形へ変換し、`exists_eq_pow_of_mul_eq_pow` を両方向に適用して $n_0=u^5$、$|H|=v^5$ を得る。
9. $u,v$ が 0 なら $|b|=0$ または $|H|=0$ になるため、既知の正値性と矛盾させて $u,v>0$ を得る。
10. `exact_mod_cast` と `Int.ofNat_natAbs_of_nonneg` を使い、自然数上の等式を整数上の符号付き等式へ戻す。

## Lean 固有の処理

この証明では `ℤ` と `ℕ` の境界処理が多い。代数的な元の等式は整数上にあるが、素因数分離と `exists_eq_pow_of_mul_eq_pow` は自然数側で扱うため、一度 `congrArg Int.natAbs` によって全体を `ℕ` へ移している。

`simpa [Int.natAbs_pow, Int.natAbs_mul]` は絶対値と積・冪の整形、`Int.natCast_dvd.mpr` は自然数の可除性を整数へ持ち上げる bridge である。末尾の `exact_mod_cast` は逆方向に自然数第五冪等式を整数へ cast し、正値性を使う `Int.ofNat_natAbs_of_nonneg` によって `natAbs` を元の整数へ戻す。

また `Nat.Coprime` から `IsUnit (gcd ...)` へ変換しているのは、`exists_eq_pow_of_mul_eq_pow` が gcd の unit 条件を要求する API だからである。

## 冗長・重複箇所

証明前半では `hNatEq` と `hProduct` の二段階で同じ積恒等式を変形しており、zero-sector 系には「整数積等式を `natAbs` の冪積へ変換する」処理が複数回現れる。この変換は helper lemma 化できる余地がある。

また `hunit` と `hunit'` は gcd の引数順を入れ替えただけであり、`exists_eq_pow_of_mul_eq_pow` に左右対称版または coprime 版 wrapper があれば一度の coprimality 情報から直接二つの第五根を取り出せる。

`huPos` と `hvPos` も「正の整数が第五冪に等しいなら根も正」という一般補題にまとめられる。

## 最適化候補

最も有力なのは、次の形の専用補題を用意することである。

```lean
Nat.Coprime a b →
a * b = c ^ 5 →
∃ u v, a = u ^ 5 ∧ b = v ^ 5
```

これにより `gcd`、`IsUnit`、`gcd_comm` をこの theorem から隠蔽できる。

さらに

```lean
|s| = 5 * t ^ 5 →
s ^ 2 = 5 * b * H →
0 < b → 0 < H → ¬ 5 ∣ H →
...
```

という zero-sector product split の arithmetic core を packet 非依存補題へ分離すれば、Comparator challenge と再利用性の双方が改善する。

一方、0394 自体は packet API を統合する orchestration theorem として残すのが自然である。

## 必要 Mathlib import と import 最適化候補

確認できる standalone 正本は

```lean
import Mathlib
```

を使用している。

この theorem が直接利用する Mathlib 機能には、自然数・整数の divisibility/coprimality、`gcd` と `IsUnit`、`natAbs`、cast、`norm_num`、`ring`、`simp` などが含まれる。

ただし、この実行では Lean build を行わない条件なので、`Mathlib` をどの個別 import 群まで安全に縮小できるかは **未確認** である。import 最適化を行うなら、定理本体の算術 core を分離した後、`Mathlib.Data.Nat.GCD.Basic`、整数 divisibility/cast 関係、および使用 tactic の import を候補として実ビルドで最小化するのが安全である。

## Comparator challenge 化の可否

**可。しかも良い候補である。**

ただし theorem 全体をそのまま challenge にすると DkMath 固有 packet API への依存が大きい。Comparator 向けには arithmetic core、すなわち

$$
xy=5z^5,
\qquad
\gcd(x,y)=1,
\qquad
5\nmid y
$$

から

$$
x=5u^5,
\qquad
y=v^5
$$

を導く部分を独立させるのが望ましい。

この形なら「素数 5 の ownership」「coprime product の power split」「cast を含まない自然数算術」という三点に集中でき、複数の Lean 証明戦略を比較しやすい。

## 次に読むべき宣言

次は **0395 `GoldenZeroSectorStrictDescent`** である。宣言種別は `structure`。

```lean
structure GoldenZeroSectorStrictDescent
    (source : GoldenZeroSectorDescentPacket) where
  next : GoldenZeroSectorDescentPacket
  lift_eq : goldenZeroSectorLift source.base = goldenPow next.base 5
  measure_lt :
    goldenZeroSectorDescentMeasure next <
      goldenZeroSectorDescentMeasure source
```

0393 で strict decrease、0394 で recursive power shape が揃った直後に、その成果を「次 packet」「第五冪による再入」「measure の真の減少」の三点を持つ一つの証明オブジェクトへ束ねる構造体である。ここから descent は個別補題の集合ではなく、反復可能な certified step として扱われる。