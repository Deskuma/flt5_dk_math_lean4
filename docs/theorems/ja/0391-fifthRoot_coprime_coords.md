# 0391 `GoldenZeroSectorDescentPacket.fifthRoot_coprime_coords`

## 宣言種別

`theorem`

`GoldenZeroSectorDescentPacket` namespace 内で、0387 以降に得られた第五根 `gamma : GoldenInt` の二座標が primitive、すなわち互いに素であることを回収する補題である。

## Lean コード

```lean
theorem fifthRoot_coprime_coords
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5)
    (hnorm : goldenNorm gamma = (p.D : ℤ)) :
    Nat.Coprime gamma.fst.natAbs gamma.snd.natAbs := by
  by_contra hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
    ⟨q, hqPrime, hqF, hqSnd⟩
  have hqFZ : (q : ℤ) ∣ gamma.fst := Int.natCast_dvd.mpr hqF
  have hqSndZ : (q : ℤ) ∣ gamma.snd := Int.natCast_dvd.mpr hqSnd
  have hqNormZ : (q : ℤ) ∣ goldenNorm gamma := by
    simp only [goldenNorm]
    exact dvd_sub (dvd_add (dvd_pow hqFZ (by decide : 2 ≠ 0))
      (dvd_mul_of_dvd_left hqFZ gamma.snd))
      (dvd_pow hqSndZ (by decide : 2 ≠ 0))
  have hqD : q ∣ p.D := by
    rw [hnorm] at hqNormZ
    exact_mod_cast hqNormZ
  have hEq := p.fifthRoot_snd_factor_eq gamma hroot
  have hqBaseSqZ : (q : ℤ) ∣ p.base.snd ^ 2 := by
    rw [hEq]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hqSndZ 5) _
  have hqBaseSq : q ∣ p.base.snd.natAbs ^ 2 := by
    simpa [Int.natAbs_pow] using Int.natCast_dvd.mp hqBaseSqZ
  have hqBase : q ∣ p.base.snd.natAbs :=
    hqPrime.dvd_of_dvd_pow hqBaseSq
  exact (Nat.not_coprime_of_dvd_of_dvd hqPrime.one_lt hqD hqBase)
    p.coprime_D_s
```

## Lean の型

概念的には次の型である。

```lean
GoldenZeroSectorDescentPacket.fifthRoot_coprime_coords :
  (p : GoldenZeroSectorDescentPacket) →
  (gamma : GoldenInt) →
  goldenZeroSectorLift p.base = goldenPow gamma 5 →
  goldenNorm gamma = (p.D : ℤ) →
  Nat.Coprime gamma.fst.natAbs gamma.snd.natAbs
```

入力は descent packet `p`、黄金整数 `gamma`、lift が `gamma^5` であることを示す `hroot`、および

```lean
goldenNorm gamma = (p.D : ℤ)
```

という norm 同定 `hnorm` である。出力は `gamma` の二整数座標の絶対値が自然数上で互いに素であること、すなわち

$$
\gcd(|\gamma_{\mathrm{fst}}|,|\gamma_{\mathrm{snd}}|)=1
$$

である。

## 数学的主張

`gamma=(a,b)`、`p.base=(r,s)` と書く。

示すべきことは

$$
\gcd(|a|,|b|)=1.
$$

反対に、$|a|$ と $|b|$ が互いに素でないと仮定する。すると共通素因子 $q$ が存在して

$$
q\mid |a|,
\qquad
q\mid |b|.
$$

整数側では

$$
q\mid a,
\qquad
q\mid b.
$$

となる。

黄金整数 norm は

$$
N(a,b)=a^2+ab-b^2
$$

なので、$q$ は三項すべてを割り、したがって

$$
q\mid N(a,b).
$$

仮定 `hnorm` により

$$
N(a,b)=D,
$$

ゆえに

$$
q\mid D.
$$

一方、0388 `fifthRoot_snd_factor_eq` から

$$
s^2
 = 5bH(a,b),
$$

ここで

$$
H(a,b)
 = a^4+2a^3b+4a^2b^2+3ab^3+b^4.
$$

$q\mid b$ なので

$$
q\mid s^2.
$$

$q$ は素数だから

$$
q\mid |s|.
$$

従って同じ素数 $q$ が

$$
q\mid D,
\qquad
q\mid |s|
$$

を満たす。しかし 0384 `coprime_D_s` は

$$
\gcd(D,|s|)=1
$$

を既に保証しているので矛盾する。

したがって

$$
\gcd(|a|,|b|)=1
$$

である。

## 証明全体での役割

0387 `exists_lift_eq_fifthPower` によって、元の quadratic lift は

$$
T(r,s)=\gamma^5,
\qquad
N(\gamma)=D
$$

という純粋な第五冪にまで整理された。0388–0390 では第二座標を射影し、quartic factor と `gamma.snd` の正値性を得た。

0391 は、第五根 `gamma` を次の descent datum として使うために必要な **primitive 条件を回収する段階** である。

単に第五根が存在するだけでは descent を反復できない。次の packet を元の packet と同じ primitive class に戻すためには、`gamma=(a,b)` が

$$
\gcd(|a|,|b|)=1
$$

を満たす必要がある。本 theorem はまさにその閉包性を示す。

証明の構造は特徴的で、`gamma` 内部の仮想的な共通素因子 $q$ を二方向へ送る。

1. norm を通して $q\mid D$ へ送る。
2. fifth-root の第二座標恒等式を通して $q\mid |s|$ へ送る。
3. 既存の packet invariant `coprime_D_s` で二つを衝突させる。

したがって 0391 は、黄金整数環で得た fifth root を、元 packet の自然数 primitive invariant へ接続する bridge theorem である。

## 直接依存する定義・補題

主要な直接依存は次の通りである。

- `GoldenZeroSectorDescentPacket`
- `GoldenInt`
- `goldenZeroSectorLift`
- `goldenPow`
- `goldenNorm`
- `GoldenZeroSectorDescentPacket.fifthRoot_snd_factor_eq`
- `GoldenZeroSectorDescentPacket.coprime_D_s`
- `Nat.Prime.not_coprime_iff_dvd`
- `Int.natCast_dvd.mpr`
- `Int.natCast_dvd.mp`
- `dvd_pow`
- `dvd_mul_of_dvd_left`
- `dvd_mul_of_dvd_right`
- `dvd_add`
- `dvd_sub`
- `Int.natAbs_pow`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.not_coprime_of_dvd_of_dvd`
- `exact_mod_cast`

`hroot` は直接 norm の計算には使われず、0388 の

```lean
p.fifthRoot_snd_factor_eq gamma hroot
```

を呼び出すために使われる。一方 `hnorm` は `q ∣ goldenNorm gamma` を `q ∣ p.D` に変換するために使われる。この二入力は異なる経路を担当している。

## 証明・構築の流れ

1. 目的の coprimality を否定する。

   ```lean
   by_contra hcop
   ```

2. `Nat.Prime.not_coprime_iff_dvd` により共通素因子 $q$ を抽出する。

   ```lean
   rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
     ⟨q, hqPrime, hqF, hqSnd⟩
   ```

   ここで

   $$
   q\mid |a|,
   \qquad
   q\mid |b|.
   $$

3. `natAbs` 上の自然数可除性を整数可除性へ移す。

   ```lean
   have hqFZ : (q : ℤ) ∣ gamma.fst := Int.natCast_dvd.mpr hqF
   have hqSndZ : (q : ℤ) ∣ gamma.snd := Int.natCast_dvd.mpr hqSnd
   ```

4. norm の定義

   $$
   N(a,b)=a^2+ab-b^2
   $$

   を展開し、$q\mid a,b$ から $q\mid N(a,b)$ を構築する。

5. `hnorm` を使って

   $$
   q\mid N(\gamma)
   \Longrightarrow
   q\mid D
   $$

   を得る。

6. 0388 の第二座標恒等式

   $$
   s^2=5bH(a,b)
   $$

   を取得する。

7. $q\mid b$ から右辺全体、従って $s^2$ が $q$ で割れることを示す。

8. `Int.natAbs_pow` と `Int.natCast_dvd.mp` で自然数側の

   $$
   q\mid |s|^2
   $$

   に戻す。

9. $q$ の素性から

   $$
   q\mid |s|
   $$

   を得る。

10. $q\mid D$ と $q\mid |s|$ から `Nat.not_coprime_of_dvd_of_dvd` により `Nat.Coprime p.D p.base.snd.natAbs` の否定を作り、0384 `p.coprime_D_s` と矛盾させる。

## Lean 固有の処理

### `Nat.Prime.not_coprime_iff_dvd`

数学では「互いに素でないなら共通素因子がある」と一言で済むが、Lean ではこれを

```lean
Nat.Prime.not_coprime_iff_dvd.mp hcop
```

で具体的な prime witness `q` と二つの divisibility proof に変換している。

この witness 化が後続証明の軸になる。

### `Int.natCast_dvd`

本 theorem は自然数の `natAbs` と整数座標を何度も往復する。

```lean
Int.natCast_dvd.mpr hqF
Int.natCast_dvd.mpr hqSnd
```

は

$$
q\mid |a|
$$

を整数上の

$$
(q:\mathbb Z)\mid a
$$

へ移す。

逆向きには

```lean
Int.natCast_dvd.mp hqBaseSqZ
```

を用いて整数可除性から自然数可除性へ戻している。

### norm の可除性を手作業で構築

```lean
simp only [goldenNorm]
exact dvd_sub (dvd_add (dvd_pow hqFZ ...)
  (dvd_mul_of_dvd_left hqFZ gamma.snd))
  (dvd_pow hqSndZ ...)
```

では `goldenNorm` を明示展開し、$q$ が各項を割ることから norm 全体を割ることを構築している。

これは自動化に任せず、可除性の構造を Lean の combinator で直接組み立てた部分である。

### `exact_mod_cast`

`hnorm` で norm を `p.D : ℤ` に置換した後、整数上の

```lean
(q : ℤ) ∣ (p.D : ℤ)
```

を自然数上の

```lean
q ∣ p.D
```

へ戻すために `exact_mod_cast` を使っている。

### `Int.natAbs_pow`

元の第二座標は整数だが、`coprime_D_s` は自然数 `natAbs` 上の statement である。このため

```lean
simpa [Int.natAbs_pow] using Int.natCast_dvd.mp hqBaseSqZ
```

によって

$$
q\mid s^2
$$

を

$$
q\mid |s|^2
$$

へ整形している。

### prime divisor の平方からの降下

```lean
hqPrime.dvd_of_dvd_pow hqBaseSq
```

によって

$$
q\mid |s|^2
\Longrightarrow
q\mid |s|
$$

を得る。ここでは $q$ が prime であることが本質的である。

## 冗長・重複箇所

証明自体は論理の流れが明瞭で、不要な中間事実はほぼない。ただし既存コードには抽象化可能なパターンがある。

### 1. 「共通座標素因子は norm を割る」の重複

`hqFZ` と `hqSndZ` から `hqNormZ` を構築する部分は、黄金整数について一般に成立する。

例えば

```lean
theorem goldenNorm_dvd_of_common_coord_dvd
    {q : ℤ} {z : GoldenInt}
    (hfst : q ∣ z.fst) (hsnd : q ∣ z.snd) :
    q ∣ goldenNorm z
```

のような helper があれば、本 theorem の norm 展開を隠蔽できる。

リポジトリ内に同等 API が既に存在するかどうかは、今回確認した範囲では確定できないため、これは **候補** である。

### 2. `natAbs` / cast 往復

自然数上で prime witness を取り、整数座標へ cast し、最後に再び自然数へ戻る処理が長い。

これは theorem の statement が `Nat.Coprime ...natAbs...`、代数計算が `ℤ` 上という設計から自然に生じる境界であり、単純な冗長ではない。しかし同様の bridge が複数 theorem に現れるなら補助 API の価値が高い。

### 3. `hroot` の間接利用

`hroot` は `p.fifthRoot_snd_factor_eq gamma hroot` のためだけに使われる。これは冗長ではなく dependency を明示する良い設計である。もし後続でも同じ `hEq` を繰り返し要求するなら、`hEq` を直接受け取る低レベル lemma と現在の high-level wrapper に分離する選択肢はある。

## 最適化候補

### 1. norm divisibility helper

最も自然な最適化候補は、二座標の共通因子から norm の因子を得る一般補題の抽出である。これにより theorem 本体は

- 共通 prime の抽出
- $q\mid D$
- $q\mid |s|$
- `coprime_D_s` contradiction

という数学的骨格だけになる。

### 2. second-coordinate transport helper

0388 の恒等式から

```lean
q ∣ gamma.snd.natAbs → q ∣ p.base.snd.natAbs
```

を、prime `q` に対する補助 lemma として切り出すことも可能である。後続の五進分解で同じ伝播を使うなら再利用価値がある。

### 3. `exact_mod_cast` の局所化

整数 norm と自然数 `D` の境界を専用 lemma で包めば、main proof から cast tactic を除去できる。形式化の可読性と Comparator 化には有利である。

### 4. contradiction の最終行

現在の

```lean
exact (Nat.not_coprime_of_dvd_of_dvd hqPrime.one_lt hqD hqBase)
  p.coprime_D_s
```

は簡潔でよい。ここを `exact False.elim ...` 等へ展開する必要はなく、現形がほぼ最適である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は現在

```lean
import Mathlib
```

を使用している。

本 theorem で直接見える Mathlib 機能は主に次である。

- `Nat.Coprime` / `Nat.Prime`
- divisibility API (`dvd_add`, `dvd_sub`, `dvd_pow`, `dvd_mul_of_dvd_left`, `dvd_mul_of_dvd_right`)
- `Int.natCast_dvd`
- `Int.natAbs_pow`
- `exact_mod_cast`
- `simp`

従って最小化する場合は自然数素数・coprimality、整数 divisibility/cast、power、cast tactic 周辺の module が候補になる。ただし `GoldenInt`、`GoldenZeroSectorDescentPacket`、`goldenNorm`、および先行 theorem 群の transitive dependency を含む厳密な最小 import は、この実行では Lean build を行わないため確認していない。

したがって **確認済みの working import は `Mathlib`、厳密な最小 import は未確定** である。

## Comparator challenge 化の可否

**可。中規模の divisibility / cast / coprimality challenge として良い題材である。**

FLT5 固有定義を抽象化すると、核は次の形になる。

```lean
(hnorm : N a b = D)
(hEq : s ^ 2 = 5 * b * H)
(hDS : Nat.Coprime D s.natAbs)
⊢ Nat.Coprime a.natAbs b.natAbs
```

ただし `N a b = a^2 + a*b - b^2` という norm 構造を与える必要がある。

challenge の重要点は、

1. 非 coprime から共通 prime witness を抽出する。
2. $q\mid a,b$ から $q\mid N(a,b)$ を示す。
3. norm equality から $q\mid D$ へ transport する。
4. $q\mid b$ と $s^2=5bH$ から $q\mid s$ を得る。
5. `Coprime D |s|` と矛盾させる。

という複数 domain の接続にある。

特に `Nat` と `Int` の cast をそのまま残す版は Lean 実務的な Comparator challenge になる。一方、全変数を同一整域上に置いて cast を除去した版なら純粋な数学構造の比較に向く。

## 次に読むべき宣言

次は **0392 `GoldenZeroSectorDescentPacket.fifthRoot_five_not_dvd_H`** である。宣言種別は `theorem`。

Lean 正本では 0391 の直後に次の形で始まる。

```lean
theorem fifthRoot_five_not_dvd_H
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hnorm : goldenNorm gamma = (p.D : ℤ)) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd := by
  intro hH
  have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq gamma
  ...
```

0391 で第五根 `gamma` 自身の primitive coordinates を確定した後、0392 は第五根側の quartic factor

$$
H(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}})
$$

について 5 が割らないことを確定する段階へ進む。

これは元 packet で 0381 `five_not_dvd_H` が担った 5-adic clean property を第五根側へ再生する処理であり、再帰的 descent packet の構築へ向けて invariant を一つずつ復元していく流れに位置する。
