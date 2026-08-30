# 0281 — `SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split`

## 宣言種別

これは **`theorem`** である。

zero sector で fifth-power base `gamma : GoldenInt` が与えられたとき、第二座標の自然数絶対値に現れる `5^6` を完全に分離し、残りの第二座標因子と quartic factor がそれぞれ tenth power になることを示す。

## Lean の型

```lean
/--
The coprime zero-sector product splits exactly: all six factors of five lie in
the second coordinate, and the remaining coprime factors are tenth powers.
-/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    ∃ c d : ℕ,
      gamma.snd.natAbs = 5 ^ 6 * c ^ 10 ∧
      (goldenFifthSndFactor gamma.fst gamma.snd).natAbs = d ^ 10 := by
  let H := (goldenFifthSndFactor gamma.fst gamma.snd).natAbs
  have hprod : gamma.snd.natAbs * H =
      5 ^ 6 * p.exceptional.powerSplit.a ^ 10 := by
    simpa [H] using p.zeroSector_natAbs_product_eq hbeta
  have h5H : ¬ 5 ∣ H := by
    intro h
    apply p.zeroSector_five_not_dvd_sndFactor hbeta
    apply Int.natCast_dvd.mpr
    simpa [H] using h
  have hcop5H : Nat.Coprime (5 ^ 6) H :=
    (Nat.Coprime.pow_left 6
      ((by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr h5H))
  have h5dvdProduct : 5 ^ 6 ∣ gamma.snd.natAbs * H := by
    rw [hprod]
    exact dvd_mul_right (5 ^ 6) _
  have h5dvdS : 5 ^ 6 ∣ gamma.snd.natAbs :=
    hcop5H.dvd_of_dvd_mul_right h5dvdProduct
  rcases h5dvdS with ⟨t, ht⟩
  have htProduct : t * H = p.exceptional.powerSplit.a ^ 10 := by
    rw [ht] at hprod
    rw [mul_assoc] at hprod
    exact Nat.mul_left_cancel (by positivity) hprod
  have htDvdS : t ∣ gamma.snd.natAbs := by
    rw [ht]
    exact dvd_mul_left t (5 ^ 6)
  have hcopTH : Nat.Coprime t H :=
    (p.zeroSector_coprime_s_sndFactor hbeta).of_dvd_left htDvdS
  have hunit : IsUnit (gcd t H) := by
    simpa [gcd_eq_nat_gcd, Nat.Coprime, Nat.isUnit_iff] using hcopTH
  obtain ⟨c, hc⟩ :=
    exists_eq_pow_of_mul_eq_pow hunit htProduct
  have hunit' : IsUnit (gcd H t) := by
    simpa [gcd_comm] using hunit
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hunit'
    (by simpa [mul_comm] using htProduct)
  exact ⟨c, d, by simpa [hc] using ht, hd⟩
```

`gamma = (r,s)` とし、

```lean
goldenFifthSndFactor r s
```

の自然数絶対値を `H` と書けば、結論は

$$
|s|=5^6c^{10},
\qquad
H=d^{10}
$$

となる。

## 数学的主張の意味

直前までに zero sector では

$$
|s|H=5^6a^{10}
$$

が得られている。また、

$$
5\nmid H,
\qquad
\gcd(|s|,H)=1
$$

も証明済みである。

まず `5 ∤ H` から

$$
\gcd(5^6,H)=1
$$

である。ところが `5^6` は積 `|s|H` を割るので、Euclid の補題型の coprimality 消去により

$$
5^6\mid |s|
$$

が従う。よってある `t : ℕ` が存在して

$$
|s|=5^6t
$$

と書ける。

これを積等式へ戻して正の因子 `5^6` を消去すると

$$
tH=a^{10}
$$

を得る。

さらに `t | |s|` と `gcd(|s|,H)=1` から

$$
\gcd(t,H)=1
$$

である。互いに素な二自然数の積が tenth power なので、素因数の指数は両因子間で混ざらず、それぞれが tenth power でなければならない。したがって

$$
t=c^{10},
\qquad
H=d^{10}
$$

となり、最終的に

$$
|s|=5^6c^{10},
\qquad
H=d^{10}
$$

を得る。

これは単なる可除性ではなく、zero-sector product の素因数所有権を完全に確定する分解定理である。

## 証明全体での役割

0275 から 0280 までで、second-coordinate equation は段階的に整備された。

$$
sH(r,s)=-5^6a^{10}
$$

を 0278 が自然数絶対値へ移して

$$
|s||H|=5^6a^{10}
$$

とし、0277 が `5 ∤ H`、0279 と 0280 が primitive/coprime 条件を与えた。本 theorem 0281 はそれらを一つにまとめ、以後の inversion layer が直接使える

$$
|s|=5^6c^{10},
\qquad
|H|=d^{10}
$$

という正規形へ変換する。

この theorem をもって生成 source `SignedGoldenZeroSector.lean` は終了し、次の `SignedGoldenZeroSectorInversion.lean` では

$$
X=2r+s,
\qquad
U=X^2+5s^2,
\qquad
W=4d^5
$$

という新しい座標へ移る。したがって 0281 は **zero-sector arithmetic と inversion geometry の境界** に位置する。

## 直接依存する定義・補題

### `SignedGoldenRamifierStrippedPacket.zeroSector_natAbs_product_eq`（0278）

```lean
gamma.snd.natAbs *
    (goldenFifthSndFactor gamma.fst gamma.snd).natAbs =
  5 ^ 6 * p.exceptional.powerSplit.a ^ 10
```

本 theorem の基礎となる積等式を与える。

### `SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_sndFactor`（0277）

```lean
¬ (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd
```

これを `Int.natCast_dvd` で自然数絶対値側へ移し、`5 ∤ H` を得る。

### `SignedGoldenRamifierStrippedPacket.zeroSector_coprime_s_sndFactor`（0280）

```lean
Nat.Coprime gamma.snd.natAbs
  (goldenFifthSndFactor gamma.fst gamma.snd).natAbs
```

`|s|` と `H` の coprimality を与え、`t | |s|` から `gcd(t,H)=1` へ降ろす。

### `Nat.Coprime.dvd_of_dvd_mul_right`

`gcd(5^6,H)=1` と `5^6 | |s|H` から `5^6 | |s|` を取り出す。

### `exists_eq_pow_of_mul_eq_pow`

互いに素な積が冪であるとき、一方の因子自身も同じ指数の冪であることを与える一般 GCDMonoid 補題。本 theorem では `t` と `H` の双方へ向きを替えて二度使う。

## 証明または構築の流れ

### 1. quartic factor の自然数絶対値を `H` と置く

```lean
let H := (goldenFifthSndFactor gamma.fst gamma.snd).natAbs
```

以後の自然数因数分解を読みやすくするローカル略記である。

### 2. 0278 の積等式を `H` 表記へ移す

```lean
have hprod : gamma.snd.natAbs * H =
    5 ^ 6 * p.exceptional.powerSplit.a ^ 10 := by
  simpa [H] using p.zeroSector_natAbs_product_eq hbeta
```

### 3. `5 ∤ H` を整数側の 0277 から移す

```lean
have h5H : ¬ 5 ∣ H := by
  intro h
  apply p.zeroSector_five_not_dvd_sndFactor hbeta
  apply Int.natCast_dvd.mpr
  simpa [H] using h
```

ここは `ℕ` の `natAbs` と `ℤ` 上の quartic factor の型境界である。

### 4. `5^6` と `H` の coprimality を作る

```lean
have hcop5H : Nat.Coprime (5 ^ 6) H :=
  (Nat.Coprime.pow_left 6
    ((by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr h5H))
```

まず素数 5 と `H` が互いに素であることを作り、その左因子を 6 乗する。

### 5. `5^6` を `|s|` 側へ押し込む

```lean
have h5dvdS : 5 ^ 6 ∣ gamma.snd.natAbs :=
  hcop5H.dvd_of_dvd_mul_right h5dvdProduct
rcases h5dvdS with ⟨t, ht⟩
```

これで `ht` は `|s| = 5^6 * t` を表す。

### 6. `5^6` を消去して `tH=a^10` を得る

```lean
have htProduct : t * H = p.exceptional.powerSplit.a ^ 10 := by
  rw [ht] at hprod
  rw [mul_assoc] at hprod
  exact Nat.mul_left_cancel (by positivity) hprod
```

`5^6 > 0` を `positivity` で供給し、自然数の左消去を使う。

### 7. `t` と `H` の coprimality を継承する

```lean
have htDvdS : t ∣ gamma.snd.natAbs := by
  rw [ht]
  exact dvd_mul_left t (5 ^ 6)
have hcopTH : Nat.Coprime t H :=
  (p.zeroSector_coprime_s_sndFactor hbeta).of_dvd_left htDvdS
```

0280 の `gcd(|s|,H)=1` を divisor `t` へ降ろす。

### 8. generic GCDMonoid API へ渡す

```lean
have hunit : IsUnit (gcd t H) := by
  simpa [gcd_eq_nat_gcd, Nat.Coprime, Nat.isUnit_iff] using hcopTH
```

Mathlib の `exists_eq_pow_of_mul_eq_pow` が `Nat.Coprime` ではなく gcd が unit であるという一般形を要求するため、この変換を行う。

### 9. 両因子を tenth power として取り出す

```lean
obtain ⟨c, hc⟩ :=
  exists_eq_pow_of_mul_eq_pow hunit htProduct
```

で `t = c^10` を得る。さらに gcd と積の向きを交換し、

```lean
obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hunit'
  (by simpa [mul_comm] using htProduct)
```

で `H = d^10` を得る。

### 10. 最終形を組み立てる

```lean
exact ⟨c, d, by simpa [hc] using ht, hd⟩
```

## Lean 固有の処理

この proof の特徴は、算術の中身よりも **API 間の形の変換** にある。

`Int.natCast_dvd` は `ℤ` 上の非可除性と `natAbs : ℕ` 上の因数分解を接続する。`Nat.Coprime.pow_left` は `5` の coprimality を `5^6` へ持ち上げ、`Nat.Coprime.dvd_of_dvd_mul_right` は coprime な因子の所有権を決める。

さらに `Nat.Coprime` から

```lean
IsUnit (gcd t H)
```

へ変換する部分は、Mathlib の一般 GCDMonoid theorem を `ℕ` に適用するための Lean 固有の橋渡しである。

`gcd_eq_nat_gcd`、`Nat.isUnit_iff`、`gcd_comm`、`mul_comm` は数学的には自明な表現変更だが、generic theorem の入力型を正確に整えるために必要になる。

## 冗長・重複箇所

最も明確な重複は `exists_eq_pow_of_mul_eq_pow` を二方向へ二度呼ぶ部分である。

```lean
have hunit : IsUnit (gcd t H) := ...
obtain ⟨c, hc⟩ := exists_eq_pow_of_mul_eq_pow hunit htProduct
have hunit' : IsUnit (gcd H t) := by
  simpa [gcd_comm] using hunit
obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow hunit'
  (by simpa [mul_comm] using htProduct)
```

数学的には「互いに素な二因子の積が $n$ 乗なら、両因子とも $n$ 乗」という一つの対称な主張である。現在の Mathlib API が片側の存在を返す形なので、左右交換が明示されている。

一方、`H` のローカル定義や `5^6` を明示的に `|s|` へ移す段階は、証明の所有権構造を見せるため有益であり、過度に圧縮しない方が読みやすい。

## 最適化候補

### 1. coprime product power split の対称補題

例えば自然数専用に

```lean
Nat.Coprime x y → x * y = z ^ n →
  ∃ a b, x = a ^ n ∧ y = b ^ n
```

型の補助定理を用意すれば、`IsUnit (gcd ...)`、`gcd_comm`、二度の generic theorem 呼び出しを隠蔽できる。

### 2. `5^k` ownership の補助補題

`Nat.Coprime (5^6) H` と `5^6 | s*H` から `5^6 | s` を得る部分は、valuation/prime-power ownership として他でも現れる可能性がある。再利用頻度が高ければ generic helper 化できる。

### 3. 型境界の局所化

`zeroSector_five_not_dvd_sndFactor` の `natAbs` 版を別 lemma として持てば、この theorem 内の `Int.natCast_dvd` 変換を消せる。ただし API 数を増やすため、再利用がある場合に限るのがよい。

## 必要 Mathlib import と import 最適化候補

この repository の standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は、実際に

```lean
import Mathlib
```

を使用している。したがって **正本で確認できる import は `Mathlib`** である。

本 proof が実際に使う Mathlib 機能は、自然数の prime/coprime/divisibility、GCDMonoid の `gcd` と `exists_eq_pow_of_mul_eq_pow`、整数 cast/divisibility、そして `norm_num`・`positivity` などの tactic 群である。

より細い import へ削減できる可能性は高いが、この実行では Lean build も import bisect も行っていない。そのため具体的な最小 module 名を「必要」と断定することはできない。最適化候補は、`Mathlib` umbrella import を上記 API を供給する個別 module 群へ置き換え、別途 build で検証することである。

## Comparator challenge 化の可否

**適している。難度は中〜やや高。**

特に、packet 固有の前段を取り除いて次の純粋自然数問題に縮約するとよい。

```lean
hprod : s * H = 5 ^ 6 * a ^ 10
h5H   : ¬ 5 ∣ H
hcop  : Nat.Coprime s H
⊢ ∃ c d, s = 5 ^ 6 * c ^ 10 ∧ H = d ^ 10
```

この challenge は、単なる `ring` や `omega` ではなく、

- prime-power の coprime ownership
- divisor への coprimality 継承
- `Nat.Coprime` と generic GCDMonoid API の接続
- coprime product の power splitting

を適切に選べるかを測れる。

より Comparator 向けにするなら `exists_eq_pow_of_mul_eq_pow` の使用を許可する版と、素因数指数から自力で示す版の二段階に分けられる。

## PDF との対応について

対象 branch の repository tree には、日本語 PDF

```text
docs/pdf/FLT5-main-ja-v0-r1.pdf
```

と英語 PDF

```text
docs/pdf/FLT5-main-en-v0-r1.pdf
```

が存在することを確認した。

ただし、この実行では PDF binary 本文を解析可能な形で取得できなかった。そのため 0281 に対応する具体的なページ番号・節番号や、PDF 本文との逐語的対応は **未確認** であり、推測していない。本解説の技術的内容と Lean code は、branch 上の `Flt5DkMath/FLT5StandAlone.lean` を主要根拠としている。

## 次に読むべき宣言

次は **0282 `zeroSectorX`** である。宣言種別は `def`。

```lean
/-- The diagonal coordinate `X = 2*r+s`. -/
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s
```

0281 で zero-sector arithmetic の tenth-power split が完成すると、生成 source `SignedGoldenZeroSector.lean` は終了する。その直後の `SignedGoldenZeroSectorInversion.lean` は

$$
X=2r+s
$$

という対角座標の導入から始まる。

以後は

$$
U=X^2+5s^2,
\qquad
W=4d^5,
\qquad
A=U-W,
\qquad
B=U+W
$$

を構成し、quartic factor を inversion/factorization の形へ移していく。したがって 0282 は、0281 までの因数分解算術から次の幾何的・代数的再座標化へ入る最初の宣言である。
