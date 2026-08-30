# 0279 — `SignedGoldenRamifierStrippedPacket.zeroSector_coprime_coords`

## 宣言種別

これは **`theorem`** である。

zero sector の fifth-power base `gamma : GoldenInt` の二つの整数座標が primitive、すなわち自然数絶対値として互いに素であることを packet の算術条件から導く。

## Lean の型

```lean
/-- The two integer coordinates of a zero-sector fifth-power base are primitive. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_coprime_coords
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    Nat.Coprime gamma.fst.natAbs gamma.snd.natAbs := by
  by_contra hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
    ⟨q, hqPrime, hqr, hqs⟩
  have hqrZ : (q : ℤ) ∣ gamma.fst := Int.natCast_dvd.mpr hqr
  have hqsZ : (q : ℤ) ∣ gamma.snd := Int.natCast_dvd.mpr hqs
  have hqNormZ : (q : ℤ) ∣ goldenNorm gamma := by
    simp only [goldenNorm]
    exact dvd_sub (dvd_add (dvd_pow hqrZ (by decide))
      (dvd_mul_of_dvd_left hqrZ gamma.snd)) (dvd_pow hqsZ (by decide))
  have hqb : q ∣ p.exceptional.powerSplit.b := by
    rcases p.zeroSector_gamma_norm_eq_or_eq_neg hbeta with hn | hn
    · rw [hn] at hqNormZ
      exact_mod_cast hqNormZ
    · rw [hn] at hqNormZ
      exact_mod_cast (Int.dvd_neg.mp hqNormZ)
  have hprod := p.zeroSector_natAbs_product_eq hbeta
  have hqRhs : q ∣ 5 ^ 6 * p.exceptional.powerSplit.a ^ 10 := by
    rw [← hprod]
    exact dvd_mul_of_dvd_left hqs _
  rcases hqPrime.dvd_mul.mp hqRhs with hq5pow | hqapow
  · have hq5 : q ∣ 5 := hqPrime.dvd_of_dvd_pow hq5pow
    have hqeq : q = 5 :=
      ((Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hq5).resolve_left
        hqPrime.ne_one
    exact p.five_not_dvd_b (hqeq ▸ hqb)
  · have hqa : q ∣ p.exceptional.powerSplit.a :=
      hqPrime.dvd_of_dvd_pow hqapow
    exact (Nat.not_coprime_of_dvd_of_dvd hqPrime.one_lt hqa hqb)
      p.exceptional.powerSplit.coprime_a_b
```

`gamma = (r,s)`、packet の power split を `(a,b)` と略記すると、主張は

$$
\beta=\gamma^5
\quad\Longrightarrow\quad
\gcd(|r|,|s|)=1.
$$

ここで Lean の結論は

```lean
Nat.Coprime gamma.fst.natAbs gamma.snd.natAbs
```

であり、整数座標の primitive condition を自然数絶対値へ移して表している。

## 数学的主張の意味

背理法で `r` と `s` に共通素因子 `q` があると仮定する。

まず

$$
q\mid r,
\qquad
q\mid s
$$

なら、golden norm

$$
N(r,s)=r^2+rs-s^2
$$

の各項を `q` が割るので

$$
q\mid N(\gamma)
$$

となる。

0273 `zeroSector_gamma_norm_eq_or_eq_neg` により

$$
N(\gamma)=b
\quad\text{または}\quad
N(\gamma)=-b
$$

であるから、符号に関係なく

$$
q\mid b
$$

を得る。

一方、0278 `zeroSector_natAbs_product_eq` は

$$
|s|\,|H(r,s)|=5^6a^{10}
$$

を与える。`q | |s|` なので

$$
q\mid 5^6a^{10}.
$$

`q` は素数だから、

$$
q\mid 5^6
\quad\text{または}\quad
q\mid a^{10}.
$$

第一の場合は `q | 5`、したがって `q=5` となり、すでに得た `q | b` から `5 | b` が出る。しかし packet は `five_not_dvd_b : ¬ 5 ∣ b` を保持するので矛盾する。

第二の場合は `q | a` となる。すると `q | a` と `q | b` が同時に成立し、packet の `coprime_a_b : Nat.Coprime a b` に反する。

よって共通素因子 `q` は存在せず、`r` と `s` は互いに素である。

## 証明全体での役割

zero-sector descent では、第二座標 `s` と quartic factor

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s)
$$

を互いに素として分離し、最終的に

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}
$$

という tenth-power split を得たい。

本 theorem はその前段階として、fifth-power base 自身の座標 `(r,s)` が primitive であることを packet の `(a,b)` の互いに素性へ還元する。

直後の 0280 `SignedGoldenRamifierStrippedPacket.zeroSector_coprime_s_sndFactor` は本 theorem を直接使う。そこで仮に素数 `q` が `s` と `H(r,s)` をともに割るなら、`H(r,s)-r^4` が `s` の倍数であることから `q | r^4`、したがって `q | r` を得る。すると `q` が `r` と `s` の双方を割り、本 theorem の primitive condition と矛盾する。

したがって依存の流れは

$$
\text{0273, 0278 + packet coprimality}
\longrightarrow
\text{0279: }\gcd(|r|,|s|)=1
\longrightarrow
\text{0280: }\gcd(|s|,|H|)=1
\longrightarrow
\text{tenth-power split}
$$

となる。

## 直接依存する定義・補題

### `SignedGoldenRamifierStrippedPacket`

本 theorem の主要な入力構造。特に次を利用する。

- `p.exceptional.powerSplit.a`
- `p.exceptional.powerSplit.b`
- `p.exceptional.powerSplit.coprime_a_b`
- `p.five_not_dvd_b`

### `GoldenInt`

`gamma.fst`, `gamma.snd` の二整数座標を持つ golden order の元。

### `goldenNorm`

正本 source では座標表示

$$
N(r,s)=r^2+rs-s^2
$$

を持つ。本 proof は `simp only [goldenNorm]` でこの式を展開する。

### 0273 `zeroSector_gamma_norm_eq_or_eq_neg`

`goldenNorm gamma = ±b` を与え、共通素因子 `q` を packet の `b` へ移す。

### 0278 `zeroSector_natAbs_product_eq`

$$
|s|\,|H|=5^6a^{10}
$$

を与え、`q | s` から `q | 5^6a^{10}` を得るために使う。

### `Nat.Prime.not_coprime_iff_dvd`

`Nat.Coprime` の否定から、両方を割る共通素数 `q` を抽出する。

### `Int.natCast_dvd`

`q ∣ n.natAbs` という自然数可除性と `(q : ℤ) ∣ n` という整数可除性の橋渡しに使う。

### `Nat.Prime.dvd_mul` / `Nat.Prime.dvd_of_dvd_pow`

素数が積や冪を割る場合に、その素因子を base まで降ろす。

### `Nat.dvd_prime`

`q | 5` と 5 の素数性から `q=1 ∨ q=5` を得る。`q` 自身が prime なので `q=1` を除外し `q=5` を確定する。

### `Nat.not_coprime_of_dvd_of_dvd`

`q | a`, `q | b`, `1 < q` から `a,b` が coprime ではないことを与え、packet の `coprime_a_b` と衝突させる。

## 証明または構築の流れ

### 1. coprimality を否定して共通素数を取る

```lean
by_contra hcop
rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
  ⟨q, hqPrime, hqr, hqs⟩
```

これで

```lean
hqr : q ∣ gamma.fst.natAbs
hqs : q ∣ gamma.snd.natAbs
```

を得る。

### 2. `ℕ` の可除性を `ℤ` へ移す

```lean
have hqrZ : (q : ℤ) ∣ gamma.fst := Int.natCast_dvd.mpr hqr
have hqsZ : (q : ℤ) ∣ gamma.snd := Int.natCast_dvd.mpr hqs
```

### 3. norm を `q` が割ることを示す

`goldenNorm` を展開し、`r^2`, `rs`, `s^2` の各項が `q` の倍数であることを組み合わせる。

```lean
have hqNormZ : (q : ℤ) ∣ goldenNorm gamma := by
  simp only [goldenNorm]
  exact dvd_sub ...
```

### 4. norm の値から `q | b` を得る

0273 の二分岐を `rcases` し、負号の場合は `Int.dvd_neg.mp` で符号を除く。

```lean
rcases p.zeroSector_gamma_norm_eq_or_eq_neg hbeta with hn | hn
```

`exact_mod_cast` により整数可除性を自然数可除性へ戻す。

### 5. 0278 から `q | 5^6 a^10` を得る

```lean
have hprod := p.zeroSector_natAbs_product_eq hbeta
have hqRhs : q ∣ 5 ^ 6 * p.exceptional.powerSplit.a ^ 10 := by
  rw [← hprod]
  exact dvd_mul_of_dvd_left hqs _
```

### 6. prime divisor を二分する

```lean
rcases hqPrime.dvd_mul.mp hqRhs with hq5pow | hqapow
```

- `q | 5^6` なら `q | 5`、したがって `q=5`。これは `five_not_dvd_b` と矛盾。
- `q | a^10` なら `q | a`。`q | b` と合わせて `coprime_a_b` と矛盾。

これで背理法が閉じる。

## Lean 固有の処理

### `Nat.Coprime` の否定を common prime witness に変換

数学では「gcd が 1 でないなら共通素因子がある」と一言で済むが、Lean では `Nat.Prime.not_coprime_iff_dvd` が明示的 witness `q` と prime proof、二つの divisibility proof を供給する。この形が以降の prime splitting と非常に相性が良い。

### `natAbs` と整数可除性の往復

goal は `Nat.Coprime` なので自然数側で始まる一方、`goldenNorm` は整数式である。そのため

```lean
Int.natCast_dvd.mpr
```

と `exact_mod_cast` を使って `ℕ ↔ ℤ` の境界を往復する。

### `by decide` による指数の非零条件

`dvd_pow` の指数条件に対して

```lean
(by decide)
```

を使い、具体的指数 2 が 0 でないことを kernel 計算で処理している。

### `resolve_left hqPrime.ne_one`

`Nat.dvd_prime` は divisor が 1 または prime 自身であるという disjunction を返す。`q` が prime なので `q ≠ 1` を使い、`q=5` 側だけを残す。

## 冗長・重複箇所

proof は論理構造が明瞭で、重大な冗長性はない。ただし次の二点は定型処理である。

1. `q | r`, `q | s` から `q | goldenNorm gamma` を座標展開で直接組み立てている。
2. `q | 5^6 a^10` から `q=5` または `q | a` へ進む prime-factor splitting を局所的に記述している。

同種の descent proof が多数あるなら generic lemma 化の余地はあるが、本 theorem 単独では現行 proof の方が依存関係を追いやすい。

## 最適化候補

### 1. norm divisibility の補助 lemma 化

例えば

```lean
(q : ℤ) ∣ r → (q : ℤ) ∣ s →
(q : ℤ) ∣ goldenNorm ⟨r,s⟩
```

という project-level lemma が他所でも必要なら、`simp only [goldenNorm]` 以下を共通化できる。

ただし本実行では利用頻度を全 repository で網羅的に確認していないため、これは **候補** である。

### 2. `q | 5^6 * a^10` の分岐を抽象化

固定 prime 5 と tenth power を扱う同様の proof が複数ある場合、valuation または prime-divisor lemma にまとめられる可能性がある。ただし現 proof は 5 の exceptional role を明示しており、局所的可読性は高い。

### 3. `goldenNorm` を展開しない API

座標 primitive 性に関する補助 lemma を `GoldenInt` API として持てば、本 theorem が polynomial representation に直接依存せずに済む。これは abstraction barrier 改善として有望だが、Lean build を行っていないので具体形は未検証である。

## 必要 Mathlib import と import 最適化候補

対象ブランチの canonical standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` により全体をまとめている。

本 theorem が直接使う Mathlib 側の主要機構は、

- `Nat.Coprime`
- `Nat.Prime.not_coprime_iff_dvd`
- `Nat.Prime.dvd_mul`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.dvd_prime`
- `Nat.not_coprime_of_dvd_of_dvd`
- `Int.natCast_dvd`
- `Int.dvd_neg`
- `dvd_add`, `dvd_sub`, `dvd_pow`, `dvd_mul_of_dvd_left`
- `exact_mod_cast`
- `norm_num`

である。

project 側では少なくとも `SignedGoldenRamifierStrippedPacket`, `GoldenInt`, `goldenNorm`, 0273, 0278 と power-split fields が必要である。

ただし元 module の **最小 Mathlib import 集合は未確認** である。standalone artifact では `Mathlib` 一括 import を使用しており、本実行では Lean build を行わないため、import の削減案を検証済みとは主張しない。

## 既存 PDF との対応

対象ブランチの repository tree には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在する。

GitHub コネクタの repository-content API では PDF binary 本文を解析可能な形で取得できないため、本 theorem に対応する具体的ページ番号・節番号は **未確認** である。

したがって theorem-level の技術的記述は、`Flt5DkMath/FLT5StandAlone.lean` 内の生成区間 `DkMath/FLT/Five/SignedGoldenZeroSector.lean` を第一根拠としている。PDF の具体的位置は推測していない。

## Comparator challenge 化の可否

**適している。難度は中程度。**

challenge としては、次を既知として与えると良い。

- `p.zeroSector_gamma_norm_eq_or_eq_neg hbeta`
- `p.zeroSector_natAbs_product_eq hbeta`
- `p.exceptional.powerSplit.coprime_a_b`
- `p.five_not_dvd_b`

goal を

```lean
Nat.Coprime gamma.fst.natAbs gamma.snd.natAbs
```

とし、共通素数 witness の抽出、`ℕ → ℤ → ℕ` の cast、prime divisor splitting を学ばせる。

特に comparator では、

- gcd を直接計算する proof
- common-prime contradiction による proof

を比較すると、後者が packet の既存 API と自然に接続することが見えやすい。

## 次に読むべき宣言

次は **0280 `SignedGoldenRamifierStrippedPacket.zeroSector_coprime_s_sndFactor`** を読むべきである。

これは本 theorem の primitive coordinate condition を利用し、

$$
\gcd\bigl(|s|,|H(r,s)|\bigr)=1
$$

を証明する。具体的には共通素数 `q` が `s` と `H(r,s)` を割ると仮定し、quartic factor の形から `q | r^4`、素数性から `q | r` を得て、本 theoremの

$$
\gcd(|r|,|s|)=1
$$

と矛盾させる。

zero-sector tenth-power split に向けて、0279 が座標 primitive 性、0280 が実際の二因子の coprimality を担当するという綺麗な二段構成になっている。