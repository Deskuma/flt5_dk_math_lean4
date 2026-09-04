# 0280 — `SignedGoldenRamifierStrippedPacket.zeroSector_coprime_s_sndFactor`

## 宣言種別

これは **`theorem`** である。

zero sector の fifth-power base `gamma : GoldenInt` について、第二座標 `gamma.snd` と fifth-power の第二座標に現れる quartic factor `goldenFifthSndFactor gamma.fst gamma.snd` が、自然数絶対値として互いに素であることを示す。

## Lean の型

```lean
/-- The primitive coordinate condition makes `s` coprime to its quartic factor. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_coprime_s_sndFactor
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    Nat.Coprime gamma.snd.natAbs
      (goldenFifthSndFactor gamma.fst gamma.snd).natAbs := by
  by_contra hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
    ⟨q, hqPrime, hqs, hqH⟩
  have hqsZ : (q : ℤ) ∣ gamma.snd := Int.natCast_dvd.mpr hqs
  have hqHZ : (q : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd :=
    Int.natCast_dvd.mpr hqH
  have hqR4 : (q : ℤ) ∣ gamma.fst ^ 4 := by
    have htail : (q : ℤ) ∣
        goldenFifthSndFactor gamma.fst gamma.snd - gamma.fst ^ 4 := by
      rcases hqsZ with ⟨k, hk⟩
      refine ⟨k * (2 * gamma.fst ^ 3 + 4 * gamma.fst ^ 2 * gamma.snd +
        3 * gamma.fst * gamma.snd ^ 2 + gamma.snd ^ 3), ?_⟩
      simp only [goldenFifthSndFactor]
      rw [hk]
      ring
    have h := dvd_sub hqHZ htail
    ring_nf at h
    exact h
  have hqr4 : q ∣ gamma.fst.natAbs ^ 4 := by
    simpa [Int.natAbs_pow] using Int.natCast_dvd.mp hqR4
  have hqr : q ∣ gamma.fst.natAbs := hqPrime.dvd_of_dvd_pow hqr4
  exact (Nat.not_coprime_of_dvd_of_dvd hqPrime.one_lt hqr hqs)
    (p.zeroSector_coprime_coords hbeta)
```

`gamma = (r,s)` とし、

```lean
goldenFifthSndFactor r s
```

を `H(r,s)` と書けば、結論は

$$
\gcd\bigl(|s|,|H(r,s)|\bigr)=1.
$$

ここで

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4.
$$

## 数学的主張の意味

この quartic factor は `s` を法として非常に単純になる。

$$
H(r,s)-r^4
= s\bigl(2r^3+4r^2s+3rs^2+s^3\bigr).
$$

したがって

$$
H(r,s)\equiv r^4\pmod{s}.
$$

ここで `|s|` と `|H(r,s)|` が互いに素でないと仮定する。すると、それらをともに割る素数 `q` が存在する。

$$
q\mid s,
\qquad
q\mid H(r,s).
$$

上の合同式から

$$
q\mid r^4
$$

となり、`q` は素数なので

$$
q\mid r.
$$

よって `q` は `r` と `s` の双方を割る。しかし 0279 `zeroSector_coprime_coords` は

$$
\gcd(|r|,|s|)=1
$$

を保証しているので矛盾する。

したがって

$$
\gcd\bigl(|s|,|H(r,s)|\bigr)=1
$$

である。

## 証明全体での役割

0278 では zero-sector product equation が自然数絶対値へ移され、

$$
|s|\,|H(r,s)|=5^6a^{10}
$$

という積等式が得られた。

この積を tenth powers に分離するためには、左辺の二因子が互いに素であることが必要になる。0279 はまず fifth-power base 自身の座標について

$$
\gcd(|r|,|s|)=1
$$

を確立した。本 theorem 0280 は、その primitive condition を quartic factor へ転送して

$$
\gcd(|s|,|H|)=1
$$

を得る。

直後の 0281 `SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split` は本 theorem を直接使用する。そこで `5^6` を `|s|` 側へ完全に移した後、

$$
|s|=5^6t,
\qquad
tH=a^{10}
$$

とし、本 theorem から `t` と `H` も互いに素であることを得る。その coprime product が tenth power なので、両因子がそれぞれ tenth power になる。

したがって依存の流れは

$$
\text{0278: }|s||H|=5^6a^{10}
\longrightarrow
\text{0279: }\gcd(|r|,|s|)=1
\longrightarrow
\text{0280: }\gcd(|s|,|H|)=1
\longrightarrow
\text{0281: tenth-power split}
$$

となる。

## 直接依存する定義・補題

### `goldenFifthSndFactor`

正本では

```lean
def goldenFifthSndFactor (r s : ℤ) : ℤ :=
  r ^ 4 + 2 * r ^ 3 * s + 4 * r ^ 2 * s ^ 2 +
    3 * r * s ^ 3 + s ^ 4
```

と定義される。本 theorem はこの多項式を展開して、`r^4` 以外の全項に `s` が含まれることを使う。

### 0279 `SignedGoldenRamifierStrippedPacket.zeroSector_coprime_coords`

```lean
Nat.Coprime gamma.fst.natAbs gamma.snd.natAbs
```

を与える、本 theorem の最終矛盾先である。

### `Nat.Prime.not_coprime_iff_dvd`

`Nat.Coprime` の否定から、両方を割る共通素数 `q` を取り出す。

### `Int.natCast_dvd`

自然数絶対値での可除性

```lean
q ∣ x.natAbs
```

を整数での

```lean
(q : ℤ) ∣ x
```

へ移すために使う。また `hqR4` を自然数側へ戻す箇所でも逆向きに使う。

### `dvd_sub`

`q | H` と `q | (H-r^4)` から `q | r^4` を得る。

### `Nat.Prime.dvd_of_dvd_pow`

`q | |r|^4` から `q | |r|` を得る。

### `Nat.not_coprime_of_dvd_of_dvd`

`q | |r|`, `q | |s|`, `1 < q` から `|r|` と `|s|` が coprime でないことを作り、0279 と衝突させる。

## 証明または構築の流れ

### 1. coprimality を否定して共通素数を取る

```lean
by_contra hcop
rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
  ⟨q, hqPrime, hqs, hqH⟩
```

これで

```lean
hqs : q ∣ gamma.snd.natAbs
hqH : q ∣ (goldenFifthSndFactor ...).natAbs
```

を得る。

### 2. 自然数可除性を整数へ移す

```lean
have hqsZ : (q : ℤ) ∣ gamma.snd := Int.natCast_dvd.mpr hqs
have hqHZ : (q : ℤ) ∣ goldenFifthSndFactor ... :=
  Int.natCast_dvd.mpr hqH
```

quartic factor は `ℤ` 上の多項式なので、ここから整数側で処理する。

### 3. `H-r^4` が `q` で割れることを明示的 witness で示す

`hqsZ` を

```lean
rcases hqsZ with ⟨k, hk⟩
```

として `s = q*k` の witness を取り出し、

```lean
refine ⟨k * (2 * r^3 + 4 * r^2 * s + 3 * r * s^2 + s^3), ?_⟩
```

という quotient を直接与える。

これは恒等式

$$
H-r^4=s(2r^3+4r^2s+3rs^2+s^3)
$$

を Lean の divisibility witness としてそのまま記述したものになっている。

### 4. `q | r^4` を得る

```lean
have h := dvd_sub hqHZ htail
ring_nf at h
exact h
```

`dvd_sub` がまず `q | H-(H-r^4)` を与え、`ring_nf` がその差を `r^4` に正規化する。

### 5. `ℤ` の可除性を `ℕ` の `natAbs` へ戻す

```lean
have hqr4 : q ∣ gamma.fst.natAbs ^ 4 := by
  simpa [Int.natAbs_pow] using Int.natCast_dvd.mp hqR4
```

### 6. prime divisor を冪から base へ降ろす

```lean
have hqr : q ∣ gamma.fst.natAbs := hqPrime.dvd_of_dvd_pow hqr4
```

### 7. 0279 と衝突させる

```lean
exact (Nat.not_coprime_of_dvd_of_dvd hqPrime.one_lt hqr hqs)
  (p.zeroSector_coprime_coords hbeta)
```

共通素数 `q` が `|r|` と `|s|` の両方を割るため、0279 の primitive coordinate condition に反する。

## Lean 固有の処理

### `Nat.Coprime` から common-prime witness への反証形

数学では gcd を直接扱ってもよいが、Lean proof は `Nat.Prime.not_coprime_iff_dvd` で共通素数を即座に取り出す。この形にすると `dvd_of_dvd_pow` が直接利用でき、証明が valuation 的な流れになる。

### `natAbs` と `ℤ` の往復

結論は `Nat.Coprime` なので `ℕ` 側だが、多項式 `goldenFifthSndFactor` は `ℤ` 上で定義されている。そのため proof は

$$
\mathbb N \to \mathbb Z \to \mathbb N
$$

と可除性を往復する。`Int.natCast_dvd` と `Int.natAbs_pow` がこの型境界を処理している。

### divisibility witness の手書き

`htail` では `s | H-r^4` という一般補題を先に作らず、`q | s` の witness `k` を展開して直接 quotient を構成している。kernel が確認する等式は最後に `ring` が閉じる。

### `ring_nf` による差の正規化

`dvd_sub hqHZ htail` の結果は syntactic には `H-(H-r^4)` の可除性である。`ring_nf at h` によって `r^4` へ正規化している。

## 冗長・重複箇所

証明は比較的短く、論理的な重複はほとんどない。ただし、次の部分は独立した再利用可能な算術補題として切り出せる。

```lean
(gamma.snd : ℤ) ∣
  goldenFifthSndFactor gamma.fst gamma.snd - gamma.fst ^ 4
```

数学的には単に

$$
H(r,s)\equiv r^4\pmod{s}
$$

であり、zero-sector packet には依存しない純粋な polynomial lemma である。

現 proof は `q | s` を先に受け取ってから quotient を構成しているため、この合同構造が theorem 名として表面化していない。

## 最適化候補

### 1. `goldenFifthSndFactor` の mod-`s` 補題を独立化する

例えば

```lean
theorem goldenFifthSndFactor_sub_fst_pow_four_dvd_snd (r s : ℤ) :
    s ∣ goldenFifthSndFactor r s - r ^ 4 := by
  refine ⟨2 * r ^ 3 + 4 * r ^ 2 * s + 3 * r * s ^ 2 + s ^ 3, ?_⟩
  simp [goldenFifthSndFactor]
  ring
```

のような補題があれば、`htail` は `hqsZ.trans ...` に近い一行へ圧縮できる。

これは theorem 自体の数学的意味も明確にするため、最も自然な refactoring 候補である。

### 2. generic coprime-transfer lemma 化

一般に `H(r,s) ≡ r^n (mod s)` かつ `gcd(r,s)=1` なら `gcd(s,H)=1` である。この形式を generic lemma にすると、本 theorem は polynomial congruence と 0279 を渡すだけになる。

ただし、この抽象化が repository 内で複数回再利用されるかは本実行では網羅確認していないため、現段階では **候補** に留める。

### 3. `dvd_sub` 後の `ring_nf` を避ける

上記 mod-`s` lemma を用いれば `H-r^4` の形を意図的に保持できるため、`dvd_sub` と `ring_nf` の組合せもより直接的な `dvd_add_iff_left` / congruence API へ置き換えられる可能性がある。ただし可読性は現 proof も十分高い。

## 必要 Mathlib import と import 最適化候補

対象ブランチの standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用しており、この状態で本 theorem を含む全生成 source を束ねている。

本 theorem が直接使用する Mathlib 側の主要 API / tactic は少なくとも次である。

- `Nat.Coprime`
- `Nat.Prime.not_coprime_iff_dvd`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.not_coprime_of_dvd_of_dvd`
- `Int.natCast_dvd`
- `Int.natAbs_pow`
- `dvd_sub`
- `ring`
- `ring_nf`

ただし standalone は source modules の import を平坦化した生成 artifact であり、元の `DkMath/FLT/Five/SignedGoldenZeroSector.lean` の正確な import 行はこのリポジトリ内の standalone からは復元できない。そのため **最小 Mathlib import 集合は未確認** である。

import 最適化を行うなら、元 source module 上で `import Mathlib` を細分化し、`lake build` または Lean elaboration で検証する必要がある。本タスクでは Lean build を行わない指定なので、具体的な最小 import 名を断定しない。

## Comparator challenge 化の可否

**適している。難度は中程度。**

理由は、最終 theorem 自体は短い一方、Lean で次の三つの境界処理を正確に組み合わせる必要があるためである。

1. `¬ Nat.Coprime` から共通素数 witness を抽出する。
2. `natAbs` 上の可除性を `ℤ` 上の quartic polynomial へ移す。
3. `H(r,s) ≡ r^4 (mod s)` から prime divisor を `r` へ戻し、primitive condition と矛盾させる。

challenge としては、次の依存だけを与える構成が自然である。

```lean
p.zeroSector_coprime_coords hbeta
```

および `goldenFifthSndFactor` の定義、標準 Mathlib divisibility API を使用可能とし、本 theorem を再構成させる。

より数学中心の challenge にするなら、まず

```lean
s ∣ goldenFifthSndFactor r s - r ^ 4
```

を補助問題として証明させ、その後 coprimality transfer を完成させる二段構成がよい。

## PDF との対応

対象ブランチの repository tree には次の既存 PDF が存在することを確認した。

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

ただし本実行の GitHub コネクタは binary PDF 本文を UTF-8 text として取得できず、Web 経由の PDF 取得も成功しなかった。このため **0280 に対応する PDF の具体的ページ、節番号、記述との逐語的対応は確認できていない**。ここでの数学的・Lean 技術的説明は、対象ブランチの Lean 正本 `Flt5DkMath/FLT5StandAlone.lean` と既存 theorem museum の依存順を根拠としている。

PDF に存在する内容を推測で補ってはいない。

## 次に読むべき宣言

次は 0281

```lean
SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split
```

である。

型は

```lean
theorem SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    ∃ c d : ℕ,
      gamma.snd.natAbs = 5 ^ 6 * c ^ 10 ∧
      (goldenFifthSndFactor gamma.fst gamma.snd).natAbs = d ^ 10 := by
  ...
```

0280 までで整えた

$$
|s||H|=5^6a^{10},
\qquad
5\nmid H,
\qquad
\gcd(|s|,|H|)=1
$$

を実際に使用し、

$$
|s|=5^6c^{10},
\qquad
|H|=d^{10}
$$

という exact tenth-power split を構築する。zero-sector arithmetic の一つの大きな到達点であり、その次の inversion layer への入力になる。