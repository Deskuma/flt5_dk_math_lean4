# 0341 — `nonempty_even_factorData`

## 宣言種別

この宣言は **`private theorem`** である。

```lean
private theorem nonempty_even_factorData
    (p : GoldenZeroSectorInversionPacket) (hc : Even p.source.c) :
    Nonempty (GoldenZeroSectorFactorData p) := by
  rcases even_iff_two_dvd.mp hc with ⟨k, hk⟩
  let Q2 : ℕ := 5 ^ 5 * 2 ^ 7 * k ^ 8
  have hQ : zeroSectorQ p.source.c = 2 * Q2 := by
    unfold zeroSectorQ Q2
    rw [hk]
    ring
  have hQ2Even : Even Q2 := by
    rw [even_iff_two_dvd]
    dsimp [Q2]
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right (by norm_num : 2 ∣ 2 ^ 7) (5 ^ 5)) _
  obtain ⟨A1, B1, hA8, hB8, hparity⟩ := p.even_factor_eighths hc
  rcases hparity with ⟨hAodd, hBeven⟩ | ⟨hAeven, hBodd⟩
  · rcases even_iff_two_dvd.mp hBeven with ⟨B2, hB2⟩
    have hcop : Nat.Coprime A1 B2 := by
      apply coprime_of_odd_of_no_common_odd_prime hAodd
      intro q hq hq2 hqA1 hqB2
      apply p.no_common_odd_prime q hq hq2
      · rw [hA8]
        exact dvd_mul_of_dvd_right hqA1 8
      · rw [hB8, hB2]
        exact Nat.dvd_mul_left_of_dvd
          (Nat.dvd_mul_left_of_dvd hqB2 2) 8
    have hred : A1 * B2 = Q2 ^ 5 := by
      apply Nat.mul_left_cancel (show 0 < 128 by norm_num)
      calc
        128 * (A1 * B2) = p.source.A0 * p.source.B0 := by
          rw [hA8, hB8, hB2]
          ring
        _ = 4 * zeroSectorQ p.source.c ^ 5 := p.factor_product
        _ = 128 * Q2 ^ 5 := by rw [hQ]; ring
    obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := fifth_power_factor_split hcop hred
    have hePos : 0 < e := by
      by_contra he0
      have he0' : e = 0 := Nat.eq_zero_of_not_pos he0
      have hpos := p.A0_pos
      rw [hA8, he, he0'] at hpos
      norm_num at hpos
    have hfPos : 0 < f := by
      by_contra hf0
      have hf0' : f = 0 := Nat.eq_zero_of_not_pos hf0
      have hpos := p.B0_pos
      rw [hB8, hB2, hf, hf0'] at hpos
      norm_num at hpos
    have hef : Nat.Coprime e f := by
      have hpows : Nat.Coprime (e ^ 5) (f ^ 5) := by
        simpa [he, hf] using hcop
      exact (hpows.of_dvd_left (dvd_pow_self e (by decide))).of_dvd_right
        (dvd_pow_self f (by decide))
    have heOdd : Odd e := (Nat.odd_pow_iff (by decide)).mp (he ▸ hAodd)
    have hefQ2 : e * f = Q2 := by
      apply Nat.pow_left_injective (by decide : 5 ≠ 0)
      calc
        (e * f) ^ 5 = e ^ 5 * f ^ 5 := mul_pow e f 5
        _ = A1 * B2 := by rw [← he, ← hf]
        _ = Q2 ^ 5 := hred
    have hfEven : Even f := by
      have h2ef : 2 ∣ e * f := by
        rw [hefQ2]
        exact hQ2Even.two_dvd
      rcases (by norm_num : Nat.Prime 2).dvd_mul.mp h2ef with h2e | h2f
      · exact (heOdd.not_two_dvd_nat h2e).elim
      · exact even_iff_two_dvd.mpr h2f
    have hownership : 2 * (e * f) = zeroSectorQ p.source.c := by
      rw [hefQ2, hQ]
    have hdiff : e ^ 5 + p.source.d ^ 5 = 2 * f ^ 5 := by
      have hdifference := p.factor_difference
      rw [hA8, hB8, hB2, he, hf] at hdifference
      omega
    have hefd : Nat.Coprime (e * f) p.source.d :=
      p.coprime_Q_d.of_dvd_left ⟨2, by rw [← hownership]; ring⟩
    exact ⟨.evenLeftLow e f hePos hfPos hef hefd heOdd hfEven
      (by rw [hA8, he]) (by rw [hB8, hB2, hf]; ring)
      hownership hdiff⟩
  · rcases even_iff_two_dvd.mp hAeven with ⟨A2, hA2⟩
    have hcop : Nat.Coprime A2 B1 := by
      have hcop' : Nat.Coprime B1 A2 := by
        apply coprime_of_odd_of_no_common_odd_prime hBodd
        intro q hq hq2 hqB1 hqA2
        apply p.no_common_odd_prime q hq hq2
        · rw [hA8, hA2]
          exact Nat.dvd_mul_left_of_dvd
            (Nat.dvd_mul_left_of_dvd hqA2 2) 8
        · rw [hB8]
          exact dvd_mul_of_dvd_right hqB1 8
      exact hcop'.symm
    have hred : A2 * B1 = Q2 ^ 5 := by
      apply Nat.mul_left_cancel (show 0 < 128 by norm_num)
      calc
        128 * (A2 * B1) = p.source.A0 * p.source.B0 := by
          rw [hA8, hA2, hB8]
          ring
        _ = 4 * zeroSectorQ p.source.c ^ 5 := p.factor_product
        _ = 128 * Q2 ^ 5 := by rw [hQ]; ring
    obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := fifth_power_factor_split hcop hred
    have hePos : 0 < e := by
      by_contra he0
      have he0' : e = 0 := Nat.eq_zero_of_not_pos he0
      have hpos := p.A0_pos
      rw [hA8, hA2, he, he0'] at hpos
      norm_num at hpos
    have hfPos : 0 < f := by
      by_contra hf0
      have hf0' : f = 0 := Nat.eq_zero_of_not_pos hf0
      have hpos := p.B0_pos
      rw [hB8, hf, hf0'] at hpos
      norm_num at hpos
    have hef : Nat.Coprime e f := by
      have hpows : Nat.Coprime (e ^ 5) (f ^ 5) := by
        simpa [he, hf] using hcop
      exact (hpows.of_dvd_left (dvd_pow_self e (by decide))).of_dvd_right
        (dvd_pow_self f (by decide))
    have hfOdd : Odd f := (Nat.odd_pow_iff (by decide)).mp (hf ▸ hBodd)
    have hefQ2 : e * f = Q2 := by
      apply Nat.pow_left_injective (by decide : 5 ≠ 0)
      calc
        (e * f) ^ 5 = e ^ 5 * f ^ 5 := mul_pow e f 5
        _ = A2 * B1 := by rw [← he, ← hf]
        _ = Q2 ^ 5 := hred
    have heEven : Even e := by
      have h2ef : 2 ∣ e * f := by
        rw [hefQ2]
        exact hQ2Even.two_dvd
      rcases (by norm_num : Nat.Prime 2).dvd_mul.mp h2ef with h2e | h2f
      · exact even_iff_two_dvd.mpr h2e
      · exact (hfOdd.not_two_dvd_nat h2f).elim
    have hownership : 2 * (e * f) = zeroSectorQ p.source.c := by
      rw [hefQ2, hQ]
    have hdiff : 2 * e ^ 5 + p.source.d ^ 5 = f ^ 5 := by
      have hdifference := p.factor_difference
      rw [hA8, hA2, hB8, he, hf] at hdifference
      omega
    have hefd : Nat.Coprime (e * f) p.source.d :=
      p.coprime_Q_d.of_dvd_left ⟨2, by rw [← hownership]; ring⟩
    exact ⟨.evenRightLow e f hePos hfPos hef hefd heEven hfOdd
      (by rw [hA8, hA2, he]; ring) (by rw [hB8, hf])
      hownership hdiff⟩
```

## Lean の型

本体の型は

```lean
(p : GoldenZeroSectorInversionPacket) →
Even p.source.c →
Nonempty (GoldenZeroSectorFactorData p)
```

である。

`GoldenZeroSectorFactorData p` は `p` に依存する dependent inductive 型であり、この定理は `p.source.c` が偶数なら、その型の inhabitant が必ず存在することを示す。返り値が具体的な datum そのものではなく `Nonempty` なのは、後続で `Classical.choice` により一つ選択するためである。

## 数学的主張

偶数 branch では 0340 により

$$
p.source.A0 = 8A_1,
\qquad
p.source.B0 = 8B_1
$$

かつ $A_1,B_1$ は反対の parity を持つ。

一方、$c$ が偶数なので $c=2k$ と書ける。コードは

$$
Q_2 := 5^5 2^7 k^8
$$

を置き、`zeroSectorQ` を

$$
\operatorname{zeroSectorQ}(c)=2Q_2
$$

と書き直す。さらに $Q_2$ は明らかに偶数である。

ここから二つの場合に分かれる。

### 1. $A_1$ が奇数、$B_1$ が偶数

$B_1=2B_2$ と置き、

$$
\gcd(A_1,B_2)=1
$$

を示す。積公式から

$$
A_1B_2=Q_2^5
$$

を得るので `fifth_power_factor_split` により

$$
A_1=e^5,
\qquad
B_2=f^5
$$

と分解できる。

すると

$$
A_0=8e^5,
\qquad
B_0=16f^5.
$$

また $e$ は奇数で、$ef=Q_2$ は偶数だから、互いに素性と素数 2 の積への可除性を使って $f$ が偶数であることを強制する。差分公式から

$$
e^5+d^5=2f^5
$$

を得て、最終的に `GoldenZeroSectorFactorData.evenLeftLow` を構築する。

### 2. $A_1$ が偶数、$B_1$ が奇数

今度は $A_1=2A_2$ と置き、対称的に

$$
\gcd(A_2,B_1)=1,
\qquad
A_2B_1=Q_2^5
$$

を示して

$$
A_2=e^5,
\qquad
B_1=f^5
$$

へ分解する。

したがって

$$
A_0=16e^5,
\qquad
B_0=8f^5,
$$

$e$ は偶数、$f$ は奇数となり、差分式は

$$
2e^5+d^5=f^5
$$

になる。これが `GoldenZeroSectorFactorData.evenRightLow` である。

## 証明全体での役割

この定理は zero-sector inversion から exact factor packet へ進む even branch の本体である。

0339 `GoldenZeroSectorInversionPacket.eight_dvd_factors` が $A_0,B_0$ から共通の $2^3$ を取り出し、0340 `GoldenZeroSectorInversionPacket.even_factor_eighths` が quotient の parity を二分した。0341 はその parity 情報を使って偶数側から **さらに一つの 2 を取り出す**。この追加の 2 が

$$
(8,16)
\quad\text{または}\quad
(16,8)
$$

という非対称な二進係数を生み、`evenLeftLow` / `evenRightLow` の二 constructor に直接対応する。

したがって、0341 は「even である」という粗い分類を、後続 descent が利用できる **完全な証明付き factor certificate** に変換する層である。

## 直接依存する定義・補題

主要な直接依存は次の通りである。

- `GoldenZeroSectorInversionPacket.even_factor_eighths`
- `GoldenZeroSectorInversionPacket.no_common_odd_prime`
- `GoldenZeroSectorInversionPacket.factor_product`
- `GoldenZeroSectorInversionPacket.factor_difference`
- `GoldenZeroSectorInversionPacket.A0_pos`
- `GoldenZeroSectorInversionPacket.B0_pos`
- `GoldenZeroSectorInversionPacket.coprime_Q_d`
- `GoldenZeroSectorFactorData.evenLeftLow`
- `GoldenZeroSectorFactorData.evenRightLow`
- `zeroSectorQ`
- `coprime_of_odd_of_no_common_odd_prime`
- `fifth_power_factor_split`
- `even_iff_two_dvd`
- `Nat.Prime.dvd_mul`
- `Nat.odd_pow_iff`
- `Nat.pow_left_injective`
- `dvd_pow_self`

特に数学的な中心は `fifth_power_factor_split` であり、「互いに素な二因子の積が第五冪なら、それぞれが第五冪である」という既に形式化済みの分解原理を利用している。

## 証明の流れ

証明は次の順で進む。

1. `hc : Even c` から $c=2k$ を得る。
2. $Q_2=5^5 2^7 k^8$ を定義し、`zeroSectorQ c = 2 * Q2` と $Q_2$ の偶性を証明する。
3. 0340 から $A_0=8A_1$, $B_0=8B_1$ と opposite parity を得る。
4. parity の二場合に分岐する。
5. 偶数側をさらに 2 で割り、`B2` または `A2` を導入する。
6. `no_common_odd_prime` を使って reduced pair の互いに素性を証明する。
7. `factor_product` を 128 倍の等式へ正規化し、左消去して reduced product が $Q_2^5$ であることを示す。
8. `fifth_power_factor_split` により reduced factors を $e^5,f^5$ に分解する。
9. `A0_pos`,`B0_pos` から $e,f>0$ を回収する。
10. power-level coprimality から `Nat.Coprime e f` を回収する。
11. 奇数側の parity を `Nat.odd_pow_iff` で root へ降ろす。
12. $(ef)^5=Q_2^5$ の第五冪単射性から $ef=Q_2$ を示す。
13. $Q_2$ が偶数であることと素数 2 の `dvd_mul` から、残る root の偶性を強制する。
14. `2*(e*f)=zeroSectorQ c` を ownership として回収する。
15. `factor_difference` を書き換え、`omega` で branch 固有の第五冪方程式を得る。
16. `coprime_Q_d` から `Nat.Coprime (e*f) d` を引き戻す。
17. `.evenLeftLow` または `.evenRightLow` constructor を完成させる。

## Lean 固有の処理

### `Nonempty` による existence の包装

返り値は

```lean
Nonempty (GoldenZeroSectorFactorData p)
```

であり、constructive に得た datum を `⟨...⟩` で `Nonempty` に包む。後続の `nonempty_factorData` と `Classical.choice` に適した API になっている。

### `let Q2` と `unfold`

`Q2` は局所定義として置かれ、`hQ` では

```lean
unfold zeroSectorQ Q2
```

により両者を明示的な多項式へ展開してから `ring` で閉じる。

### 可除性 witness の逐次展開

`even_iff_two_dvd.mp` によって `Even n` を `2 ∣ n` へ変換し、`⟨B2,hB2⟩` や `⟨A2,hA2⟩` という quotient witness を直接取り出している。

### 128 の左消去

reduced product の等式では

```lean
apply Nat.mul_left_cancel (show 0 < 128 by norm_num)
```

としている。$8\cdot16=128$ が二 branch 共通の normalization coefficient であるためである。

### 第五冪の単射性

`ef = Q2` は自然数の積を直接操作するのではなく

```lean
apply Nat.pow_left_injective (by decide : 5 ≠ 0)
```

により第五冪を比較して回収する。これは `hred` と `mul_pow` をそのまま再利用できる Lean らしい経路である。

### parity の root への降下

`A1=e^5` と `Odd A1` から `Odd e` を得る部分は

```lean
(Nat.odd_pow_iff (by decide)).mp
```

を用いる。同様に右 branch では `B1=f^5` から `Odd f` を得る。

### `omega` と `ring` の役割分担

`ring` は積・冪係数の恒等式整理、`omega` は書き換え後の自然数線形算術に使用されている。第五冪そのものは atom として扱われるため、`omega` が非線形冪を展開しているわけではない。

## 冗長・重複箇所

二 branch は高度に対称であり、以下がほぼ重複している。

- reduced pair の coprimality 証明
- `hred` の構築
- `e,f` の正性証明
- root-level coprimality の回収
- `ef = Q2` の証明
- 偶数 root の決定
- ownership の構築
- `coprime_ef_d` の回収

ただし左右で `A1/B2` と `A2/B1` の順序、奇数 root の位置、最終 constructor が異なるため、完全に同一コードへ潰すには branch orientation を抽象化する補助構造が必要になる。

## 最適化候補

最も有力なのは even branch 共通の reduced-factor lemma を抽出することである。例えば、

- odd factor `O`
- even factor `E=2E₂`
- product relation
- source factor embedding

を入力し、

$$
O=e^5,
\qquad
E_2=f^5,
\qquad
\gcd(e,f)=1,
\qquad
ef=Q_2
$$

までを一括して返す補題があれば、0341 本体は branch orientation と最終差分方程式の処理だけになる。

また `hePos` / `hfPos` の証明も「正の係数倍が正なら第五冪 root は正」という汎用補題に切り出せる可能性がある。

一方、現状の実装は左右の数学的対応がコード上で非常に明瞭であり、証明 museum の可読性という観点では、ある程度の重複を残す利点もある。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

この定理が直接利用する Mathlib 側機能として少なくとも次が見える。

- `Even`, `Odd`, `even_iff_two_dvd`
- `Nat.Coprime`
- `Nat.Prime.dvd_mul`
- `Nat.odd_pow_iff`
- `Nat.pow_left_injective`
- `Nat.eq_zero_of_not_pos`
- `Nat.mul_left_cancel`
- `dvd_pow_self`
- `norm_num`
- `ring`
- `omega`

ただし、元の個別 source module の import 宣言はこの generated standalone 断片だけからは確認していない。また本作業では Lean ビルドを行わないため、これらを満たす **最小 import 集合は未確定** である。`import Mathlib` からの削減候補は存在するが、実際の最小化は別途 import audit と build 検証を伴うべきである。

## Comparator challenge 化の可否

**適している。特に中〜上級 challenge として良い。**

候補は二段階ある。

1. `even_factor_eighths` と product relation を与え、左右いずれかの reduced product が第五冪になることを証明させる challenge。
2. `fifth_power_factor_split` まで与えたうえで、parity・ownership・difference を回収し `.evenLeftLow` / `.evenRightLow` を完成させる challenge。

後者は dependent constructor、可除性、coprimality、parity、`omega`、`ring`、power injectivity を一度に扱うため、Comparator 用の実践的な Lean proof-refactoring 課題として価値が高い。

## 次に読むべき宣言

次は **0342 `nonempty_factorData`** である。宣言種別は **`private theorem`**。

```lean
private theorem nonempty_factorData (p : GoldenZeroSectorInversionPacket) :
    Nonempty (GoldenZeroSectorFactorData p) := by
  rcases Nat.even_or_odd p.source.c with hc | hc
  · exact nonempty_even_factorData p hc
  · exact nonempty_odd_factorData p hc
```

0341 までで odd / even の双方について exact factor data の存在が構築されたため、0342 は `Nat.even_or_odd p.source.c` で二者を統合し、無条件の `Nonempty (GoldenZeroSectorFactorData p)` を得る小さな routing theorem となる。