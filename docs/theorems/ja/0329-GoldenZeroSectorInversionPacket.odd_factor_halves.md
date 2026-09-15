# 0329 — `GoldenZeroSectorInversionPacket.odd_factor_halves`

## 宣言種別

この宣言は **`theorem`** である。

`GoldenZeroSectorInversionPacket` に属する公開定理であり、`c` が奇数である零セクター反転 packet に対して、自然数因子 `A0`, `B0` がともに **ちょうど一つだけ因子 2 を持つ** ことを証明する。

## Lean の型

```lean
/-- In the odd-`c` branch, each inversion factor has exactly one factor of two. -/
theorem GoldenZeroSectorInversionPacket.odd_factor_halves
    (p : GoldenZeroSectorInversionPacket) (hc : Odd p.source.c) :
    ∃ A1 B1 : ℕ,
      p.source.A0 = 2 * A1 ∧ Odd A1 ∧
      p.source.B0 = 2 * B1 ∧ Odd B1 := by
  have hQodd : Odd (zeroSectorQ p.source.c) := by
    unfold zeroSectorQ
    exact (show Odd (5 ^ 5) by norm_num).mul hc.pow
  have hRhsNotEight : ¬ 8 ∣ 4 * zeroSectorQ p.source.c ^ 5 := by
    intro h8
    rcases h8 with ⟨k, hk⟩
    have h2Q : 2 ∣ zeroSectorQ p.source.c ^ 5 := by
      refine ⟨k, ?_⟩
      omega
    exact hQodd.pow.not_two_dvd_nat h2Q
  have h2Product : 2 ∣ p.source.A0 * p.source.B0 := by
    rw [p.factor_product]
    exact dvd_mul_of_dvd_left (by norm_num) _
  have h2Diff : 2 ∣ 8 * p.source.d ^ 5 := by
    exact dvd_mul_of_dvd_left (by norm_num) _
  have hEven : 2 ∣ p.source.A0 ∧ 2 ∣ p.source.B0 := by
    rcases (by norm_num : Nat.Prime 2).dvd_mul.mp h2Product with hA | hB
    · exact ⟨hA, by rw [p.factor_difference]; exact dvd_add hA h2Diff⟩
    · have hsum : 2 ∣ p.source.A0 + 8 * p.source.d ^ 5 := by
        simpa [p.factor_difference] using hB
      exact ⟨(Nat.dvd_add_left h2Diff).mp hsum, hB⟩
  have hNotFourA : ¬ 4 ∣ p.source.A0 := by
    intro h4A
    have h4Diff : 4 ∣ 8 * p.source.d ^ 5 :=
      dvd_mul_of_dvd_left (by norm_num) _
    have h4B : 4 ∣ p.source.B0 := by
      rw [p.factor_difference]
      exact dvd_add h4A h4Diff
    have h16Product : 16 ∣ p.source.A0 * p.source.B0 := by
      simpa using Nat.mul_dvd_mul h4A h4B
    have h8Product : 8 ∣ p.source.A0 * p.source.B0 :=
      (by norm_num : 8 ∣ 16).trans h16Product
    rw [p.factor_product] at h8Product
    exact hRhsNotEight h8Product
  have hNotFourB : ¬ 4 ∣ p.source.B0 := by
    intro h4B
    have h4Diff : 4 ∣ 8 * p.source.d ^ 5 :=
      dvd_mul_of_dvd_left (by norm_num) _
    have hsum : 4 ∣ p.source.A0 + 8 * p.source.d ^ 5 := by
      simpa [p.factor_difference] using h4B
    have h4A : 4 ∣ p.source.A0 := (Nat.dvd_add_left h4Diff).mp hsum
    exact hNotFourA h4A
  obtain ⟨A1, hA, hAodd⟩ :=
    exists_eq_two_mul_odd_of_two_dvd_not_four_dvd hEven.1 hNotFourA
  obtain ⟨B1, hB, hBodd⟩ :=
    exists_eq_two_mul_odd_of_two_dvd_not_four_dvd hEven.2 hNotFourB
  exact ⟨A1, B1, hA, hAodd, hB, hBodd⟩
```

## 数学的主張

仮定は `hc : Odd p.source.c`、すなわち $c$ が奇数であることである。

結論は、ある自然数 $A_1,B_1$ が存在して

$$
A_0=2A_1,
\qquad
B_0=2B_1,
$$

かつ $A_1,B_1$ がともに奇数になることである。

したがって二進付値の言葉では

$$
v_2(A_0)=v_2(B_0)=1
$$

という内容に相当する。Lean の定理自体は `padicValNat` 等を使わず、`2 ∣ n` と `¬ 4 ∣ n` の組としてこれを証明している。

## 証明全体での役割

零セクター反転 packet には既に

$$
A_0B_0=4Q^5,
$$

$$
B_0=A_0+8d^5,
$$

が保存されている。ここで

$$
Q=5^5c^8.
$$

$c$ が奇数なら $Q$ も奇数である。したがって右辺 $4Q^5$ の二進因子はちょうど $2^2$ だけである。

一方、差 $B_0-A_0=8d^5$ は 2 で割れるため、$A_0$ と $B_0$ は同じ偶奇を持つ。積が 4 を含むので両者は偶数でなければならない。さらに片方が 4 で割れれば差から他方も 4 で割れ、積が 16 で割れてしまう。しかし $4Q^5$ は $Q$ が奇数なので 8 ですら割れない。よって両者とも 4 では割れない。

以上から各因子は

$$
2\mid A_0,
\quad 4\nmid A_0,
\qquad
2\mid B_0,
\quad 4\nmid B_0
$$

を満たし、0327 `exists_eq_two_mul_odd_of_two_dvd_not_four_dvd` によりそれぞれ `2 × odd` に正規化される。

この定理は後続の odd branch factorization で $A_1,B_1$ を導入する入口であり、0328 `no_common_odd_prime` と 0326 `coprime_of_odd_of_no_common_odd_prime` を組み合わせて `Nat.Coprime A1 B1` を得るための前処理である。

## 直接依存する定義・補題

### `GoldenZeroSectorInversionPacket`

使用する主要 field は次である。

- `p.factor_product`
- `p.factor_difference`
- `p.source.A0`
- `p.source.B0`
- `p.source.c`
- `p.source.d`

### `zeroSectorQ`

定義を `unfold zeroSectorQ` し、$Q=5^5c^8$ の奇性を `hc` から導く。

### 0327 `exists_eq_two_mul_odd_of_two_dvd_not_four_dvd`

今回の最後で直接二度使われる private theorem である。

$$
2\mid n,
\quad 4\nmid n
\Longrightarrow
\exists m,\ n=2m\land Odd(m).
$$

### Mathlib の主な道具

- `Odd.mul`, `Odd.pow`
- `Odd.not_two_dvd_nat`
- `Nat.Prime.dvd_mul`
- `Nat.mul_dvd_mul`
- `dvd_mul_of_dvd_left`
- `dvd_add`
- `Nat.dvd_add_left`
- `Nat.Dvd.trans`
- `norm_num`
- `simpa`
- `omega`

## 証明または構築の流れ

### 1. `Q` が奇数であることを示す

`zeroSectorQ` を展開すると $5^5c^8$ である。$5^5$ は奇数であり、`hc.pow` から $c^8$ も奇数なので

$$
Q\text{ は奇数}
$$

を得る。

### 2. `4Q^5` は 8 で割れないことを固定する

仮に

$$
8\mid4Q^5
$$

なら、商の存在を展開して `omega` により

$$
2\mid Q^5
$$

を作れる。しかし $Q$ は奇数なので $Q^5$ も奇数であり矛盾する。

この `hRhsNotEight` が後半の二進上限を担う。

### 3. `A0`, `B0` がともに偶数であることを示す

積恒等式から

$$
2\mid A_0B_0
$$

を得る。2 は素数なので `Nat.Prime.dvd_mul` により $2\mid A_0$ または $2\mid B_0$。

差項 $8d^5$ も 2 で割れるので、

$$
B_0=A_0+8d^5
$$

を使えば、片方の偶数性から他方の偶数性が従う。これで `hEven` を構成する。

### 4. `A0` は 4 で割れない

$4\mid A_0$ と仮定する。$4\mid8d^5$ なので差恒等式から $4\mid B_0$ も得る。

すると

$$
16\mid A_0B_0
$$

であり、特に $8\mid A_0B_0$。積恒等式で右辺へ書き換えると $8\mid4Q^5$ となり、`hRhsNotEight` に矛盾する。

### 5. `B0` は 4 で割れない

これは対称的だが、完全に同じ証明を繰り返さず、$4\mid B_0$ から差恒等式により $4\mid A_0$ を導いて、直前の `hNotFourA` に矛盾させる。

### 6. 両因子を `2 × odd` へ正規化する

0327 を

- `hEven.1`, `hNotFourA`
- `hEven.2`, `hNotFourB`

へ適用し、$A_1,B_1$ とその奇性を得る。最後に存在量をまとめて返す。

## Lean 固有の処理

### `Odd` を二進可除性の否定として使う

Lean では奇性を `Odd n` として保持し、必要な箇所だけ `not_two_dvd_nat` により `¬ 2 ∣ n` へ変換している。二進付値を導入せず、Elementary な可除性 API だけで閉じている点が特徴である。

### `rcases (by norm_num : Nat.Prime 2).dvd_mul.mp ...`

素数 2 が積を割ることから左右どちらかを割る、という Euclid の補題を直接使っている。数学上の「積が偶数なら少なくとも一方は偶数」に対応する。

### `simpa [p.factor_difference] using hB`

`p.factor_difference` を rewrite rule として `simpa` に渡し、`B0` の可除性を `A0 + 8d^5` の可除性へ形だけ変換している。

### `omega`

`8 ∣ 4Q^5` の witness 展開後に `2 ∣ Q^5` の witness を作る箇所で、定数係数の線形整数算術を処理するために使われる。

## 冗長・重複箇所

`A0` と `B0` の偶数性、および 4 非可除性は本質的に対称である。ただし現行証明では、差恒等式が `B0 = A0 + ...` という方向を持つため完全な左右対称コードにはなっていない。

`h4Diff : 4 ∣ 8 * d^5` は `hNotFourA` と `hNotFourB` の双方で再構築されており、局所的には重複している。

また `2 ∣ 8*d^5` と `4 ∣ 8*d^5` はどちらも数値係数だけから即座に得られるため、二進可除性の補助情報を先にまとめて持つ設計も可能である。

## 最適化候補

### 1. 二進付値を用いた短縮

数学的には

$$
v_2(A_0)+v_2(B_0)=2
$$

かつ $A_0\equiv B_0\pmod 8$ に近い差情報から、両者の付値が 1 と直ちに決まる。Mathlib の `padicValNat` 系 API を導入すれば証明を概念的に短くできる可能性がある。

ただし現在の elementary な証明は依存が軽く、後続の `Odd` API と直接接続する利点があるため、必ずしも置換が優位とは限らない。

### 2. `hRhsNotEight` の一般補題化

「`Q` が奇数なら `¬ 8 ∣ 4 * Q^5`」は指数 5 に本質的ではなく、より一般に奇数 `u` に対して `¬ 8 ∣ 4*u` として切り出せる。二進 branch の他箇所で同形処理があるなら再利用価値が高い。

### 3. `h4Diff` の共有

`have h4Diff : 4 ∣ 8 * p.source.d ^ 5 := ...` を `hNotFourA` より前に一度だけ置けば、小さいながら重複を除ける。

## 必要 Mathlib import と import 最適化候補

standalone 正本は `import Mathlib` を使用している。

この theorem が実際に必要とする機能は主に

- 自然数の可除性・素数
- parity (`Odd`, `Even`)
- `norm_num`
- `omega`

である。したがって standalone 全体を分割する場合には、`Mathlib` 一括 import から NumberTheory/Prime、Parity、`Mathlib.Tactic.Omega`、`Mathlib.Tactic.NormNum` 周辺の個別 import へ縮小できる可能性がある。

ただし正確な最小 import 集合はこの実行では Lean ビルドによる検証を行っていないため、 **最適化候補** とする。

## Comparator challenge 化の可否

**可能。適性は高い。**

入力として

- $A_0B_0=4Q^5$
- $B_0=A_0+8d^5$
- `Odd Q`

を与え、出力として

$$
\exists A_1 B_1,
A_0=2A_1\land Odd(A_1)\land
B_0=2B_1\land Odd(B_1)
$$

を要求すれば、可除性・偶奇・積の素因子分配を組み合わせる良い challenge になる。

特に「積に $2^2$ しかない」「差には $2^3$ がある」という二つの情報から個々の二進付値を決定する設計が核心であり、単純な tactic 問題ではなく構造把握を要求できる。

## 次に読むべき宣言

次は 0330 `GoldenZeroSectorInversionPacket.coprime_Q_d` を読むべきである。

```lean
theorem GoldenZeroSectorInversionPacket.coprime_Q_d
    (p : GoldenZeroSectorInversionPacket) :
    Nat.Coprime (zeroSectorQ p.source.c) p.source.d := by
  have h5d : Nat.Coprime 5 p.source.d :=
    (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr p.five_not_dvd_d
  unfold zeroSectorQ
  exact (h5d.pow_left 5).mul_left (p.coprime_c_d.pow_left 8)
```

これは $Q=5^5c^8$ と $d$ の互いに素性を packet の既存条件から合成し、後続の factor ownership と `coprime_ef_d` を支える定理である。
