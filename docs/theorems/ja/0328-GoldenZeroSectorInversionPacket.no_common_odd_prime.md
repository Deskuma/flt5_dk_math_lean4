# 0328 — `GoldenZeroSectorInversionPacket.no_common_odd_prime`

## 宣言種別

この宣言は **`theorem`** である。

`GoldenZeroSectorInversionPacket` に属する公開定理であり、零セクター反転で得られた自然数因子 `A0`, `B0` が **共通の奇素因子を持たない** ことを証明する。

## Lean の型

```lean
/-- The positive inversion factors have no common odd prime divisor. -/
theorem GoldenZeroSectorInversionPacket.no_common_odd_prime
    (p : GoldenZeroSectorInversionPacket)
    (q : ℕ) (hq : Nat.Prime q) (hq2 : q ≠ 2)
    (hqA : q ∣ p.source.A0) (hqB : q ∣ p.source.B0) : False := by
  have hqDiff : q ∣ 8 * p.source.d ^ 5 := by
    have hqAZ : (q : ℤ) ∣ p.source.A0 := Int.natCast_dvd.mpr hqA
    have hqBZ : (q : ℤ) ∣ p.source.B0 := Int.natCast_dvd.mpr hqB
    have hqDiffZ : (q : ℤ) ∣
        (p.source.B0 : ℤ) - (p.source.A0 : ℤ) :=
      dvd_sub hqBZ hqAZ
    have hdiffZ : (p.source.B0 : ℤ) - (p.source.A0 : ℤ) =
        8 * (p.source.d : ℤ) ^ 5 := by
      have hcast : (p.source.B0 : ℤ) =
          (p.source.A0 : ℤ) + 8 * (p.source.d : ℤ) ^ 5 := by
        exact_mod_cast p.factor_difference
      linarith
    rw [hdiffZ] at hqDiffZ
    exact Int.natCast_dvd.mp hqDiffZ
  have hqd : q ∣ p.source.d := by
    rcases hq.dvd_mul.mp hqDiff with hq8 | hqd5
    · have hq2pow : q ∣ 2 ^ 3 := by simpa using hq8
      have hq2' : q ∣ 2 := hq.dvd_of_dvd_pow hq2pow
      have : q = 2 :=
        ((Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hq2').resolve_left hq.ne_one
      exact (hq2 this).elim
    · exact hq.dvd_of_dvd_pow hqd5
  have hqMass : q ∣ zeroSectorQ p.source.c := by
    have hqProduct : q ∣ 4 * zeroSectorQ p.source.c ^ 5 := by
      rw [← p.factor_product]
      exact dvd_mul_of_dvd_left hqA _
    rcases hq.dvd_mul.mp hqProduct with hq4 | hqQ5
    · have hq2pow : q ∣ 2 ^ 2 := by simpa using hq4
      have hq2' : q ∣ 2 := hq.dvd_of_dvd_pow hq2pow
      have : q = 2 :=
        ((Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hq2').resolve_left hq.ne_one
      exact (hq2 this).elim
    · exact hq.dvd_of_dvd_pow hqQ5
  unfold zeroSectorQ at hqMass
  rcases hq.dvd_mul.mp hqMass with hq5pow | hqcpow
  · have hq5 : q ∣ 5 := hq.dvd_of_dvd_pow hq5pow
    have hqeq : q = 5 :=
      ((Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hq5).resolve_left hq.ne_one
    exact p.five_not_dvd_d (hqeq ▸ hqd)
  · have hqc : q ∣ p.source.c := hq.dvd_of_dvd_pow hqcpow
    exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqc hqd) p.coprime_c_d
```

## 数学的主張

素数 $q$ が

$$
q\mid A_0,
\qquad
q\mid B_0
$$

を同時に満たし、さらに $q\neq2$ なら矛盾する、という主張である。したがって自然数因子 $A_0,B_0$ は共通の **奇素因子** を持たない。

この時点では `Nat.Coprime A0 B0` そのものを結論にはしていない。$2$ は実際に両因子へ現れるためである。後続では二進因子を取り除いてから、この定理と 0326 `coprime_of_odd_of_no_common_odd_prime` を組み合わせ、残った奇数因子の互いに素性を得る。

## 証明全体での役割

零セクター反転 packet は既に次の二つの自然数恒等式を持っている。

$$
A_0B_0=4Q^5,
$$

$$
B_0=A_0+8d^5,
$$

ここで

$$
Q=5^5c^8.
$$

この定理は「積」と「差」の二本の情報を同じ素数 $q$ に作用させる。

1. $q\mid A_0$ と $q\mid B_0$ を差へ入れると $q\mid8d^5$。
2. $q$ は奇素数なので $q\nmid8$。したがって $q\mid d$。
3. $q\mid A_0$ を積へ入れると $q\mid4Q^5$。
4. $q$ は奇素数なので $q\nmid4$。したがって $q\mid Q$。
5. $Q=5^5c^8$ より $q\mid5$ または $q\mid c$。
6. 前者なら $q=5$ となり、既知の `five_not_dvd_d` と $q\mid d$ が矛盾する。
7. 後者なら $q\mid c$ と $q\mid d$ が `coprime_c_d` に矛盾する。

よって共通奇素因子は存在しない。

この結果は、後続の `GoldenZeroSectorInversionPacket.odd_factor_halves` が

$$
A_0=2A_1,
\qquad
B_0=2B_1
$$

と書いた後、$A_1,B_1$ の互いに素性を証明するための直接の入力となる。

## 直接依存する定義・補題

### `GoldenZeroSectorInversionPacket`

0324 で定義され、0325 で candidate から構築された certified packet。今回直接使用する field は次である。

- `p.factor_difference`
- `p.factor_product`
- `p.five_not_dvd_d`
- `p.coprime_c_d`
- `p.source.A0`, `p.source.B0`, `p.source.c`, `p.source.d`

### `zeroSectorQ`

証明中で `unfold zeroSectorQ` される質量項で、ここでは

$$
Q=5^5c^8
$$

という素因子構造が決定的に使われる。

### Mathlib の主な補題

- `Int.natCast_dvd.mpr`, `Int.natCast_dvd.mp`
- `dvd_sub`
- `Nat.Prime.dvd_mul`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.dvd_prime`
- `Nat.not_coprime_of_dvd_of_dvd`
- `dvd_mul_of_dvd_left`

また `norm_num`, `simpa`, `linarith`, `exact_mod_cast` が型変換・数値正規化を支える。

## 証明の流れ

### 1. 共通因子から差の因子を作る

まず `hqA`, `hqB` を整数へ cast する。

```lean
have hqAZ : (q : ℤ) ∣ p.source.A0 := Int.natCast_dvd.mpr hqA
have hqBZ : (q : ℤ) ∣ p.source.B0 := Int.natCast_dvd.mpr hqB
```

整数では通常の減算が使えるため、

```lean
have hqDiffZ : (q : ℤ) ∣
    (p.source.B0 : ℤ) - (p.source.A0 : ℤ) :=
  dvd_sub hqBZ hqAZ
```

により共通因子は差も割る。

一方 `p.factor_difference` は自然数上の加法形

$$
B_0=A_0+8d^5
$$

なので、`exact_mod_cast` と `linarith` を介して整数差

$$
B_0-A_0=8d^5
$$

へ戻す。最後に `Int.natCast_dvd.mp` で自然数の可除性へ戻し、

$$
q\mid8d^5
$$

を得る。

### 2. `q ≠ 2` を使って `q ∣ d` を抽出する

`hq.dvd_mul.mp hqDiff` により

$$
q\mid8
\quad\text{または}\quad
q\mid d^5
$$

へ分岐する。

$q\mid8=2^3$ の場合、素数の `dvd_of_dvd_pow` から $q\mid2$、さらに `Nat.dvd_prime` から $q=2$ となり `hq2` に矛盾する。

したがって残るのは $q\mid d^5$ であり、再び `dvd_of_dvd_pow` により

$$
q\mid d
$$

を得る。

### 3. 積恒等式から `q ∣ Q` を抽出する

`hqA : q ∣ A0` と

$$
A_0B_0=4Q^5
$$

から

$$
q\mid4Q^5
$$

を得る。

ここでも `hq.dvd_mul.mp` で

$$
q\mid4
\quad\text{または}\quad
q\mid Q^5
$$

へ分ける。前者は $4=2^2$ なので先ほどと同様に $q=2$ となって消える。後者から

$$
q\mid Q
$$

を得る。

### 4. `Q = 5^5 c^8` を分解して最後の矛盾へ送る

`unfold zeroSectorQ at hqMass` の後、素数 $q$ が積を割ることから

$$
q\mid5^5
\quad\text{または}\quad
q\mid c^8
$$

となる。

前者では $q\mid5$、素数性から $q=5$。既に $q\mid d$ があるので $5\mid d$ となり `p.five_not_dvd_d` と矛盾する。

後者では $q\mid c$。既に $q\mid d$ があるため、素数 $q>1$ が `c` と `d` の共通因子となり `p.coprime_c_d` と矛盾する。

これで全分岐が閉じる。

## Lean 固有の処理

### `ℕ → ℤ → ℕ` の往復

証明冒頭だけ自然数可除性を整数可除性へ移している。理由は `B0 - A0` を安全に扱うためである。自然数の減算 `Nat.sub` は切り詰めを持つので、既に持っている加法恒等式から整数差へ移る方が局所的には扱いやすい。

### `hq.dvd_of_dvd_pow`

数学では「素数が冪を割れば底を割る」と一言で済む箇所を Lean では明示的に適用している。これは $2^3$, $2^2$, $d^5$, $Q^5$, $5^5$, $c^8$ のすべてで同じパターンとして現れる。

### `Nat.dvd_prime`

$q\mid2$ や $q\mid5$ から、`q = 1 ∨ q = 2` / `q = 1 ∨ q = 5` 型の情報を得て、`hq.ne_one` で `1` を排除する形になっている。

### `exact (hq2 this).elim`

`this : q = 2` と `hq2 : q ≠ 2` から `False` を作り、その `False.elim` で現在のゴールを閉じる典型的な contradiction idiom である。

## 冗長・重複箇所

最も目立つ重複は、「$q$ が $2$ の正冪を割るなら $q=2$」という処理が `8` と `4` に対して二度現れる点である。

```lean
have hq2pow : q ∣ 2 ^ k := ...
have hq2' : q ∣ 2 := hq.dvd_of_dvd_pow hq2pow
have : q = 2 := ...
exact (hq2 this).elim
```

これは局所補題へ切り出せる。

また、`dvd_of_dvd_pow` による「冪から底へ戻す」処理も複数回現れるが、こちらは各対象が異なるため、現在の明示形には読みやすさもある。

## 最適化候補

### 1. 差の整数 cast を省略できる可能性

`p.factor_difference` は既に自然数の subtraction-free な

$$
B_0=A_0+8d^5
$$

である。そのため `q ∣ A0`, `q ∣ B0` から自然数上の `Nat.dvd_add_left` / 関連補題だけで $q\mid8d^5$ を引き出せる可能性が高い。

これが通れば、

- `Int.natCast_dvd`
- `dvd_sub`
- `exact_mod_cast`
- `linarith`

の一群を削除でき、この定理は完全に `ℕ` 内で閉じられる。

ただし、ここは実際の Mathlib 補題の向きと elaboration を Lean で確認してから採用すべき最適化候補である。

### 2. `q ≠ 2` から `¬ q ∣ 2^k` をまとめる局所補題

例えば「prime `q ≠ 2` は任意の正冪 `2^k` を割らない」という補助補題があれば、`8` と `4` の二つの branch を短縮できる。ただしこの補題が今回以外で再利用されないなら、現行コードの方が局所性は高い。

### 3. `q ∣ 5` から `q = 5` の短縮

Mathlib に現在のバージョンでより直接的な prime-divisor equality lemma が利用できるなら `Nat.dvd_prime ... resolve_left hq.ne_one` を短縮できる可能性がある。これも API 名の確認が必要である。

## 必要 Mathlib import

standalone 正本は

```lean
import Mathlib
```

を使用している。

この定理単独で必要になる機能は主として、

- `Nat.Prime` と素数可除性補題
- `Nat.Coprime`
- `Int.natCast_dvd`
- divisibility algebra
- `norm_num`
- `linarith`
- `exact_mod_cast`

である。

### import 最適化候補

`import Mathlib` は standalone artifact としては合理的だが、この定理だけを最小 module 化するなら NumberTheory の prime/divisibility 系と tactic import に絞れる可能性がある。ただし正確な最小 import 集合は、このリポジトリで Lean build を行わずには確定できないため、ここでは候補に留める。

## Comparator challenge 化の可否

**適している。**

特に次の能力を比較しやすい。

- `Nat.Prime.dvd_mul` を使った素因子分岐
- prime divisor of a power の処理
- `ℕ` / `ℤ` cast を含む可除性証明
- `Nat.Coprime` から共通素因子を排除する contradiction
- 既存 packet field を組み合わせて新しい局所不変量を作る能力

challenge としては、packet 全体を与える形より、必要な仮定だけを抽象化して

$$
AB=4Q^5,
\quad
B=A+8d^5,
\quad
Q=5^5c^8,
\quad
\gcd(c,d)=1,
\quad
5\nmid d
$$

から共通奇素因子が存在しないことを示させる形が比較に向く。

さらに難度を上げるなら、「整数 cast を使わず `ℕ` だけで証明せよ」という制約を付けると proof engineering の比較として面白い。

## 次に読むべき宣言

次は

```lean
theorem GoldenZeroSectorInversionPacket.odd_factor_halves
```

である。

これは `c` が奇数の branch で $Q$ も奇数になることを使い、積

$$
A_0B_0=4Q^5
$$

の二進付値がちょうど $2$ であることと差

$$
B_0=A_0+8d^5
$$

を組み合わせ、両因子がそれぞれ **ちょうど一個の 2** を持つことを示す。結果として

$$
A_0=2A_1,
\qquad
B_0=2B_1
$$

かつ $A_1,B_1$ が奇数であることを得る。

その後 `no_common_odd_prime` と 0326 `coprime_of_odd_of_no_common_odd_prime` が結合され、`A1`, `B1` の `Nat.Coprime` が構築される。したがって今回の 0328 は、二進因子を除去した後の factor splitting へ進むための素因子排除の核心である。
