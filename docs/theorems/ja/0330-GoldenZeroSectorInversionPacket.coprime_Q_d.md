# 0330 — `GoldenZeroSectorInversionPacket.coprime_Q_d`

## 宣言種別

この宣言は **`theorem`** である。

`GoldenZeroSectorInversionPacket` に属する公開定理であり、零セクター反転で現れる第五冪質量

$$
Q=5^5c^8
$$

と、quartic 側の tenth-power base `d` が互いに素であることを証明する。

## Lean の型

```lean
/-- The full fifth-power mass is coprime to the quartic tenth-power base. -/
theorem GoldenZeroSectorInversionPacket.coprime_Q_d
    (p : GoldenZeroSectorInversionPacket) :
    Nat.Coprime (zeroSectorQ p.source.c) p.source.d := by
  have h5d : Nat.Coprime 5 p.source.d :=
    (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr p.five_not_dvd_d
  unfold zeroSectorQ
  exact (h5d.pow_left 5).mul_left (p.coprime_c_d.pow_left 8)
```

## 数学的主張

`zeroSectorQ` は

$$
Q=5^5c^8
$$

と定義されている。

この定理は、packet に保存されている

$$
5\nmid d
$$

と

$$
\gcd(c,d)=1
$$

から

$$
\gcd(5^5c^8,d)=1
$$

を導く。

したがって結論は

$$
\gcd(Q,d)=1
$$

である。

数学的には非常に短い合成則であり、`d` が `Q` を構成する二つの素因子源、すなわち `5` と `c` の双方から独立であることを一つの `Nat.Coprime` にまとめている。

## 証明全体での役割

零セクター反転後の factorization phase では、`A0`, `B0` を二進因子と第五冪部分へ分解していく。その際、後続 packet は単に左右因子同士が互いに素であるだけでなく、そこから抽出される第五冪 base `e`, `f` が `d` とも互いに素であることを要求する。

今回の定理は、そのための mass-level coprimality を先に確定する。

$$
Q=5^5c^8
$$

の全体と `d` が互いに素であれば、後で `e f = Q` や `2(e f)=Q` のような ownership 等式が得られたとき、`e*f` と `d` の互いに素性へ降ろすことができる。

つまりこの定理は、0328 `no_common_odd_prime` や 0329 `odd_factor_halves` のような局所的な二因子解析とは異なり、**零セクター質量 `Q` と quartic base `d` の全体的な素因子分離** を保証する bridge である。

## 直接依存する定義・補題

### `zeroSectorQ`

```lean
def zeroSectorQ (c : ℕ) : ℕ :=
  5 ^ 5 * c ^ 8
```

今回の証明では `unfold zeroSectorQ` によりそのまま展開される。

### `GoldenZeroSectorInversionPacket.five_not_dvd_d`

packet に保存されている

```lean
five_not_dvd_d : ¬ 5 ∣ source.d
```

を用いる。

これは上流の `GoldenZeroSectorCandidate.five_not_dvd_d` に由来する。

### `GoldenZeroSectorInversionPacket.coprime_c_d`

packet に保存されている

```lean
coprime_c_d : Nat.Coprime source.c source.d
```

を用いる。

### Mathlib の主な道具

- `Nat.Prime.coprime_iff_not_dvd`
- `Nat.Coprime.pow_left`
- `Nat.Coprime.mul_left`
- `norm_num`
- `unfold`

## 証明または構築の流れ

### 1. `5` と `d` の互いに素性を作る

packet には

```lean
p.five_not_dvd_d : ¬ 5 ∣ p.source.d
```

がある。

さらに `5` は素数なので

```lean
(by norm_num : Nat.Prime 5).coprime_iff_not_dvd
```

を使い、

$$
\gcd(5,d)=1
$$

を `h5d` として得る。

### 2. `5^5` と `d` の互いに素性へ持ち上げる

`h5d.pow_left 5` により

$$
\gcd(5^5,d)=1
$$

を得る。

`Nat.Coprime.pow_left` は、左辺の基数と右辺が互いに素なら、その左辺の任意の自然数冪とも互いに素であることを表す。

### 3. `c^8` と `d` の互いに素性へ持ち上げる

packet の

```lean
p.coprime_c_d : Nat.Coprime p.source.c p.source.d
```

から

```lean
p.coprime_c_d.pow_left 8
```

により

$$
\gcd(c^8,d)=1
$$

を得る。

### 4. 左辺の積を合成する

`Nat.Coprime.mul_left` により

$$
\gcd(5^5,d)=1,
\qquad
\gcd(c^8,d)=1
$$

を

$$
\gcd(5^5c^8,d)=1
$$

へ合成する。

`zeroSectorQ` を展開済みなので、これがそのまま目標に一致する。

## Lean 固有の処理

### `Nat.Prime.coprime_iff_not_dvd`

数学では「素数 `p` が `n` を割らないなら `gcd(p,n)=1`」をほぼ自明に使うが、Lean では `Nat.Prime` の API を介して `¬ p ∣ n` を `Nat.Coprime p n` へ変換している。

```lean
(by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr p.five_not_dvd_d
```

は、その変換を一行で行う箇所である。

### `.pow_left`

`Nat.Coprime` は冪に対して閉じている。ここでは

```lean
h5d.pow_left 5
p.coprime_c_d.pow_left 8
```

と、`5` と `c` の両方を必要な指数まで持ち上げる。

### `.mul_left`

```lean
(h5d.pow_left 5).mul_left (p.coprime_c_d.pow_left 8)
```

は、共通の右辺 `d` に対して左辺の二つの互いに素条件を積へまとめる。

この chained method syntax により、証明はほぼ数学式そのままの長さになっている。

## 冗長・重複箇所

この定理自身には実質的な冗長性はほとんどない。証明は三段階、

1. `5` と `d` の coprime 化
2. `5^5`, `c^8` への冪持ち上げ
3. 積への合成

だけで閉じている。

強いて挙げれば、`h5d` を局所名として置かずに `exact` 内へ直接埋め込むことは可能である。しかし現在の形の方が `5 ∤ d` から `Coprime 5 d` への意味変換が明示され、読みやすい。

## 最適化候補

### 1. 現行形を維持するのが有力

この証明は既にかなり最小化されている。

```lean
have h5d : Nat.Coprime 5 p.source.d := ...
unfold zeroSectorQ
exact (h5d.pow_left 5).mul_left (p.coprime_c_d.pow_left 8)
```

という構成は、数学的構造と Lean API の対応が明瞭であり、短縮しても大きな利益はない。

### 2. `zeroSectorQ` 用の一般 coprime 補題

もし後続で

```lean
Nat.Coprime (zeroSectorQ c) n
```

を何度も再構築するなら、

```lean
Nat.Coprime 5 n → Nat.Coprime c n → Nat.Coprime (zeroSectorQ c) n
```

という一般補題へ切り出す余地がある。

ただし現時点で、この一回だけのために抽象化する必要性は低い。

### 3. `five_not_dvd_d` の保存形式

上流 packet が `¬ 5 ∣ d` ではなく `Nat.Coprime 5 d` を直接保持していれば今回の最初の変換は不要になる。

一方、`¬ 5 ∣ d` は算術的な exclusion として他の証明でも使いやすいため、現在の field 設計には合理性がある。

## 必要 Mathlib import と import 最適化候補

standalone 正本全体は

```lean
import Mathlib
```

を使用している。

この定理単体で必要になる機能は主に

- 自然数の素数性と可除性
- `Nat.Coprime`
- `Nat.Coprime.pow_left`
- `Nat.Coprime.mul_left`
- `norm_num`

である。

したがって `Mathlib` 全体より小さい import へ縮小できる可能性は高い。ただし今回 Lean ビルドは行わないため、**最小 import 集合は確認していない**。

特に `norm_num` tactic の import と `Nat.Coprime` / `Nat.Prime` の定理配置を同時に満たす最小構成は別途検証が必要である。

## Comparator challenge 化の可否

**適している。**

理由は、証明の数学的内容が非常に明快で、同一命題に複数の Lean 表現を比較できるからである。

challenge としては、例えば次の制約が考えられる。

- `zeroSectorQ` を展開する
- `five_not_dvd_d` と `coprime_c_d` のみを packet field として使用する
- `omega`, `linarith`, `nlinarith` を使わない
- `Nat.Coprime.pow_left` と `mul_left` を使う短証明を目標にする

期待される核心は

```lean
have h5d : Nat.Coprime 5 p.source.d :=
  (by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr p.five_not_dvd_d
unfold zeroSectorQ
exact (h5d.pow_left 5).mul_left (p.coprime_c_d.pow_left 8)
```

である。

proof search や自動算術に依存せず、Mathlib の coprimality API を正しく選択できるかを見る小型 Comparator challenge として良い題材である。

## 次に読むべき宣言

次は

```lean
theorem fifth_mod_eleven_cases (n : ℕ) :
    n ^ 5 % 11 = 0 ∨ n ^ 5 % 11 = 1 ∨ n ^ 5 % 11 = 10 := by
  rw [Nat.pow_mod]
  generalize hr : n % 11 = r
  have hlt : r < 11 := by rw [← hr]; omega
  interval_cases r <;> norm_num
```

である。

したがって次の連番は **0331 `fifth_mod_eleven_cases`** となる。

これは第五冪の mod 11 剰余を

$$
0,1,-1\pmod{11}
$$

の三種類へ分類する有限剰余計算であり、その次の `eleven_dvd_d_of_fifth_add_four_fifth` における mod 11 channel の基礎となる。