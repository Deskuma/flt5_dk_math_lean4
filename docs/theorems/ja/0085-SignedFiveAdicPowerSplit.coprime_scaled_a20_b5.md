# 0085 — `SignedFiveAdicPowerSplit.coprime_scaled_a20_b5`

## Lean の型

```lean
theorem SignedFiveAdicPowerSplit.coprime_scaled_a20_b5
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    Nat.Coprime (5 ^ 15 * s.a ^ 20) (s.b ^ 5) := by
  have h5b : Nat.Coprime 5 s.b :=
    (show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr s.five_not_dvd_b
  have hscaled : Nat.Coprime (5 ^ 15) (s.b ^ 5) :=
    (Nat.Coprime.pow_left 15 h5b).pow_right 5
  have hab : Nat.Coprime (s.a ^ 20) (s.b ^ 5) :=
    (Nat.Coprime.pow_left 20 s.coprime_a_b).pow_right 5
  exact hscaled.mul_left hab
```

## 数学的主張

`SignedFiveAdicPowerSplit` が保持する

$$
\gcd(a,b)=1
$$

と、0084 で得た

$$
5\nmid b
$$

から、後続で必要となる拡大された二因子

$$
5^{15}a^{20}
\quad\text{and}\quad
b^5
$$

が互いに素であること、すなわち

$$
\gcd(5^{15}a^{20},b^5)=1
$$

を示す。

ここで指数 15、20、5 はこの補題自身が新しく導出する数論的情報ではなく、後続の ramifier-stripped square / golden factorization で現れる形に合わせた指数である。

## 証明全体での役割

0083 で

$$
\mathrm{carrier}=5^4a^5,\qquad
\mathrm{residual}=5b^5,\qquad
\gcd(a,b)=1
$$

という power split を得て、0084 で $5\nmid b$ を確定した。本定理はその二つの局所的な coprimality 情報を、後続で実際に使う高冪の積へ持ち上げる normalization lemma である。

つまり証明の流れは

$$
\gcd(a,b)=1,\ 5\nmid b
\Longrightarrow
\gcd(5^{15},b^5)=1,\ \gcd(a^{20},b^5)=1
\Longrightarrow
\gcd(5^{15}a^{20},b^5)=1
$$

となる。

本補題により、後続の因数分解では左側の $5$-冪と $a$-冪を一つの因子として扱っても、右側の $b^5$ との間に新しい共通因子が発生しないことが保証される。

## 直接依存する定義・補題

- `SignedFiveAdicPowerSplit`
  - `s.coprime_a_b : Nat.Coprime s.a s.b`
- `SignedFiveAdicPowerSplit.five_not_dvd_b`
- `Nat.Prime.coprime_iff_not_dvd`
- `Nat.Coprime.pow_left`
- `Nat.Coprime.pow_right`
- `Nat.Coprime.mul_left`
- `decide`
  - `Nat.Prime 5` の有限判定に使用

本定理は `SignedFiveAdicPacket` の carrier / residual の式や mod 25 の情報を直接参照しない。それらは 0083–0084 までに `s.coprime_a_b` と `s.five_not_dvd_b` へ圧縮済みである。

## 証明の流れ

1. `s.five_not_dvd_b` と 5 の素数性から

$$
\gcd(5,b)=1
$$

を得る。

2. `pow_left 15` と `pow_right 5` により

$$
\gcd(5^{15},b^5)=1
$$

へ持ち上げる。

3. `s.coprime_a_b` に `pow_left 20`、`pow_right 5` を適用し、

$$
\gcd(a^{20},b^5)=1
$$

を得る。

4. `hscaled.mul_left hab` により、同じ右因子 $b^5$ に対して互いに素な左因子 $5^{15}$ と $a^{20}$ を掛け合わせ、

$$
\gcd(5^{15}a^{20},b^5)=1
$$

を得る。

## Lean 固有の処理

最初の

```lean
(show Nat.Prime 5 by decide).coprime_iff_not_dvd.mpr s.five_not_dvd_b
```

は、具体的な素数 5 の証明を `decide` で生成し、その prime API を使って `¬ 5 ∣ b` を `Nat.Coprime 5 b` へ変換している。

`Nat.Coprime.pow_left` / `pow_right` は gcd を直接展開せず、coprimality を冪へ保存する高水準 API である。このため本証明には素因数分解、gcd 計算、`omega`、`ring` は不要である。

最後の

```lean
exact hscaled.mul_left hab
```

では、`Nat.Coprime` の積閉性を利用して二つの左因子をまとめている。Lean 側では「同じ右因子に対してそれぞれ coprime」という型が揃っているため、そのまま合成できる。

## 冗長・重複箇所

証明自体は非常に短く、局所的な冗長性は少ない。ただし

```lean
(Nat.Coprime.pow_left n h).pow_right m
```

というパターンは、後続の高冪因子分解でも繰り返し現れる可能性がある。

また指数 15、20、5 をここで固定しているため、この補題は用途特化型である。数学的コアはより一般に

$$
\gcd(p,b)=1,\quad\gcd(a,b)=1
\Longrightarrow
\gcd(p^r a^s,b^t)=1
$$

という形であり、本 theorem はその $p=5$, $r=15$, $s=20$, $t=5$ という特殊化と見なせる。

## 最適化候補

一般補題としては概念的に次のような形へ抽象化できる。

```lean
-- 概念形
theorem coprime_mul_powers
    (hpb : Nat.Coprime p b)
    (hab : Nat.Coprime a b) :
    Nat.Coprime (p ^ r * a ^ s) (b ^ t) := ...
```

この helper が後続で複数回使われるなら、指数操作の boilerplate を減らせる。一方、本 theorem は四行で読み切れるため、この一箇所だけなら現行の明示的証明の方が意図を追いやすい。

もう一つの最適化は、`five_not_dvd_b` の時点で `Nat.Coprime 5 b` を field または companion theorem として公開することだ。ただし `¬ 5 ∣ b` の方が arithmetic obstruction として意味が直接的であり、API を増やす価値は利用頻度次第である。

## 必要 Mathlib import と import 最適化候補

対象ブランチの standalone artifact は `import Mathlib` で構築されており、manifest 上では本宣言は `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` に属する。

本証明で直接必要なのは `Nat.Prime`、`Nat.Coprime` の prime/divisibility bridge と power/product API、および `decide` である。`ring` や `omega` は本定理では使っていない。

したがって standalone の `Mathlib` 全体 import は明らかに過大だが、この博物館ブランチでは分割元 `SignedFiveAdicPowerSplit.lean` の正確な import 列を独立確認していないため、最小 import の具体名は断定しない。import 最適化を行うなら、分割元 module の import graph を確認したうえで Lean build により検証すべきである。本回では Lean build は行わない。

## Comparator challenge 化の可否

可能。証明探索よりも API 選択の比較に向く。

比較候補は次の三方式である。

1. 現行の `Nat.Coprime.pow_left` / `pow_right` / `mul_left` による構成。
2. 一般 helper `coprime_mul_powers` を先に証明して特殊化する構成。
3. gcd や prime-factor characterization へ一度落としてから再構成する低水準版。

評価軸は proof length、型推論の安定性、再利用性、必要 import、後続 theorem との API 一貫性である。現行版は Mathlib の高水準 `Nat.Coprime` API を素直に使っており、比較の基準実装として良い。

## PDF との対応

既存の日英 PDF は叙述的根拠として扱う方針だが、今回 GitHub code search が 502 upstream error となり、この短い補題に対応する PDF 内位置を一意に特定できなかった。そのためページ番号・節番号・PDF 固有の説明は推測で補っていない。

形式的な最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` にある実際の Lean 宣言である。

## 次に読むべき定理

次は

```lean
theorem SignedFiveAdicPowerSplit.coprime_b5_scaled_a20
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    Nat.Coprime (s.b ^ 5) (5 ^ 15 * s.a ^ 20) :=
  s.coprime_scaled_a20_b5.symm
```

を読むべきである。

内容は本 theorem の coprimality の向きを反転した companion lemma である。数学的情報は同一だが、後続 API が $b^5$ を左因子として要求するため、その型の向きを一行で供給する。これは Lean 形式化における「同じ数学的事実を後段の引数順へ合わせる adapter」の典型例である。
