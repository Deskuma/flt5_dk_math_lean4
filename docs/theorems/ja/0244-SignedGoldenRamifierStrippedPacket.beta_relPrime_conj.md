# 0244 — `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj`

## Lean の型

```lean
/-- Every common divisor of a stripped element and its conjugate is a unit. -/
theorem SignedGoldenRamifierStrippedPacket.beta_relPrime_conj
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    GoldenRelPrime p.beta (goldenConj p.beta) := by
  intro d hdbeta hdconj
  have hddiff : GoldenDivides d (p.beta - goldenConj p.beta) :=
    goldenDivides_sub hdbeta hdconj
  have hnormBeta : goldenNorm d ∣ goldenNorm p.beta :=
    goldenNorm_dvd_of_goldenDivides hdbeta
  have hnormDiff : goldenNorm d ∣
      goldenNorm (p.beta - goldenConj p.beta) :=
    goldenNorm_dvd_of_goldenDivides hddiff
  have hdB : (goldenNorm d).natAbs ∣ p.exceptional.powerSplit.b ^ 5 := by
    apply Int.dvd_natCast.mp
    simpa [p.beta_norm] using hnormBeta
  have hdA : (goldenNorm d).natAbs ∣
      5 ^ 15 * p.exceptional.powerSplit.a ^ 20 := by
    apply Int.dvd_natCast.mp
    have hpos : goldenNorm d ∣
        (5 ^ 15 * p.exceptional.powerSplit.a ^ 20 : ℕ) := by
      exact Int.dvd_neg.mp (by simpa [p.norm_sub_conj_eq] using hnormDiff)
    exact_mod_cast hpos
  have hab := p.exceptional.powerSplit.coprime_b5_scaled_a20
  have habs : Nat.Coprime (p.exceptional.powerSplit.b ^ 5)
      (5 ^ 15 * p.exceptional.powerSplit.a ^ 20) := hab
  have hone : (goldenNorm d).natAbs = 1 :=
    Nat.eq_one_of_dvd_coprimes habs hdB hdA
  apply goldenUnit_of_norm_eq_one_or_neg_one
  omega
```

これは `theorem` であり、0231 `SignedGoldenRamifierStrippedPacket` が保持する stripped element `beta` とその共役 `goldenConj beta` が、黄金整数環の意味で相対素であることを証明する。

## 数学的主張

0208 `GoldenRelPrime` は

$$
GoldenRelPrime(x,y)
$$

を

$$
\forall d,\quad d\mid x\land d\mid y\Longrightarrow d\text{ は unit}
$$

という Bézout-free な形で定義している。

本 theorem は stripped packet の `beta` について

$$
GoldenRelPrime(\beta,\overline\beta)
$$

を示す。

共通因子を $d$ とする。すると $d$ は `beta` と `conj beta` の両方を割るので、その差も割る。

$$
d\mid\beta,\qquad d\mid\overline\beta
\Longrightarrow
d\mid(\beta-\overline\beta).
$$

0192 `goldenNorm_dvd_of_goldenDivides` により、黄金整数の整除は整数ノルムの整除へ射影される。

$$
N(d)\mid N(\beta),
$$

$$
N(d)\mid N(\beta-\overline\beta).
$$

stripped packet は

$$
N(\beta)=b^5
$$

を保持し、0243 では

$$
N(\beta-\overline\beta)=-5^{15}a^{20}
$$

が確立されている。したがって自然数値 $|N(d)|$ は

$$
b^5
$$

と

$$
5^{15}a^{20}
$$

の双方を割る。

一方、power-split packet は

$$
\gcd\!\left(b^5,5^{15}a^{20}\right)=1
$$

を `coprime_b5_scaled_a20` として保持する。よって両方を割る自然数は `1` しかなく、

$$
|N(d)|=1.
$$

整数ノルムについてこれは

$$
N(d)=1\quad\text{または}\quad N(d)=-1
$$

を意味する。0201 `goldenUnit_of_norm_eq_one_or_neg_one` により $d$ は `GoldenUnit` となる。したがって任意の共通因子が unit であり、`beta` とその共役は相対素である。

## 証明全体での役割

この theorem は `SignedGoldenConjugateCoprime.lean` の中心結果である。module コメント自体が、共通因子のノルムを二つの整数 mass

$$
N(\beta)=b^5,
$$

$$
N(\beta-\overline\beta)=-5^{15}a^{20}
$$

へ同時に拘束し、power-split 側の互いに素性から unit を導く方針を明示している。

0231–0243 までの流れは、本 theorem のための材料整備と見ることができる。

- stripped packet が `beta_norm : N(beta)=b^5` を保持する。
- 0191 `goldenDivides_sub` が共通因子を差へ移す。
- 0192 が黄金整除を整数ノルム整除へ射影する。
- 0241–0243 が `beta-conj(beta)` のノルムを exact five-adic mass にする。
- power-split packet が `b^5` と `5^15*a^20` の coprimality を保持する。
- 0201 が norm `±1` を unit へ戻す。

この結果は後続の fifth-power factor extraction に必要な主要仮定である。正本 source の後段では `p.beta_relPrime_conj` が `GoldenCoprimeFactorOfFifthPower` へ直接渡され、

$$
\beta=\varepsilon\gamma^5
$$

という unit × fifth-power 形を得るために使われる。

## 直接依存する定義・補題

直接の主要依存は次の通りである。

- 0231 `SignedGoldenRamifierStrippedPacket`
- 0208 `GoldenRelPrime`
- 0187 `GoldenDivides`
- 0191 `goldenDivides_sub`
- 0192 `goldenNorm_dvd_of_goldenDivides`
- packet field `p.beta_norm`
- 0243 `SignedGoldenRamifierStrippedPacket.norm_sub_conj_eq`
- `SignedFiveAdicPowerSplit.coprime_b5_scaled_a20`
- `Int.dvd_natCast.mp`
- `Int.dvd_neg.mp`
- `Nat.eq_one_of_dvd_coprimes`
- 0201 `goldenUnit_of_norm_eq_one_or_neg_one`
- `omega`

概念的には

$$
\text{common divisor}
\to
\text{divides }N(\beta)\text{ and }N(\beta-\overline\beta)
\to
|N(d)|\mid b^5,\ 5^{15}a^{20}
\to
|N(d)|=1
\to
N(d)=\pm1
\to
GoldenUnit(d).
$$

## 証明の流れ

### 1. 共通因子を受け取る

```lean
intro d hdbeta hdconj
```

`GoldenRelPrime` の定義を展開した形で、任意の共通因子 `d` と二本の整除仮定を受け取る。

### 2. 共通因子を共役差へ移す

```lean
have hddiff : GoldenDivides d (p.beta - goldenConj p.beta) :=
  goldenDivides_sub hdbeta hdconj
```

通常の $d\mid x, d\mid y\Rightarrow d\mid x-y$ を黄金整数 API で使う。

### 3. ノルム整除へ射影する

```lean
have hnormBeta : goldenNorm d ∣ goldenNorm p.beta :=
  goldenNorm_dvd_of_goldenDivides hdbeta
```

および

```lean
have hnormDiff : goldenNorm d ∣
    goldenNorm (p.beta - goldenConj p.beta) :=
  goldenNorm_dvd_of_goldenDivides hddiff
```

により、環内部の整除を整数側へ移す。

### 4. `natAbs` による自然数整除へ変換する

`hdB` では `p.beta_norm` を使い、

$$
|N(d)|\mid b^5
$$

を得る。

`hdA` では 0243 の負号付き等式から `Int.dvd_neg.mp` で符号を除き、cast を整理して

$$
|N(d)|\mid 5^{15}a^{20}
$$

を得る。

### 5. coprime masses の共通約数を 1 に潰す

```lean
have hone : (goldenNorm d).natAbs = 1 :=
  Nat.eq_one_of_dvd_coprimes habs hdB hdA
```

ここが算術上の魔核である。power-split 側で既に証明済みの coprimality を使うことで、共通因子ノルムの絶対値が `1` に強制される。

### 6. norm `±1` から unit へ戻す

```lean
apply goldenUnit_of_norm_eq_one_or_neg_one
omega
```

`natAbs = 1` から整数値そのものが `1` または `-1` であることを `omega` が処理し、0201 の unit criterion で証明を閉じる。

## Lean 固有の処理

この proof では型境界が三段ある。

1. `GoldenInt` 上の `GoldenDivides`
2. `ℤ` 上の `goldenNorm` 整除
3. `ℕ` 上の `Int.natAbs` 整除と `Nat.Coprime`

`Int.dvd_natCast.mp` は、整数整除を自然数の `natAbs` 整除へ移す橋として使われる。`exact_mod_cast` は `ℤ` / `ℕ` の cast を整合させる。

`Int.dvd_neg.mp` は 0243 の

$$
N(\beta-\overline\beta)=-M
$$

という負号を取り除き、正の自然数 mass $M=5^{15}a^{20}$ へ持ち込むために使われる。

最後の `omega` は、

```lean
(goldenNorm d).natAbs = 1
```

から

```lean
goldenNorm d = 1 ∨ goldenNorm d = -1
```

への整数符号分類を閉じる。

## 冗長・重複箇所

証明の数学は一貫しているが、`ℤ → natAbs → ℕ → ±1` という往復には多少の API friction がある。

特に `hdB` と `hdA` はどちらも

> integer norm divisibility を natural-number divisibility に移す

という同型の処理を行っている。`goldenNorm_natAbs_dvd_of_goldenDivides` のような補助 theorem があれば、この変換を一度に隠せる可能性がある。

また最後の

```lean
have hone : (goldenNorm d).natAbs = 1 := ...
apply goldenUnit_of_norm_eq_one_or_neg_one
omega
```

も、「`natAbs N = 1` なら対応する黄金整数は unit」という helper があれば一段にまとめられる。

一方、現行 proof は各 arithmetic interface を明示するため、監査性は高い。

## 最適化候補

1. `GoldenDivides d x → (goldenNorm d).natAbs ∣ (goldenNorm x).natAbs` を直接返す helper を追加する。
2. `goldenUnit_of_natAbs_norm_eq_one` のような theorem を追加し、最後の `omega` を隠す。
3. `GoldenUnit ↔ IsUnit` を整備し、標準環論 API へ寄せる。
4. `goldenNorm` の絶対値を multiplicative `MonoidHom GoldenInt ℕ` 的に bundle し、整除射影を一般化する。
5. `beta_norm` と `norm_sub_conj_eq` の二つの mass、およびその coprimality を専用 packet / certificate にまとめる。

ただし本 theorem は、どの情報から relative primality が出るかを非常に明瞭に示しているので、過度に抽象化すると FLT5 固有の five-adic 構造が見えにくくなる可能性がある。

## 必要 Mathlib import と import 最適化候補

standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用している。本 theorem が直接利用する Mathlib 側の主な表面は、整数・自然数整除、`Nat.Coprime`、cast machinery、`omega` である。

生成 artifact なので original module 単独の最小 import 集合はこのリポジトリからは直接確認できない。manifest 上では `SignedGoldenConjugateCoprime.lean` は `GoldenDivisibility`、`SignedGoldenRamifierStripped` などの後に配置されている。

Lean build は行わないため、正確な最小 import は未検証である。候補としては `Mathlib` 全体から、整数整除・coprime・tactic `omega` と上流 DkMath modules だけへ狭められる可能性がある。

## Comparator challenge 化の可否

適している。特に次の三方式を比較できる。

- A: 現行の `GoldenDivides → ℤ divisibility → natAbs → Nat.Coprime` proof
- B: gcd / Euclidean-domain API を直接使い、共通因子の associated class を処理する proof
- C: absolute norm を multiplicative map として bundle し、coprime image theorem から unit を導く proof

比較軸は、proof 長、cast 数、`omega` / `exact_mod_cast` 依存、数学的 provenance の見えやすさ、一般 quadratic-order への移植性、FLT5 固有の five-adic mass が読みやすく残るか、である。

本 theorem は「明示座標・整数 mass による監査性」と「抽象 algebra hierarchy」のどちらを優先するかを比較する良い題材である。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` generated section である。

module コメントには、共通因子が `N(beta)=b^5` と差のノルム `-5^15*a^20` の双方を割り、power-split coprimality から norm `±1` と unit を得る方針が明記されている。本 theorem はその方針をそのまま Lean proof にした中心宣言である。

対象ブランチには `docs/pdf/FLT5-main-ja-v0-r1.pdf` と `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0245 `SignedGoldenConjugateCoprimePacket`** である。

```lean
/-- A packet retaining the stripped data and certified conjugate coprimality. -/
structure SignedGoldenConjugateCoprimePacket (u v w : ℕ) : Type where
  stripped : SignedGoldenRamifierStrippedPacket u v w
  relPrime : GoldenRelPrime stripped.beta (goldenConj stripped.beta)
```

0244 で relative-primality certificate が完成したため、0245 は stripped packet とその certificate を一つの structure に束ねる。これにより後続の fifth-power factor extraction は `beta` の構成過程を再展開せず、certified conjugate-coprime state を直接受け取れるようになる。
