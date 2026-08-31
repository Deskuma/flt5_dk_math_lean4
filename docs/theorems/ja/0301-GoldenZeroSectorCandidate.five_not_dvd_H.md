# 0301 — `GoldenZeroSectorCandidate.five_not_dvd_H`

## 宣言種別

これは **`theorem`** である。

zero-sector candidate に保存された norm の情報と prime five の除外条件を使い、quartic factor

$$
H(r,s):=\operatorname{goldenFifthSndFactor}(r,s)
$$

そのものが 5 で割れないこと

$$
5\nmid H(r,s)
$$

を証明する。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- The quartic factor retains the packet's exclusion of the prime five. -/
theorem five_not_dvd_H (p : GoldenZeroSectorCandidate) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor p.r p.s := by
  intro hH
  have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq
    (⟨p.r, p.s⟩ : GoldenInt)
  have hnormSq : (5 : ℤ) ∣ goldenNorm ⟨p.r, p.s⟩ ^ 2 := by
    have h := dvd_sub hH hdiff
    ring_nf at h
    exact h
  have hnorm : (5 : ℤ) ∣ goldenNorm ⟨p.r, p.s⟩ :=
    (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
  apply p.five_not_dvd_b
  rcases p.norm_eq_or_eq_neg with h | h
  · rw [h] at hnorm
    exact_mod_cast hnorm
  · rw [h] at hnorm
    exact_mod_cast (Int.dvd_neg.mp hnorm)
```

結論は整数環 `ℤ` 上の非可除性

```lean
¬ (5 : ℤ) ∣ goldenFifthSndFactor p.r p.s
```

である。

## 数学的意味

本 theorem の中心は、quartic factor と golden norm の間の合同関係

$$
H(r,s)\equiv N(r,s)^2\pmod 5
$$

である。Lean ではこれを

```lean
five_dvd_goldenFifthSndFactor_sub_norm_sq
```

が

$$
5\mid\bigl(H(r,s)-N(r,s)^2\bigr)
$$

という形で与える。

ここで仮に

$$
5\mid H(r,s)
$$

とすると、差も 5 で割れるため

$$
5\mid N(r,s)^2
$$

となる。5 は素数なので

$$
5\mid N(r,s)
$$

が従う。

一方 candidate は

$$
N(r,s)=b
\quad\text{または}\quad
N(r,s)=-b
$$

を `norm_eq_or_eq_neg` として保持し、さらに

$$
5\nmid b
$$

を `five_not_dvd_b` として保持している。

従ってどちらの符号の場合でも $5\mid N(r,s)$ は $5\mid b$ を意味し、`five_not_dvd_b` と矛盾する。ゆえに

$$
5\nmid H(r,s).
$$

## 証明全体での役割

0300 `coprime_c_d` までで tenth-power split の base 側には

$$
a=cd,
\qquad
\gcd(c,d)=1
$$

が得られている。しかし prime five が `d` 側へ入り込めるかどうかは、まだ決着していない。

本 theorem はまず quartic factor 自身に対して

$$
5\nmid H(r,s)
$$

を確定する。直後の 0302 `five_not_dvd_d` は

$$
H(r,s)=d^{10}
$$

を使って

$$
5\nmid d
$$

を導く。

したがって 0301 は、**five-adic exclusion を norm 側から quartic factor 側へ移送する橋** である。ここで 5 を `H` から排除しておくことで、後続の split base `d`、parity、valuation、factorization packet の解析で five-adic ownership が混線しない。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate`

0290 で導入された structure で、本 theorem は少なくとも次の field を使う。

```lean
p.five_not_dvd_b : ¬ 5 ∣ p.b
p.norm_eq_or_eq_neg :
  goldenNorm ⟨p.r, p.s⟩ = (p.b : ℤ) ∨
    goldenNorm ⟨p.r, p.s⟩ = -(p.b : ℤ)
```

つまり prime-five exclusion の最終的な根拠は quartic factor の式そのものではなく、candidate に保存された `b` の five-adic exclusion である。

### `goldenFifthSndFactor`

本 theorem が 5 の非可除性を証明する対象となる quartic factor である。

### `goldenNorm`

`GoldenInt` の norm。ここでは `⟨p.r,p.s⟩ : GoldenInt` の norm を使う。

### `five_dvd_goldenFifthSndFactor_sub_norm_sq`

直接の主要補題。

```lean
theorem five_dvd_goldenFifthSndFactor_sub_norm_sq (gamma : GoldenInt) :
    (5 : ℤ) ∣
      goldenFifthSndFactor gamma.fst gamma.snd - goldenNorm gamma ^ 2
```

すなわち

$$
H(\gamma)-N(\gamma)^2\equiv0\pmod5.
$$

この congruence が本 theorem の魔核である。

### `dvd_sub`

`hH : 5 ∣ H` と `hdiff : 5 ∣ H-N^2` から、適切な差を取って $5\mid N^2$ を得るために使う。

### `Prime.dvd_of_dvd_pow`

5 が素数であり $5\mid N^2$ なら $5\mid N$ を導く。

```lean
(show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
```

### `Int.dvd_neg`

norm が `-b` 側だった場合に、$5\mid -b$ から $5\mid b$ へ符号を除く。

### `exact_mod_cast`

整数上の divisibility

```lean
(5 : ℤ) ∣ (p.b : ℤ)
```

を自然数上の

```lean
5 ∣ p.b
```

へ移すために使う。

## 証明または構築の流れ

1. 反証法として
   $$
   5\mid H(r,s)
   $$
   を `hH` と仮定する。
2. `five_dvd_goldenFifthSndFactor_sub_norm_sq` から
   $$
   5\mid H(r,s)-N(r,s)^2
   $$
   を `hdiff` として得る。
3. `dvd_sub hH hdiff` により、5 が norm square を割る形の divisibility を作る。
4. `ring_nf` で差の符号・正規形を整理し、
   $$
   5\mid N(r,s)^2
   $$
   を `hnormSq` とする。
5. 5 が素数であることを `norm_num` で証明し、`Prime.dvd_of_dvd_pow` により
   $$
   5\mid N(r,s)
   $$
   を `hnorm` として得る。
6. `apply p.five_not_dvd_b` により、目標を `5 ∣ p.b` の構築へ変える。
7. `p.norm_eq_or_eq_neg` を場合分けする。
8. `N=b` の枝では `rw [h] at hnorm` の後、`exact_mod_cast hnorm` で `5 ∣ p.b` を得る。
9. `N=-b` の枝では `Int.dvd_neg.mp hnorm` で負号を外し、`exact_mod_cast` で自然数へ戻す。
10. どちらも `p.five_not_dvd_b` と矛盾し、仮定 `hH` が否定される。

## Lean 固有の処理

数学では

$$
5\mid H,
\qquad
5\mid(H-N^2)
$$

から即座に $5\mid N^2$ と書くことが多い。Lean では `dvd_sub` の引数順により生成される式がそのまま `N^2` の形にならないため、

```lean
ring_nf at h
```

で整数式を正規化している。

また

```lean
(show Prime (5 : ℤ) by norm_num)
```

は、自然数の `Nat.Prime 5` ではなく整数環で必要な `Prime (5 : ℤ)` を明示的に構成している点が重要である。

最後の `exact_mod_cast` は、candidate field `five_not_dvd_b` が `ℕ` 上の divisibility を否定する一方、`hnorm` は `ℤ` 上にあるため必要となる coercion bridge である。

## 冗長・重複箇所

この theorem は上流にある zero-sector 用の類似論法、たとえば `SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_gamma_norm` や quartic factor の five-exclusion と数学的に近い構造を持つ。実際、`five_dvd_goldenFifthSndFactor_sub_norm_sq` と prime divisibility を介して norm 側へ戻す型は後続の descent packet にも再登場する。

したがって「$H\equiv N^2\pmod5$ と $5\nmid N$ から $5\nmid H$」を一般 helper theorem として抽象化できる余地はある。

ただし現行 theorem は candidate の provenance `norm_eq_or_eq_neg` と `five_not_dvd_b` をその場で展開するため、**どの仮定が five-exclusion の根拠かが非常に明瞭** である。重複を消すために抽象化しすぎると監査性が落ちる可能性もある。

## 最適化候補

1. `hnormSq` を得る部分は、適切な divisibility algebra lemma を選べれば `ring_nf` を避けられる可能性がある。しかし現行形は符号方向に頑健で分かりやすい。
2. `N=b` / `N=-b` の二枝から `5 ∣ b` を得る処理は helper lemma としてまとめられる可能性がある。
3. `Prime (5 : ℤ)` の証明が近接 theorem で繰り返されるなら局所 lemma として共有できる。ただし `norm_num` 一行なので抽象化コストの方が大きい可能性もある。
4. より一般には
   ```lean
   5 ∣ H - N ^ 2 → ¬ 5 ∣ N → ¬ 5 ∣ H
   ```
   のような congruence-level helper を切り出す設計も考えられる。

これらは Lean build を行っていないため **未検証の最適化候補** である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

生成元 manifest の順序では本 theorem は

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

の領域に属する。

本 theorem 自体で主要な Mathlib 機能は

- 整数の divisibility
- `dvd_sub`
- `Prime.dvd_of_dvd_pow`
- `Int.dvd_neg`
- `ring_nf`
- `norm_num`
- `exact_mod_cast`
- `rw`, `rcases`, `apply`

である。

`omega`, `linarith`, `nlinarith` は本 theorem 自体では使用しない。

厳密な最小 import 集合は Lean build 禁止条件のため **未確認** である。`Mathlib` 全体から ring normalization、integer divisibility、prime、norm-cast 関係の限定 import へ縮小できる可能性はあるが、上流の `GoldenInt` / `goldenNorm` / `goldenFifthSndFactor` 定義が要求する import も合わせて検証する必要がある。

## Comparator challenge 化の可否

**適している。** 難度は中級程度である。

challenge としては次を与えるとよい。

```lean
h5b : ¬ 5 ∣ b
hnorm : N = (b : ℤ) ∨ N = -(b : ℤ)
hdiff : (5 : ℤ) ∣ H - N ^ 2
```

目標を

```lean
¬ (5 : ℤ) ∣ H
```

とする。

評価点は、

- congruence $H\equiv N^2\pmod5$ を divisibility として扱えるか
- $5\mid N^2$ から素数性により $5\mid N$ を抜けるか
- `N=±b` の符号分岐を処理できるか
- `ℤ` と `ℕ` の divisibility を `exact_mod_cast` で接続できるか
- 不要な展開や巨大な polynomial 計算に逃げず、既存 congruence lemma を使えるか

である。

単なる数値計算ではなく、prime divisibility・符号・cast・既存補題の選択を一度に試せるため、Comparator challenge として質が高い。

## PDF との対応

対象 branch の repository tree には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。tree 上の blob SHA は日本語版 `88796012a87abfb348e7c9e529332063288319a3`、英語版 `3d85ef047731caa199bc0aef9969f671998eaaab` である。

ただし GitHub コネクタでは binary PDF 本文をテキストとして取得できず、この theorem に対応する具体的ページ・節番号は **確認できなかった**。従って PDF 内容について推測による引用・位置付けは行わない。

技術的意味と Lean コードについては、現行 branch の `Flt5DkMath/FLT5StandAlone.lean` を最優先の根拠とする。

## 次に読むべき宣言

次は **0302 `GoldenZeroSectorCandidate.five_not_dvd_d`**。種別は `theorem` である。

Lean 正本では 0301 の直後に

```lean
/-- The quartic tenth-power base is not divisible by five. -/
theorem five_not_dvd_d (p : GoldenZeroSectorCandidate) : ¬ 5 ∣ p.d := by
  intro h5d
  apply p.five_not_dvd_H
  rw [p.H_eq_tenth]
  exact dvd_pow (Int.natCast_dvd.mpr h5d) (by decide : 10 ≠ 0)
```

と続く。

0301 で得た

$$
5\nmid H(r,s)
$$

と 0297 `H_eq_tenth` の

$$
H(r,s)=d^{10}
$$

を組み合わせ、split base 自身について

$$
5\nmid d
$$

を確定する段階である。