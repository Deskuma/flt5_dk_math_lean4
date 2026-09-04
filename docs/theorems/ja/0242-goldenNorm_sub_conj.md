# 0242 — `goldenNorm_sub_conj`

## Lean の型

```lean
/-- The norm of the conjugate difference is `-5` times the square coordinate. -/
theorem goldenNorm_sub_conj (x : GoldenInt) :
    goldenNorm (x - goldenConj x) = -5 * x.snd ^ 2 := by
  rw [golden_sub_conj_eq_snd_mul_sqrtFive, goldenNorm_mul,
    goldenNorm_sqrtFive]
  simp [goldenNorm, goldenOfInt]
  ring
```

これは `theorem` であり、黄金整数 `x` とその共役との差のノルムが、第二座標 `x.snd` の平方に `-5` を掛けた整数へ完全に落ちることを示す。

## 数学的主張

`x = a + bφ` とする。0241 で

$$
x-\overline{x}=b\sqrt5
$$

が既に証明されている。また黄金ノルムは乗法的で、

$$
N(\sqrt5)=-5
$$

である。したがって

$$
N(x-\overline{x})
=N(b\sqrt5)
=N(b)N(\sqrt5).
$$

埋め込まれた整数 `b` のノルムは `b^2` なので、

$$
N(x-\overline{x})
=b^2(-5)
=-5b^2.
$$

Lean の statement はこれをそのまま

```lean
goldenNorm (x - goldenConj x) = -5 * x.snd ^ 2
```

と表している。

## 証明全体での役割

0241 は共役との差を

$$
x-\overline{x}=x_{\mathrm{snd}}\sqrt5
$$

と因数分解した。本 theorem はその factorization を **整数ノルムの質量公式** へ変換する。

`SignedGoldenRamifierStrippedPacket` の `beta` には

$$
\beta_{\mathrm{snd}}=-5^7a^{10}
$$

という explicit coordinate が保存されている。したがって本 theorem を `x = beta` に適用すると、次の 0243 で

$$
N(\beta-\overline\beta)
=-5\,(-5^7a^{10})^2
=-5^{15}a^{20}
$$

が得られる。

一方、stripped packet では

$$
N(\beta)=b^5
$$

である。`beta` と `conj beta` の共通因子 `d` は両方を割るので、0191 `goldenDivides_sub` により差も割る。0192 `goldenNorm_dvd_of_goldenDivides` でノルムへ移せば、`N(d)` は

$$
b^5
$$

と

$$
5^{15}a^{20}
$$

の双方を割る。power-split 側の coprimality と `5 ∤ b` を使えば、最終的に `|N(d)| = 1` が強制され、0201/0202 の unit criterion により `d` は unit になる。

したがって 0242 は、共役差という黄金整数内部の量を、後続の整数整除・互いに素性 argument で扱える explicit integer mass に変換する中心的な橋である。

## 直接依存する定義・補題

proof が直接使用する named theorem は次の三つである。

- 0241 `golden_sub_conj_eq_snd_mul_sqrtFive`
- 0174 `goldenNorm_mul`
- 0182 `goldenNorm_sqrtFive`

さらに simplification のため、次の定義が展開される。

- 0164 `goldenNorm`
- 0162 `goldenOfInt`

statement 自体は次にも依存する。

- `GoldenInt`
- 0163 `goldenConj`

概念的には

$$
x-\overline{x}=x_{\mathrm{snd}}\sqrt5
$$

と

$$
N(xy)=N(x)N(y),\qquad N(\sqrt5)=-5
$$

を合成した theorem である。

## 証明の流れ

proof は三段階である。

### 1. 共役差を因数分解する

```lean
rw [golden_sub_conj_eq_snd_mul_sqrtFive]
```

これにより左辺は

```lean
goldenNorm (goldenMul (goldenOfInt x.snd) sqrtFiveElement)
```

の形になる。

### 2. ノルム乗法性と平方根5のノルムを適用する

```lean
rw [goldenNorm_mul, goldenNorm_sqrtFive]
```

これで

$$
N(goldenOfInt(x.snd))\cdot(-5)
$$

へ落ちる。

### 3. 整数埋め込みのノルムを展開する

```lean
simp [goldenNorm, goldenOfInt]
ring
```

`goldenOfInt x.snd = ⟨x.snd,0⟩` なので、ノルムは `x.snd ^ 2` に簡約される。最後に積の順序と符号を `ring` で正規化し、

$$
-5*x.snd^2
$$

へ一致させる。

## Lean 固有の処理

最初の `rw` は 0241 を theorem-level API として再利用しており、共役や `sqrtFiveElement` の座標をここで再展開しない。これは 0241 を named factorization theorem として切り出した効果が直接現れる箇所である。

`goldenNorm_mul` は raw operation `goldenMul` に対する theorem なので、0241 の右辺が raw multiplication で表されていることも proof を短くしている。

`goldenNorm_sqrtFive` は `sqrtFiveElement` が `abbrev` として `goldenSqrtFive` に透明展開されるため適用できる。alias 層と internal definition の definitional transparency を利用している。

最後の `simp [goldenNorm, goldenOfInt]` は `goldenNorm_ofInt` を使わず、整数埋め込みのノルムを定義から再計算している。これは後述の軽い重複候補である。

## 冗長・重複箇所

最も明確な重複候補は、0169 `goldenNorm_ofInt` が既に

```lean
@[simp] theorem goldenNorm_ofInt (a : ℤ) :
    goldenNorm (goldenOfInt a) = a ^ 2 := by
  simp [goldenNorm, goldenOfInt]
```

を提供している点である。

したがって現在の

```lean
simp [goldenNorm, goldenOfInt]
```

は、既存 API を使えばより高水準に置き換えられる可能性がある。

また 0241 と 0242 は常に連続して利用される factorization / norm pair であり、後続 consumer が必要とするのがノルム公式だけなら、0241 を経由せず座標から一度に示すことも可能である。しかし現行の二段構成は、

1. 黄金整数としての factorization
2. 整数ノルムとしての mass formula

を分離しており、数学的意味の監査にはむしろ有益である。

## 最適化候補

1. **`goldenNorm_ofInt` を再利用する**

   `goldenNorm (goldenOfInt x.snd)` を既存 theorem で `x.snd ^ 2` へ落とせば、定義展開への依存を減らせる。

2. **`simpa` を使う短縮形を検討する**

   0241、`goldenNorm_mul`、`goldenNorm_sqrtFive`、`goldenNorm_ofInt` を組み合わせれば、現在の `simp + ring` より高水準な proof が可能かもしれない。ただし今回は Lean build を行わないため未検証である。

3. **共役を `RingEquiv` として bundle する**

   共役の algebraic API を bundle すれば、`x * conj x = N(x)` や anti-invariant part の一般 theorem をより構造的に扱える。

4. **一般 quadratic-order theorem へ抽象化する**

   判別式 `5` の二次環では、共役差のノルムが discriminant と anti-invariant coordinate の平方で表される。本 theorem はその具体例なので、一般 quadratic form API の特殊化にできる可能性がある。

5. **0241–0243 を一つの conjugate-difference mass API として整理する**

   0241 が generic factorization、0242 が generic norm formula、0243 が stripped packet への specialization という三層になっており、namespace と theorem naming を揃えると downstream の探索性が上がる。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が直接使う Mathlib 表面は比較的小さい。

- equality rewriting `rw`
- simplifier `simp`
- integer polynomial normalization `ring`

主要な数学依存は project 内の golden-order theorem である。

宣言単独では `Mathlib` 全体よりかなり小さい import で足りる可能性が高いが、`SignedGoldenConjugateCoprime.lean` 全体では整数整除、`natAbs`、coprimality、unit 判定などを使うため、最小 import は module 単位で測る必要がある。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行の `rw` chain + `simp` + `ring`
- B: `goldenNorm_ofInt` を積極的に再利用する高水準 proof
- C: 0241 を使わず `goldenNorm` / `goldenConj` を直接座標展開する proof
- D: 共役を `RingEquiv` として bundle した抽象 proof
- E: 一般 quadratic-order / discriminant theorem の特殊化

比較軸は proof 長、直接依存、定義展開量、数学的 provenance の可視性、raw coordinate API 依存、一般化可能性である。

A は現行 API の連結性をよく示し、B は既存 theorem 再利用率を上げ、C は依存を浅くする。D/E は設計全体の抽象化余地を測る課題になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` generated section である。

正本 source では 0241 の直後に本 theorem があり、その直後に packet specialization

```lean
theorem SignedGoldenRamifierStrippedPacket.norm_sub_conj_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    goldenNorm (p.beta - goldenConj p.beta) =
      -((5 : ℤ) ^ 15 * (p.exceptional.powerSplit.a : ℤ) ^ 20) := by
  rw [goldenNorm_sub_conj, p.beta_snd]
  ring
```

が続くことを確認している。

既存の日英 PDF に対応する具体的ページ・節番号は今回直接特定していないため、PDF ページ番号は推測しない。

## 次に読むべき宣言

依存順の次は **0243 `SignedGoldenRamifierStrippedPacket.norm_sub_conj_eq`** である。

```lean
/-- The packet coordinate makes the conjugate-difference norm explicit. -/
theorem SignedGoldenRamifierStrippedPacket.norm_sub_conj_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    goldenNorm (p.beta - goldenConj p.beta) =
      -((5 : ℤ) ^ 15 * (p.exceptional.powerSplit.a : ℤ) ^ 20) := by
  rw [goldenNorm_sub_conj, p.beta_snd]
  ring
```

0242 が任意の `x` に対して

$$
N(x-\overline{x})=-5x_{\mathrm{snd}}^2
$$

を与えたので、0243 は stripped packet の explicit coordinate

$$
\beta_{\mathrm{snd}}=-5^7a^{10}
$$

を代入し、

$$
N(\beta-\overline\beta)=-5^{15}a^{20}
$$

という exact integer mass へ特殊化する。これが共通因子ノルムを `b^5` と five-adic mass の双方へ拘束する次の直接入力になる。
