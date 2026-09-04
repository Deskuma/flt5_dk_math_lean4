# 0299 — `GoldenZeroSectorCandidate.a_eq_c_mul_d`

## 宣言種別

これは **`theorem`** である。

zero-sector candidate に保存された三つの tenth-power magnitude relation を比較し、元の tenth-power base `a` が split base `c`,`d` の積に等しいこと

$$
a=cd
$$

を取り出す。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- The original tenth-power base is exactly the product of the split bases. -/
theorem a_eq_c_mul_d (p : GoldenZeroSectorCandidate) : p.a = p.c * p.d := by
  have hprod := p.natAbs_product_eq
  rw [p.s_natAbs_eq, p.H_natAbs_eq] at hprod
  have hpows : (p.c * p.d) ^ 10 = p.a ^ 10 := by
    apply Nat.mul_left_cancel (by positivity : 0 < 5 ^ 6)
    calc
      5 ^ 6 * (p.c * p.d) ^ 10 =
          (5 ^ 6 * p.c ^ 10) * p.d ^ 10 := by ring
      _ = 5 ^ 6 * p.a ^ 10 := hprod
  exact (Nat.pow_left_injective (by norm_num : 10 ≠ 0) hpows).symm
```

結論は `ℕ` 上の等式

$$
p.a=p.c\,p.d
$$

である。

## 数学的意味

0298 `natAbs_product_eq` は

$$
|s|\,|H(r,s)|=5^6a^{10}
$$

を与える。一方、`GoldenZeroSectorCandidate` 自体は

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}
$$

を field として保持している。

これらを代入すると

$$
(5^6c^{10})d^{10}=5^6a^{10}.
$$

積のべきの公式から

$$
5^6(cd)^{10}=5^6a^{10}.
$$

$5^6>0$ なので共通因子を消去し、

$$
(cd)^{10}=a^{10}
$$

を得る。自然数では指数 $10$ のべき写像は単射なので、

$$
a=cd
$$

となる。

本 theorem は、chosen tenth-power split が単に二つの独立な magnitude expression ではなく、元の base `a` を正確に因数分解していることを保証する。

## 証明全体での役割

zero-sector inversion では `s` と quartic factor `H` の magnitude をそれぞれ tenth power として分離してきた。本 theorem により、その二つの base `c`,`d` が元の arithmetic base `a` を完全に所有することが判明する。

これは後続の coprimality・prime exclusion・parity・factor packet 解析に重要である。特に直後の 0300 `GoldenZeroSectorCandidate.coprime_c_d` は、座標と quartic factor の coprimality から `c` と `d` の coprimality を抽出する。0299 の

$$
a=cd
$$

と組み合わせると、元の base の素因子が split bases にどのように分配されるかを追跡できる。

従って本 theorem は **tenth-power magnitude split から base-level factorization へ降りる bridge** である。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate.natAbs_product_eq`

0298 の theorem。直接の出発点で、

```lean
p.s.natAbs * (goldenFifthSndFactor p.r p.s).natAbs =
  5 ^ 6 * p.a ^ 10
```

を与える。

### `GoldenZeroSectorCandidate.s_natAbs_eq`

0290 の structure field。

```lean
p.s_natAbs_eq : p.s.natAbs = 5 ^ 6 * p.c ^ 10
```

### `GoldenZeroSectorCandidate.H_natAbs_eq`

同じく structure field。

```lean
p.H_natAbs_eq :
  (goldenFifthSndFactor p.r p.s).natAbs = p.d ^ 10
```

### `Nat.mul_left_cancel`

正の共通因子 `5 ^ 6` を両辺から消去するために使う。Lean では `apply Nat.mul_left_cancel ...` により、目標を共通因子付きの等式へ持ち上げている。

### `Nat.pow_left_injective`

自然数上で固定された非零指数のべき写像が単射であることを使う。ここでは指数 `10` が非零であることを `norm_num` で証明し、

```lean
(p.c * p.d) ^ 10 = p.a ^ 10
```

から

```lean
p.c * p.d = p.a
```

を得る。最終目標は逆向きなので `.symm` する。

## 証明または構築の流れ

1. 0298 の `p.natAbs_product_eq` を `hprod` として取得する。
2. `rw [p.s_natAbs_eq, p.H_natAbs_eq] at hprod` により magnitude fields を代入する。
3. 新しい中間目標
   $$
   (cd)^{10}=a^{10}
   $$
   を `hpows` として立てる。
4. `Nat.mul_left_cancel` を用い、両辺に共通因子 $5^6$ を付けた等式を示せばよい形にする。
5. `ring` で
   $$
   5^6(cd)^{10}=(5^6c^{10})d^{10}
   $$
   を正規化する。
6. その式を `hprod` へ接続して `hpows` を得る。
7. `Nat.pow_left_injective` で tenth powers の等式から bases の等式を戻し、`.symm` で目標の向きに揃える。

## Lean 固有の処理

数学では「$5^6$ を約分する」と一言で済むが、`ℕ` は体ではないため Lean では除算ではなく cancellative multiplication を使う。現行実装の

```lean
apply Nat.mul_left_cancel (by positivity : 0 < 5 ^ 6)
```

は、この cancellation を自然数の乗法構造として明示している。

また

```lean
ring
```

は

$$
(cd)^{10}=c^{10}d^{10}
$$

を含む積・べきの再配置を正規化する役割を担う。

最後の `Nat.pow_left_injective` は、実数上の単調性ではなく自然数上の algebraic injectivity を直接使う点が適切である。

## 冗長・重複箇所

0296 `s_eq_neg_five_pow_mul_tenth` と 0297 `H_eq_tenth` から signed equations を掛け合わせても同種の base relation を導ける可能性はある。しかし現行 theorem は 0298 と structure fields の magnitude data だけを使うため、符号処理への依存を持たない。

これは重複というより、**符号層と magnitude factorization 層を分離した設計** と見るのが自然である。

一方、`hpows` の証明で `Nat.mul_left_cancel` のためにいったん共通因子を付け直す構成は少し回り道にも見える。既存の cancellation lemma や `omega`/`nlinarith` 的処理ではなく、自然数乗法の構造を明示するための選択と解釈できる。

## 最適化候補

1. `ring` をより局所的な `pow_mul` / `mul_assoc` 等の rewrite へ置き換えれば、ring tactic への依存を減らせる可能性がある。
2. `5 ^ 6` の非零性または正性を `norm_num` で処理し、別の cancellation lemma を用いて `hpows` を短縮できる可能性がある。
3. `Nat.pow_left_injective` の向きを工夫すれば最後の `.symm` を避けられる可能性があるが、現行形は読みやすい。
4. 0298 と本 theorem を統合して直接 `a = c*d` を証明することも可能だが、magnitude bridge と base factorization を分離している現在の API の方が再利用性は高い。

これらは Lean build を行っていないため **未検証** である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem 自体で主要な Mathlib 機能は

- `Nat.mul_left_cancel`
- `Nat.pow_left_injective`
- `positivity`
- `ring`
- `norm_num`
- `rw`
- 自然数のべき・乗法 API

である。

`omega`, `linarith`, `nlinarith`, `exact_mod_cast` は本 theorem 自体では使わない。

generated-source 側ではこの宣言は zero-sector inversion 層、すなわち従来の manifest 対応では `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` に属する。厳密な最小 import 集合は Lean build 禁止条件のため **未確認** である。

## Comparator challenge 化の可否

**適している。** 難度は中程度である。

例えば結論だけを提示し、使用可能な入力として

```lean
p.natAbs_product_eq
p.s_natAbs_eq
p.H_natAbs_eq
```

を与える。

評価点は、

- magnitude fields を適切に rewrite できるか
- $(cd)^{10}=a^{10}$ を中間目標として発見できるか
- 自然数では「割る」のではなく cancellation を使うことを理解しているか
- `Nat.pow_left_injective` を発見できるか
- `ring` を必要最小限に使えるか

である。

単なる tactic puzzle ではなく、型付き算術で cancellation と power injectivity をどう組み合わせるかを見る challenge になる。

## PDF との対応

対象 branch の repository tree には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

GitHub 上で blob の存在は確認できたが、今回の通常取得経路では PDF binary 本文を解析できず、raw PDF の直接取得も利用できなかった。そのため具体的なページ番号・節番号・本 theorem に相当する説明位置は **確認できていない**。推測による対応付けは行わない。

技術的内容については現行 branch の `Flt5DkMath/FLT5StandAlone.lean` を最優先の根拠とする。

## 次に読むべき宣言

次は **0300 `GoldenZeroSectorCandidate.coprime_c_d`**。種別は `theorem` である。

Lean 正本では 0299 の直後にあり、

```lean
/-- The two split tenth-power bases inherit coprimality. -/
theorem coprime_c_d (p : GoldenZeroSectorCandidate) :
    Nat.Coprime p.c p.d := by
  have hcop := coprime_natAbs_goldenFifthSndFactor_of_coprime
    p.r p.s p.coprime_coords
  have hc : p.c ∣ p.s.natAbs := by
    rw [p.s_natAbs_eq]
    exact dvd_mul_of_dvd_right (dvd_pow_self p.c (by decide : 10 ≠ 0)) _
  have hd : p.d ∣ (goldenFifthSndFactor p.r p.s).natAbs := by
    rw [p.H_natAbs_eq]
    exact dvd_pow_self p.d (by decide : 10 ≠ 0)
  exact (hcop.of_dvd_left hc).of_dvd_right hd
```

という形である。

0299 で base-level factorization $a=cd$ を確定した後、0300 では split bases 自身が互いに素であることを確定する。これにより後続の prime ownership と valuation 分離の準備が整う。