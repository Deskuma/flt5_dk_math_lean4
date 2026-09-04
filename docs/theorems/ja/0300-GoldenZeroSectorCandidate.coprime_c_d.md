# 0300 — `GoldenZeroSectorCandidate.coprime_c_d`

## 宣言種別

これは **`theorem`** である。

zero-sector candidate に保存された primitive coordinate の互いに素性と、二つの tenth-power magnitude 表現から、split base `c`,`d` 自身が互いに素であること

$$
\gcd(c,d)=1
$$

を取り出す。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

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

結論は `ℕ` 上の coprimality 命題

```lean
Nat.Coprime p.c p.d
```

である。

## 数学的意味

まず primitive coordinates から既に

$$
\gcd\bigl(|s|,|H(r,s)|\bigr)=1
$$

が得られている。

一方 candidate は

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}
$$

を保持する。したがって

$$
c\mid |s|
$$

かつ

$$
d\mid |H(r,s)|.
$$

互いに素な二つの自然数の約数をそれぞれ一つずつ取れば、その約数どうしも互いに素である。ゆえに

$$
\gcd(c,d)=1.
$$

ここで重要なのは tenth power を直接「根に戻す」必要がないことである。`c` が左側 magnitude の約数、`d` が右側 magnitude の約数であることだけで十分であり、coprimality は divisibility に沿って下方継承する。

## 証明全体での役割

0299 `a_eq_c_mul_d` では

$$
a=cd
$$

を得た。本 theorem ではさらに

$$
\gcd(c,d)=1
$$

を得る。

この二つを合わせると、元の tenth-power base `a` は、共通素因子を持たない二つの split base へ分解されていることになる。すなわち、`a` の prime support は `c` 側と `d` 側へ重複なく分配される。

これは後続の prime-five exclusion、parity、valuation、factor packet の解析で重要な構造である。単に

$$
a=cd
$$

だけでは、ある素数が `c` と `d` の双方に重複している可能性が残る。本 theorem がその重複を排除する。

従って 0299 と 0300 の組は、**magnitude split を coprime base factorization に昇格させる段階** と位置付けられる。

## 直接依存する定義・補題

### `coprime_natAbs_goldenFifthSndFactor_of_coprime`

本 theorem の主要な上流補題である。

```lean
theorem coprime_natAbs_goldenFifthSndFactor_of_coprime
    (r s : ℤ) (hrs : Nat.Coprime r.natAbs s.natAbs) :
    Nat.Coprime s.natAbs (goldenFifthSndFactor r s).natAbs
```

primitive coordinate 条件

```lean
Nat.Coprime r.natAbs s.natAbs
```

から、visible coordinate `s` と quartic factor `H(r,s)` の natural absolute values が互いに素であることを与える。

### `GoldenZeroSectorCandidate.coprime_coords`

0290 `GoldenZeroSectorCandidate` の structure field。

```lean
p.coprime_coords : Nat.Coprime p.r.natAbs p.s.natAbs
```

上の coprimality 補題へ渡される provenance である。

### `GoldenZeroSectorCandidate.s_natAbs_eq`

同じく structure field。

```lean
p.s_natAbs_eq : p.s.natAbs = 5 ^ 6 * p.c ^ 10
```

これにより `p.c ∣ p.s.natAbs` を得る。

### `GoldenZeroSectorCandidate.H_natAbs_eq`

同じく structure field。

```lean
p.H_natAbs_eq :
  (goldenFifthSndFactor p.r p.s).natAbs = p.d ^ 10
```

これにより `p.d ∣ |H|` を得る。

### `dvd_pow_self`

指数が非零なら base は自分自身の power を割る、という divisibility を使う。

```lean
dvd_pow_self p.c (by decide : 10 ≠ 0)
```

および

```lean
dvd_pow_self p.d (by decide : 10 ≠ 0)
```

で tenth power への divisibility を構成している。

### `dvd_mul_of_dvd_right`

`c ∣ c^10` から

$$
c\mid 5^6c^{10}
$$

へ持ち上げるために使う。

### `Nat.Coprime.of_dvd_left` / `Nat.Coprime.of_dvd_right`

既知の

$$
\gcd(|s|,|H|)=1
$$

から、それぞれの約数 `c`,`d` へ coprimality を降ろす核心 API である。

## 証明または構築の流れ

1. `p.coprime_coords` を `coprime_natAbs_goldenFifthSndFactor_of_coprime` に渡し、
   $$
   \gcd(|s|,|H|)=1
   $$
   を `hcop` として得る。
2. `p.s_natAbs_eq` で $|s|=5^6c^{10}$ と書き換える。
3. `dvd_pow_self` により $c\mid c^{10}$ を得て、`dvd_mul_of_dvd_right` により
   $$
   c\mid |s|
   $$
   を `hc` として得る。
4. `p.H_natAbs_eq` で $|H|=d^{10}$ と書き換える。
5. `dvd_pow_self` により
   $$
   d\mid |H|
   $$
   を `hd` として得る。
6. `hcop.of_dvd_left hc` で左側を `|s|` から `c` へ縮める。
7. `.of_dvd_right hd` で右側を `|H|` から `d` へ縮め、`Nat.Coprime p.c p.d` を得る。

## Lean 固有の処理

数学では「$c$ は $5^6c^{10}$ の約数」「$d$ は $d^{10}$ の約数」は自明に見える。しかし Lean では指数が `0` の場合を一般 API が区別するため、

```lean
(by decide : 10 ≠ 0)
```

で指数 `10` の非零性を型付きで供給している。

`decide` を使えるのは `10 ≠ 0` が decidable proposition であり、閉じた数値命題だからである。

また最後の

```lean
(hcop.of_dvd_left hc).of_dvd_right hd
```

は coprimality の「約数への遺伝」を二段階で表現している。gcd を直接計算したり素因数を列挙したりせず、`Nat.Coprime` の抽象 API のみで閉じている点が本証明の特徴である。

## 冗長・重複箇所

`p.s_natAbs_eq` と `p.H_natAbs_eq` は tenth-power split を表すため、別経路として

$$
\gcd(5^6c^{10},d^{10})=1
$$

へ書き換えた後、power の coprimality から `Coprime c d` を取り出す構成も考えられる。

しかし現行実装はそこまで強い rewrite や power-coprimality lemma を必要とせず、単に

$$
c\mid |s|,
\qquad
d\mid |H|
$$

を示して既存 coprimality を縮小している。この方が依存 API が少なく、数学的にも一般的である。

また 0299 `a_eq_c_mul_d` は本 theorem では使用されない。これは意図的な層分離と見るべきである。`a=cd` は product magnitude 由来、本 theorem は primitive coordinate coprimality 由来であり、二つの情報源を独立に保っている。

## 最適化候補

1. `hc` の証明は `simp [p.s_natAbs_eq, dvd_pow_self]` 系で短縮できる可能性があるが、現行形は divisibility の由来が明示的である。
2. `by decide : 10 ≠ 0` は `by norm_num` でも処理できる可能性がある。現行の `decide` は小さく依存も軽い。
3. `hcop` を完全に rewrite してから `Coprime` の power lemma を使う別証明も可能と思われるが、より多くの Mathlib API に依存する可能性が高い。
4. `c ∣ |s|` と `d ∣ |H|` が後続でも再利用されるなら helper theorem として切り出す余地がある。ただし現時点の正本で再利用が確認できないため、これは **推測的な最適化候補** である。

Lean build は行っていないため、これらの短縮案は **未検証** である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

manifest 上では本宣言を含む領域は

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

に対応する。

本 theorem 自体で主要な Mathlib 機能は

- `Nat.Coprime`
- `Nat.Coprime.of_dvd_left`
- `Nat.Coprime.of_dvd_right`
- `dvd_pow_self`
- `dvd_mul_of_dvd_right`
- `rw`
- `decide`
- 自然数の divisibility / power API

である。

`ring`, `omega`, `linarith`, `nlinarith`, `norm_num`, `exact_mod_cast` は本 theorem 自体では使用しない。

厳密な最小 import 集合は Lean build 禁止条件のため **未確認** である。`import Mathlib` から divisibility・coprimality 関係の限定 module へ縮小できる可能性は高いが、上流定義・補題が要求する import まで含めた確認が必要である。

## Comparator challenge 化の可否

**適している。** 難度は初中級から中級程度である。

例えば次だけを与える。

```lean
hcop : Nat.Coprime p.s.natAbs
  (goldenFifthSndFactor p.r p.s).natAbs
p.s_natAbs_eq : p.s.natAbs = 5 ^ 6 * p.c ^ 10
p.H_natAbs_eq :
  (goldenFifthSndFactor p.r p.s).natAbs = p.d ^ 10
```

目標を

```lean
Nat.Coprime p.c p.d
```

とする。

評価点は、

- tenth-power equality 全体を操作するのではなく divisibility を抽出できるか
- `dvd_pow_self` を発見できるか
- `Nat.Coprime.of_dvd_left/right` による downward inheritance を使えるか
- 不要な素因数分解や gcd 計算を避けられるか

である。

短い証明だが、`Coprime` を「gcd = 1 の計算問題」ではなく divisibility に対して安定な構造として扱えるかを見る良い challenge になる。

## PDF との対応

対象 branch の repository tree には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在する。日本語 PDF の blob SHA は `88796012a87abfb348e7c9e529332063288319a3` であることも確認した。

ただし今回の GitHub コネクタによる binary 取得では本文 content が返らず、PDF の具体的ページ・節番号・本 theorem に相当する説明位置を **確認できなかった**。従って推測による PDF 対応付けは行わない。

技術的内容については現行 branch の `Flt5DkMath/FLT5StandAlone.lean` を最優先の根拠とする。

## 次に読むべき宣言

次は **0301 `GoldenZeroSectorCandidate.five_not_dvd_H`**。種別は `theorem` である。

Lean 正本では 0300 の直後に

```lean
/-- The quartic factor retains the packet's exclusion of the prime five. -/
theorem five_not_dvd_H (p : GoldenZeroSectorCandidate) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor p.r p.s := by
  ...
```

と続く。

0300 で split bases の coprimalityを確定した後、0301 では quartic factor `H` そのものから prime `5` を排除する。これは後に `d` 側へ `5 ∤ d` を降ろし、five-adic ownership を分離するための次段階になる。