# 0296 — `GoldenZeroSectorCandidate.s_eq_neg_five_pow_mul_tenth`

## 宣言種別

これは **`theorem`** である。

zero-sector candidate が保持している visible coordinate `s` の absolute-value tenth-power split に、0293 `GoldenZeroSectorCandidate.s_neg` で確定した負符号を戻し、符号付きの exact equation を復元する。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- Exact sign removal for the visible coordinate. -/
theorem s_eq_neg_five_pow_mul_tenth (p : GoldenZeroSectorCandidate) :
    p.s = -((5 : ℤ) ^ 6 * (p.c : ℤ) ^ 10) := by
  have habs : (p.s.natAbs : ℤ) =
      (5 : ℤ) ^ 6 * (p.c : ℤ) ^ 10 := by
    exact_mod_cast p.s_natAbs_eq
  have hsabs : (p.s.natAbs : ℤ) = -p.s :=
    Int.ofNat_natAbs_of_nonpos p.s_neg.le
  linarith
```

結論は

$$
p.s=-5^6p.c^{10}
$$

である。

## 数学的意味

0290 `GoldenZeroSectorCandidate` は

$$
|p.s|=5^6p.c^{10}
$$

に対応する field

```lean
p.s_natAbs_eq : p.s.natAbs = 5 ^ 6 * p.c ^ 10
```

を保持している。一方、0293 `p.s_neg` により

$$
p.s<0
$$

が分かっている。

負の整数では $|s|=-s$ なので

$$
-p.s=5^6p.c^{10}.
$$

従って

$$
p.s=-5^6p.c^{10}
$$

となる。

ここで 0294 `c_pos` は数学的には整合的な非退化情報だが、本 theorem の Lean 証明では直接使わない。符号除去に必要なのは `s_natAbs_eq` と `s_neg` だけである。

## 証明全体での役割

zero-sector arithmetic 層から渡される split は

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}
$$

という absolute-value 形式である。0296 はそのうち `s` 側を signed arithmetic に戻す。

直後の 0297 `GoldenZeroSectorCandidate.H_eq_tenth` は、0292 の $H>0$ を用いて

$$
H(r,s)=d^{10}
$$

を復元する。したがって 0296–0297 は対になって

$$
s=-5^6c^{10},
\qquad
H=d^{10}
$$

を確定し、その後の `natAbs_product_eq`、`a_eq_c_mul_d`、`coprime_c_d`、inversion factorization へ渡す exact signed data を整える。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate.s_natAbs_eq`

0290 の structure field。

```lean
p.s_natAbs_eq : p.s.natAbs = 5 ^ 6 * p.c ^ 10
```

本 theorem の magnitude 情報の唯一の直接 source である。

### `GoldenZeroSectorCandidate.s_neg`

0293 の theorem。

```lean
theorem s_neg (p : GoldenZeroSectorCandidate) : p.s < 0
```

これを `.le` により `p.s ≤ 0` へ弱め、整数の absolute-value identity に渡す。

### `Int.ofNat_natAbs_of_nonpos`

`p.s ≤ 0` から

```lean
(p.s.natAbs : ℤ) = -p.s
```

を得る。`natAbs` は `ℕ` 値なので、左辺は整数へ cast されている。

### `exact_mod_cast`

自然数等式 `p.s_natAbs_eq` を整数等式

```lean
(p.s.natAbs : ℤ) = (5 : ℤ) ^ 6 * (p.c : ℤ) ^ 10
```

へ移す。

### `linarith`

二つの整数等式

```lean
habs   : (p.s.natAbs : ℤ) = (5 : ℤ)^6 * (p.c : ℤ)^10
hsabs  : (p.s.natAbs : ℤ) = -p.s
```

から最終等式を閉じる。

## 証明の流れ

1. `p.s_natAbs_eq` を `exact_mod_cast` で `ℤ` 上へ持ち上げる。
2. `p.s_neg.le` と `Int.ofNat_natAbs_of_nonpos` により $|s|=-s$ を得る。
3. 両式の左辺が同じ `(p.s.natAbs : ℤ)` なので `linarith` で消去し、$s=-5^6c^{10}$ を得る。

本質的には「magnitude + sign = signed value」という処理であり、zero-sector 固有の難しい代数はここでは既に終了している。

## Lean 固有の処理

数学では $s<0$ ならただちに $|s|=-s$ と書けるが、Lean では `Int.natAbs` が `ℕ` 値であるため型の橋渡しが必要になる。

`p.s_natAbs_eq` は `ℕ` の等式、最終結論は `ℤ` の等式なので `exact_mod_cast` が cast をまとめて処理する。一方 `Int.ofNat_natAbs_of_nonpos` は `(s.natAbs : ℤ)` と `-s` を直接結ぶため、以後は整数線形算術として扱える。

また `p.s_neg : p.s < 0` から必要な仮定 `p.s ≤ 0` への変換は `.le` で行う。

## 冗長・重複箇所

0297 `H_eq_tenth` と構造的に対称である。0296 は負側なので

$$
|s|=-s,
$$

0297 は正側なので

$$
|H|=H
$$

を使う。

ただし Lean API はそれぞれ `Int.ofNat_natAbs_of_nonpos` と `Int.ofNat_natAbs_of_nonneg` になり、符号方向も異なるため、無理に共通化すると可読性を落とす可能性が高い。

`habs` と `hsabs` の二つの名前付き中間式は短縮可能ではあるが、magnitude 情報と sign 情報の出所を明示しており教材上は有用である。

## 最適化候補

1. `linarith` は単純な等式置換だけを行っているため、`rw` / `calc` / `omega` などで tactic dependency を縮められる可能性がある。
2. 例えば `hsabs` を `habs` に rewrite してから対称性を整える proof term にできる可能性がある。ただし exact な最短形は Lean build を行っていないため未検証である。
3. 0296–0297 を「natAbs equality + sign から signed equality」を得る一般補題へ抽象化することも可能だが、二本だけなら現行の方が proof graph の意味が明瞭である。

現行証明は短く、cast と sign removal の役割分担も明快である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。本宣言を含む generated source は章境界コメント上

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

に対応する。

本 theorem 自体が直接利用する主な機能は

- `exact_mod_cast`
- `Int.ofNat_natAbs_of_nonpos`
- order projection `.le`
- `linarith`
- `GoldenZeroSectorCandidate.s_neg`

である。

`ring`, `nlinarith`, `positivity`, `omega`, `norm_num` は本 theorem 自体では使わない。

指定に従い Lean build は実行していないため、`import Mathlib` をどの個別 import へ縮小できるかは **未検証** である。特に `exact_mod_cast` と `linarith`、および前段の candidate API を合わせた module 全体の最小 import 集合は断定しない。

## Comparator challenge 化の可否

**適している。** 難度は低～中程度である。

比較できるのは、`natAbs` の型が `ℕ` であることを認識し、`exact_mod_cast` で整数へ運ぶ能力、既存の `s_neg` を発見して `Int.ofNat_natAbs_of_nonpos` に接続する能力、そして sign + magnitude から exact signed equation を復元する能力である。

例えば

```lean
theorem challenge (p : GoldenZeroSectorCandidate) :
    p.s = -((5 : ℤ) ^ 6 * (p.c : ℤ) ^ 10) := by
  ...
```

とし、`p.s_natAbs_eq` と `p.s_neg` の利用を許可する形式が自然である。

## PDF との対応

対象 branch の repository tree には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

ただし GitHub コネクタでは PDF binary 本文を解析可能なテキストとして取得できないため、PDF 内の具体的ページ番号・節番号・本 theorem と一致する記述位置は **確認できていない**。ここでは現行 Lean 正本 `Flt5DkMath/FLT5StandAlone.lean` を最優先の根拠とし、PDF の具体的内容について推測は行わない。

## 次に読むべき宣言

次は **0297 `GoldenZeroSectorCandidate.H_eq_tenth`**。種別は `theorem` である。

```lean
/-- Exact sign removal for the positive quartic factor. -/
theorem H_eq_tenth (p : GoldenZeroSectorCandidate) :
    goldenFifthSndFactor p.r p.s = (p.d : ℤ) ^ 10 := by
  have habs : ((goldenFifthSndFactor p.r p.s).natAbs : ℤ) =
      (p.d : ℤ) ^ 10 := by
    exact_mod_cast p.H_natAbs_eq
  rw [Int.ofNat_natAbs_of_nonneg p.H_pos.le] at habs
  exact habs
```

0296 が負の visible coordinate の absolute value を外したのに対し、0297 は 0292 の $H>0$ を用いて quartic factor の absolute value を外し、

$$
H(p.r,p.s)=p.d^{10}
$$

を exact form として復元する。