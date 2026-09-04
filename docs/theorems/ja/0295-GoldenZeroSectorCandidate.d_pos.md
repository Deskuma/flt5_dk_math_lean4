# 0295 — `GoldenZeroSectorCandidate.d_pos`

## 宣言種別

これは **`theorem`** である。

0294 `GoldenZeroSectorCandidate.c_pos` が visible coordinate 側の tenth-power base `c` の正性を確定したのに対し、本 theorem は quartic factor 側の base `d` が 0 ではありえないことを示す。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- The tenth-power base in the quartic factor is nonzero. -/
theorem d_pos (p : GoldenZeroSectorCandidate) : 0 < p.d := by
  by_contra hd
  have hd0 : p.d = 0 := Nat.eq_zero_of_not_pos hd
  have hHAbsZero : (goldenFifthSndFactor p.r p.s).natAbs = 0 := by
    simpa [hd0] using p.H_natAbs_eq
  have hH0 : goldenFifthSndFactor p.r p.s = 0 :=
    Int.natAbs_eq_zero.mp hHAbsZero
  have hHpos := p.H_pos
  omega
```

結論は

$$
0<p.d
$$

である。`p.d : ℕ` なので、quartic factor の tenth-power base が非零であることを、後段で扱いやすい自然数の正性として与えている。

## 数学的意味

0290 `GoldenZeroSectorCandidate` は quartic factor

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s)
$$

について

$$
|H(p.r,p.s)|=p.d^{10}
$$

に対応する field `H_natAbs_eq` を保持している。

一方 0292 `GoldenZeroSectorCandidate.H_pos` により

$$
H(p.r,p.s)>0
$$

が既に分かっている。

もし $p.d=0$ なら

$$
|H(p.r,p.s)|=0^{10}=0
$$

なので

$$
H(p.r,p.s)=0
$$

となる。しかしこれは $H(p.r,p.s)>0$ と矛盾する。したがって

$$
p.d\neq0,
$$

自然数なので

$$
0<p.d
$$

が従う。

## 証明全体での役割

zero-sector arithmetic から inversion 層へ渡された tenth-power split は

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}
$$

という absolute-value 形式である。

0293 で $s<0$、0294 で $c>0$ を得た後、本 theorem は $d>0$ を確定する。これにより二つの split base `c`,`d` がとも退化していないことが保証される。

この正性は単なる補助情報ではない。直後の 0296 `s_eq_neg_five_pow_mul_tenth` と 0297 `H_eq_tenth` では absolute value を外して

$$
s=-5^6c^{10},
\qquad
H=d^{10}
$$

という符号付き exact form を復元する。その後 `a_eq_c_mul_d`、`coprime_c_d`、さらに inversion factorization へ進むため、0294–0295 は absolute-value split から exact signed arithmetic へ移る直前の非退化保証である。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate`

0290 の `structure`。本 theorem が直接利用する field は

```lean
p.d : ℕ
p.r : ℤ
p.s : ℤ
p.H_natAbs_eq :
  (goldenFifthSndFactor p.r p.s).natAbs = p.d ^ 10
```

である。

### `GoldenZeroSectorCandidate.H_pos`

0292 の theorem。

```lean
theorem H_pos (p : GoldenZeroSectorCandidate) :
    0 < goldenFifthSndFactor p.r p.s
```

quartic factor が 0 ではないことを最終的に保証する主要依存である。

### `Nat.eq_zero_of_not_pos`

`by_contra hd` により得た

```lean
hd : ¬ 0 < p.d
```

を、自然数上の

```lean
p.d = 0
```

へ変換する。

### `Int.natAbs_eq_zero`

```lean
(goldenFifthSndFactor p.r p.s).natAbs = 0
```

から元の整数値

```lean
goldenFifthSndFactor p.r p.s = 0
```

を得る。

### `simpa`

`p.d = 0` を `p.H_natAbs_eq` に代入し、`0 ^ 10` を 0 へ簡約する。

### `omega`

最後の

```lean
hH0   : goldenFifthSndFactor p.r p.s = 0
hHpos : 0 < goldenFifthSndFactor p.r p.s
```

の矛盾を閉じる。

## 証明の流れ

### 1. `d` の正性を否定する

```lean
by_contra hd
```

### 2. 自然数 `d` を 0 に固定する

```lean
have hd0 : p.d = 0 := Nat.eq_zero_of_not_pos hd
```

自然数では `¬ 0 < d` は `d=0` を意味する。

### 3. tenth-power split から `|H|=0` を得る

```lean
have hHAbsZero : (goldenFifthSndFactor p.r p.s).natAbs = 0 := by
  simpa [hd0] using p.H_natAbs_eq
```

これは

$$
|H|=d^{10}
$$

へ $d=0$ を代入しただけである。

### 4. `natAbs = 0` を整数等式へ戻す

```lean
have hH0 : goldenFifthSndFactor p.r p.s = 0 :=
  Int.natAbs_eq_zero.mp hHAbsZero
```

### 5. 0292 の strict positivity と矛盾させる

```lean
have hHpos := p.H_pos
omega
```

`H=0` と `H>0` は両立しないため、仮定 `¬ 0 < p.d` が排除される。

## Lean 固有の処理

本 theorem は 0294 `c_pos` とほぼ同じ Lean pattern を持つ。

1. `Nat.eq_zero_of_not_pos` で自然数の非正性を 0 へ落とす。
2. structure field の `natAbs` 等式を `simpa` で 0 に特殊化する。
3. `Int.natAbs_eq_zero.mp` で自然数値の絶対値情報から整数等式へ戻す。
4. `omega` で strict positivity との矛盾を閉じる。

`exact_mod_cast` は不要である。`H_natAbs_eq` は初めから `ℕ` 上の等式であり、矛盾に用いる `H_pos` は同じ整数式そのものについての不等式だからである。

また本 theorem 自体では `ring`, `nlinarith`, `positivity`, `norm_num` を使わない。

## 冗長・重複箇所

### 0294 `c_pos` との対称的重複

0294 は

```text
c=0 → |s|=0 → s=0 → s<0 と矛盾
```

本 theorem は

```text
d=0 → |H|=0 → H=0 → H>0 と矛盾
```

という完全に平行な構造を持つ。

共通補題として抽象化することは可能だが、対象となる量と最終的な非零性の出所が異なる。0294 は `s_neg`、0295 は `H_pos` に依存するため、現行の個別 theorem は proof graph 上の意味を明示する利点がある。

### `hH0` の明示

`Int.natAbs_eq_zero.mp hHAbsZero` をそのまま contradiction に使う短縮形も考えられる。しかし `hH0 : H = 0` を名前付きで残す現在のコードは、数学的な矛盾点を読みやすくしている。

## 最適化候補

1. `p.d ≠ 0` を先に証明し、自然数の非零性から正性へ移す形にもできる。ただし現行の `by_contra` + `Nat.eq_zero_of_not_pos` は十分短い。
2. 0294 と 0295 の共通形を、`x.natAbs = n^k` と `x ≠ 0` から `0<n` を得る一般補題として抽出できる可能性はある。ただし二本だけなら抽象化の方が重い。
3. 最後の `omega` は `H=0` と `H>0` の単純矛盾だけなので、より小さい order lemma で置換可能と思われる。Lean build/API 探索を行っていないため、最短形は断定しない。

現行証明は 0294 との対称性が明快で、教材性も高い。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。manifest 上、本宣言を含む generated source は

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

である。

本 theorem 自体が直接利用する主な機能は

- `Nat.eq_zero_of_not_pos`
- `Int.natAbs_eq_zero`
- `simpa`
- `omega`
- `GoldenZeroSectorCandidate.H_pos`

である。

`ring`, `nlinarith`, `positivity`, `norm_num`, `exact_mod_cast` は本 theorem 自体では不要である。

指定に従い Lean build は実行していないため、`import Mathlib` をどの個別 import へ縮小できるかは **未検証** である。特に `omega` と、前段の zero-sector 定義・定理群を含めた module 全体の最小 import 集合は断定しない。

## Comparator challenge 化の可否

**適している。**

難度は低めだが、次の能力を比較できる。

1. `H_natAbs_eq` という structure field を発見できるか。
2. 自然数 `d` の非正性を 0 へ変換できるか。
3. `natAbs = 0` から整数値 `H=0` に戻せるか。
4. 既存 theorem `H_pos` を適切な contradiction source として利用できるか。
5. 0294 との対称性を認識して証明パターンを再利用できるか。

例えば

```lean
theorem challenge (p : GoldenZeroSectorCandidate) : 0 < p.d := by
  ...
```

とし、`p.H_natAbs_eq` と `p.H_pos` の利用を許可する形式がよい。

## PDF との対応

対象 branch には既存の

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在する。

ただし今回、GitHub コネクタでは PDF binary 本文を解析可能なテキストとして取得できず、raw PDF の外部取得も成功しなかった。そのため PDF 内の具体的なページ番号、節番号、本 theorem と一致する記述位置は **確認できていない**。ここでは現行 Lean 正本 `Flt5DkMath/FLT5StandAlone.lean` を最優先の根拠とし、PDF の具体的内容について推測は行わない。

## 次に読むべき宣言

次は **0296 `GoldenZeroSectorCandidate.s_eq_neg_five_pow_mul_tenth`**。種別は `theorem` である。

```lean
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

0293 で確定した $s<0$ と、0290 が保持する $|s|=5^6c^{10}$ を合わせ、absolute value を外して

$$
s=-5^6c^{10}
$$

という exact signed equation を復元する段階へ進む。