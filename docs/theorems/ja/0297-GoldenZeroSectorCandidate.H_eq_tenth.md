# 0297 — `GoldenZeroSectorCandidate.H_eq_tenth`

## 宣言種別

これは **`theorem`** である。

zero-sector candidate が保持する quartic factor の absolute-value tenth-power split に、0292 `GoldenZeroSectorCandidate.H_pos` で確定した正符号を戻し、符号なしの exact equation を復元する。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- Exact sign removal for the positive quartic factor. -/
theorem H_eq_tenth (p : GoldenZeroSectorCandidate) :
    goldenFifthSndFactor p.r p.s = (p.d : ℤ) ^ 10 := by
  have habs : ((goldenFifthSndFactor p.r p.s).natAbs : ℤ) =
      (p.d : ℤ) ^ 10 := by
    exact_mod_cast p.H_natAbs_eq
  rw [Int.ofNat_natAbs_of_nonneg p.H_pos.le] at habs
  exact habs
```

結論は

$$
goldenFifthSndFactor(p.r,p.s)=p.d^{10}
$$

である。

## 数学的意味

0290 `GoldenZeroSectorCandidate` は quartic factor

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4
$$

について

$$
|H(p.r,p.s)|=p.d^{10}
$$

に対応する field

```lean
p.H_natAbs_eq :
  (goldenFifthSndFactor p.r p.s).natAbs = p.d ^ 10
```

を保持している。一方、0292 `p.H_pos` により

$$
0<H(p.r,p.s)
$$

が既に確定している。

したがって $H\ge0$ なので

$$
|H|=H,
$$

ゆえに

$$
H(p.r,p.s)=p.d^{10}
$$

となる。

0296 `s_eq_neg_five_pow_mul_tenth` が負の visible coordinate `s` に対して $|s|=-s$ を使ったのに対し、本 theorem は正の quartic factor に対して $|H|=H$ を使う、完全に対になる sign-removal step である。

## 証明全体での役割

zero-sector arithmetic receiver から inversion 層へ入る時点では、tenth-power split は

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}
$$

という absolute-value 形式で保存されている。

0296 と本 0297 によってこれを

$$
s=-5^6c^{10},
\qquad
H(r,s)=d^{10}
$$

という exact signed data へ変換する。

この二式は後続で重要である。直後の 0298 `natAbs_product_eq` と 0299 `a_eq_c_mul_d` は、元の product equation と二つの tenth-power split を接続して元の base `a` を `c*d` に分解する。また `H_eq_tenth` 自体はさらに後ろの `five_not_dvd_d`、`d_odd`、`discriminant_eq`、そして descent packet の `H_eq` 構築でも直接再利用される。

従って本 theorem は「絶対値で受け取った quartic tenth power」を inversion / descent が使える exact positive fifth/tenth-power algebra へ戻す境界である。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate.H_natAbs_eq`

0290 の structure field。

```lean
p.H_natAbs_eq :
  (goldenFifthSndFactor p.r p.s).natAbs = p.d ^ 10
```

magnitude 情報の直接 source である。

### `GoldenZeroSectorCandidate.H_pos`

0292 の theorem。

```lean
theorem H_pos (p : GoldenZeroSectorCandidate) :
    0 < goldenFifthSndFactor p.r p.s
```

本 theorem では `.le` により

```lean
p.H_pos.le : 0 ≤ goldenFifthSndFactor p.r p.s
```

へ弱めて absolute-value removal に使う。

### `Int.ofNat_natAbs_of_nonneg`

整数 `z` が非負なら

```lean
(z.natAbs : ℤ) = z
```

を与える Mathlib 補題。本 theorem では $z=H(p.r,p.s)$ として使われる。

### `exact_mod_cast`

`p.H_natAbs_eq` は `ℕ` 上の等式だが、最終結論は `ℤ` 上である。そこで

```lean
((goldenFifthSndFactor p.r p.s).natAbs : ℤ) =
  (p.d : ℤ) ^ 10
```

へ cast する。

## 証明または構築の流れ

1. `p.H_natAbs_eq` を `exact_mod_cast` で `ℤ` 上へ持ち上げ、`habs` を作る。
2. `p.H_pos.le` から quartic factor の非負性を得る。
3. `Int.ofNat_natAbs_of_nonneg` で `((H).natAbs : ℤ)` を `H` へ rewrite する。
4. rewrite 後の `habs` がそのまま目標なので `exact habs` で終了する。

0296 と異なり最後に `linarith` は不要である。非負側では `natAbs` の cast が quartic factor そのものに直接 rewrite されるためである。

## Lean 固有の処理

数学では $H>0$ と $|H|=d^{10}$ から直ちに $H=d^{10}$ と書けるが、Lean では `Int.natAbs` の値域が `ℕ` なので、まず自然数等式を整数等式へ移す必要がある。

この型境界を `exact_mod_cast` が処理し、その後 `Int.ofNat_natAbs_of_nonneg p.H_pos.le` が absolute value を外す。

また `H_pos` は strict positivity を与えるが、absolute-value lemma が要求するのは nonnegativity なので `.le` で弱めている。この「強い既存事実を必要最小限の形へ射影する」処理も Lean では明示されている。

## 冗長・重複箇所

0296 `s_eq_neg_five_pow_mul_tenth` と構造的に対称である。

- 0296: `s < 0` から `Int.ofNat_natAbs_of_nonpos`
- 0297: `H > 0` から `Int.ofNat_natAbs_of_nonneg`

ただし本 theorem は rewrite 後に `exact habs` だけで閉じるため、0296 より一段単純である。

`habs` を名前付きで保持せず、`exact_mod_cast` と rewrite をより圧縮して書ける可能性はある。しかし現在形は「型変換」と「符号除去」が別段階として読み取れ、theorem museum の教材用途ではむしろ明瞭である。

## 最適化候補

1. `have habs` を使わず `exact_mod_cast` した等式を `simpa` で直接閉じる短縮形が存在する可能性がある。
2. `rw [Int.ofNat_natAbs_of_nonneg p.H_pos.le] at habs` を `simpa [Int.ofNat_natAbs_of_nonneg p.H_pos.le] using ...` のような一段の proof にまとめられる可能性がある。
3. 0296–0297 を「`natAbs` の power equality + sign information から signed equality」を得る共通補題へ抽象化する設計も可能だが、負側と正側で使用 API が異なり、現状の二定理は十分短い。抽象化による利益は限定的と思われる。

これらの短縮形は Lean build を行っていないため **未検証** である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。manifest / generated-source 境界では本宣言は

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

に属する。

本 theorem 自体が直接使う主要機能は

- `exact_mod_cast`
- `Int.ofNat_natAbs_of_nonneg`
- order projection `.le`
- rewrite `rw`
- 既存 theorem `GoldenZeroSectorCandidate.H_pos`

である。

`linarith`, `nlinarith`, `ring`, `positivity`, `omega`, `norm_num` は本 theorem 自体では使わない。

指定に従い Lean build は実行していないため、`import Mathlib` を個別 import へどこまで縮小できるかは **未検証** である。特に本 theorem 単体の最小 import と、前段 candidate API を含む実モジュール全体の最小 import は区別する必要がある。

## Comparator challenge 化の可否

**適している。** 難度は低～中程度である。

challenge としては

```lean
theorem challenge (p : GoldenZeroSectorCandidate) :
    goldenFifthSndFactor p.r p.s = (p.d : ℤ) ^ 10 := by
  ...
```

だけを提示し、`p.H_natAbs_eq` と `p.H_pos` を探索・利用させる形が自然である。

評価点は、

- `H_natAbs_eq` が `ℕ` 上の等式であることを認識できるか
- `exact_mod_cast` により `ℤ` へ移せるか
- strict positivity を `.le` で nonnegativity に変換できるか
- `Int.ofNat_natAbs_of_nonneg` を発見できるか

である。

複雑な代数計算ではなく、Lean の整数 absolute-value API と cast discipline を比較する challenge に向いている。

## PDF との対応

対象 branch の repository tree には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

ただし今回利用できた GitHub コネクタの通常テキスト取得経路では PDF binary 本文を解析可能なテキストとして取得できなかった。そのため PDF 内の具体的ページ番号・節番号・本 theorem に対応する記述位置は **確認できていない**。ここでは現行 Lean 正本 `Flt5DkMath/FLT5StandAlone.lean` を最優先の根拠とし、PDF の具体的内容について推測は行わない。

## 次に読むべき宣言

次は **0298 `GoldenZeroSectorCandidate.natAbs_product_eq`**。種別は `theorem` である。

```lean
/-- Natural absolute-value form of the signed product equation. -/
theorem natAbs_product_eq (p : GoldenZeroSectorCandidate) :
    p.s.natAbs * (goldenFifthSndFactor p.r p.s).natAbs =
      5 ^ 6 * p.a ^ 10 := by
  have h := congrArg Int.natAbs p.product_eq
  simpa [Int.natAbs_mul, pow_succ] using h
```

0296–0297 が individual factor の sign removal を完了したのに対し、0298 は元の signed product equation 全体へ `Int.natAbs` を適用して自然数の multiplicative identity を取り出す。これは次の `a_eq_c_mul_d` で

$$
a=c d
$$

を復元する直接の入力となる。
