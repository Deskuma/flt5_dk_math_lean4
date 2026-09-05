# 0311 — `GoldenZeroSectorCandidate.factor_sum`

## 宣言種別

これは **`theorem`** である。

0310 `GoldenZeroSectorCandidate.factor_difference` が inversion factors の差

$$
B-A=8d^5
$$

を固定したのに対し、本 theorem は二因子の正確な和

$$
A+B=2U
$$

を固定する。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- Exact sum of the two inversion factors. -/
theorem factor_sum (p : GoldenZeroSectorCandidate) :
    zeroSectorA p.r p.s p.d + zeroSectorB p.r p.s p.d =
      2 * zeroSectorU p.r p.s := by
  unfold zeroSectorA zeroSectorB
  ring
```

結論は整数 `ℤ` 上の等式である。

$$
A(r,s,d)+B(r,s,d)=2U(r,s).
$$

ここで

$$
A=U-W,
\qquad
B=U+W.
$$

## 数学的意味

定義を代入すれば

$$
A+B=(U-W)+(U+W).
$$

`W` が相殺されるので

$$
A+B=2U.
$$

従って本 theorem は新しい数論的制約を導くものではなく、`A` と `B` が `U` を中心として対称に配置されていることを exact equality として取り出す定義恒等式である。

0310 の

$$
B-A=2W=8d^5
$$

と合わせると、`U` は二因子の中点、`W` は半差として働くことが明示される。

$$
U=\frac{A+B}{2},
\qquad
W=\frac{B-A}{2}.
$$

Lean の本 theorem 自体は除算を使わず、整数上で安全な形 `A+B=2U` を採用している。

## 証明全体での役割

zero-sector inversion では、0309 により multiplicative constraint

$$
AB=4Q^5
$$

が得られ、0310 により additive difference constraint

$$
B-A=8d^5
$$

が得られた。本 0311 はさらに additive sum constraint

$$
A+B=2U
$$

を与える。

これにより inversion factors `A`,`B` は、積だけでなく差と和でも元の diagonal coordinate `U` と fifth-power coordinate `W` に結び付けられる。

後続の正値性証明では直ちに本 theorem を参照してはいないが、`A`,`B` の対称構造を API として明文化する役割を持つ。特に `A=U-W`, `B=U+W` という定義を毎回展開せずに、二因子から `U` を回収できる形を提供する。

この意味で本 theorem は inversion construction の「再構成 API」であり、0306 `square_reconstruction` が `U` から元の平方座標を回収したのと同様に、ここでは `A`,`B` から `U` を回収する情報を保持している。

## 直接依存する定義・補題

### `zeroSectorA`

lower inversion factor を

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d
```

すなわち

$$
A=U-W
$$

として定義する。

### `zeroSectorB`

upper inversion factor を

```lean
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

すなわち

$$
B=U+W
$$

として定義する。

### `zeroSectorU`

本 theorem の右辺に残る diagonal coordinate である。具体的には先行定義により `r`,`s` から構成される整数値であり、本 proof ではその内部式を展開する必要はない。

### `ring`

`zeroSectorA` と `zeroSectorB` の展開後に残る可換環恒等式

$$
(U-W)+(U+W)=2U
$$

を正規化して閉じる。

## 証明または構築の流れ

1. `unfold zeroSectorA zeroSectorB` により `A`,`B` の定義だけを展開する。
2. 左辺を

$$
(U-W)+(U+W)
$$

という整数式にする。
3. `ring` が `W` の相殺と係数整理を行う。
4. 右辺

$$
2U
$$

と一致して証明が終了する。

`zeroSectorW` や `zeroSectorU` の内部定義は展開しない。従って本 theorem は `U`,`W` の具体的な多項式形状に依存せず、`A=U-W`, `B=U+W` という対称な定義だけから成立している。

## Lean 固有の処理

結論は `ℤ` 上であり、減算を含む `zeroSectorA` を自然に扱える。`p.d : ℕ` は `zeroSectorW` の内部で `ℤ` に cast されるが、本 proof では `zeroSectorW` 自体を展開しないため cast 操作は表面に現れない。

そのため `push_cast`、`exact_mod_cast`、`norm_cast` は不要である。また不等式も存在しないため `omega`、`linarith`、`nlinarith`、`positivity` も不要である。

`ring` に渡される目標は純粋な commutative-ring identity であり、本 theorem では `simp` より `ring` の方が意図を明確に表している。

なお `GoldenZeroSectorCandidate` の hypothesis fields は一切使用していない。`p` は `r`,`s`,`d` を取得するための container としてのみ使われている。この点は 0310 `factor_difference` と同じである。

## 冗長・重複箇所

proof は

```lean
unfold zeroSectorA zeroSectorB
ring
```

の二行だけであり、局所的な冗長性はほぼない。

0310 と 0311 はそれぞれ一般恒等式

$$
(U+W)-(U-W)=2W,
$$

$$
(U-W)+(U+W)=2U
$$

を specialized API として保持している。両者には構造的な重複があるが、数学的役割は「差」と「和」で明確に異なるため、別 theorem として置く意義はある。

## 最適化候補

候補仮定を全く使わないため、より一般的な namespace に candidate 非依存 lemma として

```lean
zeroSectorA r s d + zeroSectorB r s d = 2 * zeroSectorU r s
```

を切り出し、本 theorem をその wrapper にする設計が可能である。

さらに `factor_difference` と対になる一般 API をまとめれば、`zeroSectorA/B` の基本演算則として再利用しやすくなる。

ただし現行 proof は既に極小であり、追加 abstraction が実際に有益かは再利用頻度次第である。Lean build を行わない条件のため、より短い `simp [zeroSectorA, zeroSectorB]` 等で閉じるか、最小 import がどこまで削れるかは実証していない。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用している。

本 theorem が直接必要とする機能は少なくとも次である。

- `ℤ` 上の加減算・乗算
- `zeroSectorA`
- `zeroSectorB`
- `zeroSectorU`
- `unfold`
- `ring`

本 proof は `omega`、`linarith`、`nlinarith`、`positivity`、`push_cast`、`exact_mod_cast` を直接使用しない。

従って `Mathlib` 全体ではなく、整数の基本代数と ring tactic を提供する import 群まで縮小できる可能性が高い。ただし正確な最小 import 集合は Lean build 禁止条件のため未検証であり、ここでは推測として扱う。

## Comparator challenge 化の可否

**可能。難度は初級。**

定義展開後は極めて小さな環恒等式なので、証明探索の難しさよりも「不要な仮定・不要な展開を避ける proof engineering」を比較する題材に向く。

比較候補は次のようになる。

- `unfold zeroSectorA zeroSectorB; ring` の現行 proof。
- `simp [zeroSectorA, zeroSectorB]` 系の簡約で閉じる proof。
- candidate 非依存の一般 lemma を先に作り、wrapper theorem とする proof。
- 0310 `factor_difference` と対称な API 設計を認識できるか。

特に `zeroSectorU` と `zeroSectorW` の内部定義まで展開する必要がないことを見抜けるかが良い評価点になる。

## PDF との照合

対象 branch には既存の日英 PDF

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを repository 上で確認した。

ただし GitHub コネクタの通常の text fetch は binary PDF 本文を返さないため、本実行では PDF 内の具体的ページ・節・式番号との直接照合はできていない。その位置については推測しない。

本解説の Lean code、宣言順、直接依存、後続宣言との関係は `Flt5DkMath/FLT5StandAlone.lean` を正本として確認した。

## 次に読むべき宣言

次の宣言は 0312 `GoldenZeroSectorCandidate.W_pos`、種別は **`theorem`** である。

Lean 正本では

```lean
/-- The tenth-power square root contribution is strictly positive. -/
theorem W_pos (p : GoldenZeroSectorCandidate) : 0 < zeroSectorW p.d := by
  unfold zeroSectorW
  have hd : (0 : ℤ) < p.d := by exact_mod_cast p.d_pos
  positivity
```

と続く。

0311 までで `A`,`B` の積・差・和という exact algebraic identities が揃い、0312 からは `W>0`、`B>0`、`A>0`、`A<B` という order/positivity phase に移る。