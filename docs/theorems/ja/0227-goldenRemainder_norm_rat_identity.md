# 0227 — `goldenRemainder_norm_rat_identity`

## Lean の型

```lean
private theorem goldenRemainder_norm_rat_identity
    (x y : GoldenInt) (hy : y ≠ 0) :
    (goldenNorm (goldenRemainder x y) : ℚ) =
      (goldenNorm y : ℚ) *
        goldenRatNorm
          ((goldenQuotientCoords x y).1 - (goldenQuotient x y).fst,
           (goldenQuotientCoords x y).2 - (goldenQuotient x y).snd) := by
  have hn : (goldenNorm y : ℚ) ≠ 0 := by
    exact_mod_cast goldenNorm_ne_zero_of_ne_zero hy
  have hn' : (y.fst : ℚ) ^ 2 + y.fst * y.snd - y.snd ^ 2 ≠ 0 := by
    simpa [goldenNorm] using hn
  let A : ℚ := (goldenQuotientCoords x y).1
  let B : ℚ := (goldenQuotientCoords x y).2
  let m : ℤ := (goldenQuotient x y).fst
  let n : ℤ := (goldenQuotient x y).snd
  have hx1 : (x.fst : ℚ) = y.fst * A + y.snd * B := by
    dsimp [A, B, goldenQuotientCoords]
    rw [goldenQuotientNumerator_fst, goldenQuotientNumerator_snd]
    field_simp [hn']
    simp [goldenNorm]
    ring
  have hx2 : (x.snd : ℚ) =
      y.snd * A + y.fst * B + y.snd * B := by
    dsimp [A, B, goldenQuotientCoords]
    rw [goldenQuotientNumerator_fst, goldenQuotientNumerator_snd]
    field_simp [hn']
    simp [goldenNorm]
    ring
  have hr1 : ((goldenRemainder x y).fst : ℚ) =
      y.fst * (A - m) + y.snd * (B - n) := by
    simp only [goldenRemainder, goldenMul, golden_fst_sub, Int.cast_sub, Int.cast_add, Int.cast_mul,
      m, n]
    rw [hx1]
    ring
  have hr2 : ((goldenRemainder x y).snd : ℚ) =
      y.snd * (A - m) + y.fst * (B - n) + y.snd * (B - n) := by
    simp only [goldenRemainder, goldenMul, golden_snd_sub, Int.cast_sub, Int.cast_add, Int.cast_mul,
      m, n]
    rw [hx2]
    ring
  dsimp only [goldenNorm, goldenRatNorm]
  push_cast
  change _ = _ *
    ((A - (m : ℚ)) ^ 2 + (A - (m : ℚ)) * (B - (n : ℚ)) -
      (B - (n : ℚ)) ^ 2)
  rw [hr1, hr2]
  ring
```

これは `private theorem` である。外部 API として公開する theorem ではなく、`GoldenEuclidean.lean` 内部で remainder の strict norm decrease を証明するための局所的な橋として使われる。

## 数学的主張

`x / y` の有理座標を

$$
(A,B)=\mathrm{goldenQuotientCoords}(x,y)
$$

とし、その各座標を最近接整数へ丸めて

$$
m=\operatorname{round}(A),\qquad n=\operatorname{round}(B)
$$

とする。0220 `goldenQuotient` はこの $(m,n)$ を黄金整数 quotient として選び、0221 `goldenRemainder` は

$$
r=x-qy
$$

を定義する。

本 theorem は remainder の黄金ノルムを

$$
N(r)=N(y)\,Q(A-m,B-n)
$$

と正確に分解する。ここで

$$
Q(u,v)=u^2+uv-v^2
$$

は 0210 `goldenRatNorm` の有理黄金ノルム二次形式である。

つまり remainder の大きさは、divisor の norm と quotient rounding error の二次形式の積に完全に分離される。

この恒等式があることで、0214 の fundamental-cell estimate

$$
|Q(u,v)|<1
$$

をそのまま掛け合わせて

$$
|N(r)|<|N(y)|
$$

を導ける。したがって本 theorem は、最近接整数丸めと Euclidean norm decrease を結ぶ中心的な代数恒等式である。

## 証明全体での役割

0220–0227 は、黄金整数環上で Euclidean division を作るための quotient/remainder 構築 block である。

- 0220 `goldenQuotient` — 有理 quotient coordinates を最近接整数へ丸める。
- 0221 `goldenRemainder` — $r=x-qy$ を定義する。
- 0222 `goldenQuotient_zero` — divisor が `0` の場合の total quotient 仕様を確定する。
- 0223 `golden_quotient_mul_add_remainder` — $yq+r=x$ を確定する。
- 0224–0226 — Euclidean size $|N(x)|$ の定義、正性、乗法性を確立する。
- 0227 本 theorem — remainder norm を divisor norm と rounding-error norm の積へ分解する。

直後の `golden_remainder_size_lt` は、本 theorem を

```lean
have hid := goldenRemainder_norm_rat_identity x y hy
```

として直接利用する。その proof では、`A-round A` と `B-round B` がそれぞれ絶対値 `1/2` 以下であることから 0214 を適用し、

$$
|Q(A-m,B-n)|<1
$$

を得る。その後本 theorem と `abs_mul` を使って strict contraction を導く。

したがって 0227 は、`GoldenEuclidean.lean` の中でも最も重要な内部恒等式の一つであり、単なる補助計算ではなく Euclidean-domain 構築の魔核に近い位置を占める。

## 直接依存する定義・補題

主な直接依存は次の通りである。

- 0215 `goldenNorm_ne_zero_of_ne_zero`
- 0217 `goldenQuotientNumerator_fst`
- 0218 `goldenQuotientNumerator_snd`
- 0219 `goldenQuotientCoords`
- 0220 `goldenQuotient`
- 0221 `goldenRemainder`
- 0210 `goldenRatNorm`
- `goldenNorm`
- `goldenMul`
- `golden_fst_sub`
- `golden_snd_sub`
- `field_simp`
- `exact_mod_cast`
- `push_cast`
- `ring`

概念的な依存は

$$
y\neq0
\Longrightarrow N(y)\neq0
\Longrightarrow
\frac{x\overline y}{N(y)}=(A,B)
\Longrightarrow
r=y\cdot(A-m,B-n)
\Longrightarrow
N(r)=N(y)Q(A-m,B-n)
$$

と整理できる。

## 証明の流れ

### 1. 分母 `N(y)` が非零であることを確保する

```lean
have hn : (goldenNorm y : ℚ) ≠ 0 := by
  exact_mod_cast goldenNorm_ne_zero_of_ne_zero hy
```

0215 で得た整数上の `goldenNorm y ≠ 0` を、`ℚ` へ cast して nonzero certificate にする。

続いて

```lean
have hn' : (y.fst : ℚ) ^ 2 + y.fst * y.snd - y.snd ^ 2 ≠ 0 := by
  simpa [goldenNorm] using hn
```

で `goldenNorm` を展開した分母形へ変換する。これは後続 `field_simp` が必要とする非零仮定である。

### 2. quotient coordinates と丸め整数に短名を与える

```lean
let A : ℚ := (goldenQuotientCoords x y).1
let B : ℚ := (goldenQuotientCoords x y).2
let m : ℤ := (goldenQuotient x y).fst
let n : ℤ := (goldenQuotient x y).snd
```

以後の algebra を読みやすくするため、連続的 quotient coordinates $(A,B)$ と離散 quotient coordinates $(m,n)$ を明示的に分離する。

### 3. `x` を `y*(A,B)` の座標式として復元する

第一座標について

```lean
have hx1 : (x.fst : ℚ) = y.fst * A + y.snd * B := by
  ...
```

第二座標について

```lean
have hx2 : (x.snd : ℚ) =
    y.snd * A + y.fst * B + y.snd * B := by
  ...
```

を証明する。

ここでは 0217・0218 による有理化分子の座標式を展開し、`field_simp [hn']` で共通分母 `N(y)` を消し、最後を `ring` で閉じる。

これは実質的に

$$
x=y(A+B\varphi)
$$

という rational quotient identity の座標版である。

### 4. remainder の座標を rounding error で表す

0221 の `r=x-qy` を展開し、`hx1` / `hx2` を代入して、

$$
r_1=y_1(A-m)+y_2(B-n)
$$

および

$$
r_2=y_2(A-m)+y_1(B-n)+y_2(B-n)
$$

を得る。

Lean 上ではそれぞれ `hr1`, `hr2` として証明される。

### 5. 両辺のノルムを展開して ring identity として閉じる

最後に `goldenNorm` と `goldenRatNorm` を展開し、整数 cast を押し込み、目標を

$$
N(r)=N(y)\left((A-m)^2+(A-m)(B-n)-(B-n)^2\right)
$$

へ変形する。

`hr1`, `hr2` を rewrite した後は純粋な可換環多項式恒等式なので、`ring` が証明を閉じる。

## Lean 固有の処理

この proof は Lean 固有の coercion 管理がかなり濃い。

`GoldenInt` の座標は `ℤ`、quotient coordinates は `ℚ` なので、同じ式の中で整数 cast が頻繁に現れる。`exact_mod_cast`, `push_cast`, `Int.cast_sub`, `Int.cast_add`, `Int.cast_mul` は、この二つの層を安全に往復するために使われている。

また `field_simp [hn']` は分母 `N(y)` を除去するが、そのために 0215 由来の `hn'` が不可欠である。つまり 0215 の nonzero theorem は単に抽象的な整域性を述べるだけでなく、ここで実際の rational denominator certificate として働いている。

`let A`, `let B`, `let m`, `let n` を導入するのも proof engineering 上重要である。これがなければ `goldenQuotientCoords` と `goldenQuotient` の長い項が何度も展開され、`ring` 前の式が非常に読みにくくなる。

## 冗長・重複箇所

`hx1` と `hx2`、`hr1` と `hr2` は完全に二座標並列の証明になっているため、構造的な重複がある。

特に quotient reconstruction

$$
x=y(A+B\varphi)
$$

を `GoldenRat` または適切な scalar extension 上の一つの equality として bundle できれば、`hx1` / `hx2` の二本を別々に持つ必要は減る可能性がある。

同様に remainder についても

$$
r=y\cdot((A-m)+(B-n)\varphi)
$$

を先に一つの構造 theorem として公開し、その norm multiplicativityから本 theorem を導く方が数学的には自然である。

ただし現行実装は、`GoldenInt` と `GoldenRat` の間に一般的な scalar extension structure を導入せず、座標だけで証明を閉じる方針である。そのため多少の重複と引き換えに依存構造を浅く保っている。

## 最適化候補

1. **rationalized multiplication を専用 structure で bundle する**
   - `GoldenRat` 上に黄金乗法を定義し、`x = y * quotientCoords` を一つの equality で扱う。

2. **quotient reconstruction theorem を先に切り出す**
   - `hx1` / `hx2` を named theorem にまとめ、0227 の proof を remainder error の処理に集中させる。

3. **remainder factorization theorem を作る**
   - `r = y * error` 相当を rational coordinate level で証明し、norm multiplicativityから 0227 を導く。

4. **現行の座標 proof を維持する**
   - 新しい scalar-extension infrastructure を増やさず、`field_simp + ring` で監査可能な explicit proof を保つ。

5. **`GoldenRat` を `ℚ[φ]` 的な構造に昇格する Comparator を作る**
   - 現行 pair-based implementation と algebraic extension implementation で proof size と透明性を比較する。

現状では 0227 は長いが、依存がすべて明示的で、Lean が最終的にただの多項式恒等式を検証していることが見えやすい。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem が直接要求する Mathlib 表面は比較的広く、少なくとも次の機能が関係する。

- `exact_mod_cast`
- `field_simp`
- `push_cast`
- `ring`
- `Rat` / `Int` coercion
- 基本的な `let` / definitional reduction

`GoldenEuclidean.lean` 全体ではさらに `round`, `abs_sub_round`, `nlinarith`, well-founded measure, `EuclideanDomain` なども使うため、import 最適化は theorem 単独ではなく module 全体で測るべきである。

Lean build は行っていないため、正確な最小 import 集合は未検証であり、候補としてのみ記録する。

## Comparator challenge 化の可否

非常に適している。比較候補は次の通り。

- A: 現行の explicit coordinate proof
- B: `GoldenRat` に乗法を定義し `r=y*error` を構造的に証明する proof
- C: quadratic algebra / `AdjoinRoot` 側へ持ち上げ norm multiplicativityで処理する proof
- D: quotient/remainder identity と norm factorization を一つの bundled theorem にまとめる設計

比較軸は、proof 行数、cast 操作数、`field_simp` 依存、数学的構造の可視性、一般化可能性、下流 `golden_remainder_size_lt` の簡潔さである。

A は長いが明示的で、B/C は短くなる可能性がある一方 abstraction layer が増える。この trade-off は `GoldenEuclidean` block 全体の設計評価に向いている。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

正本 source 上で、0226 `goldenEuclideanSize_mul` の直後に本 `private theorem` があり、その直後に公開 theorem `golden_remainder_size_lt` が続くことを確認した。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem は `private` な内部証明であり、対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0228 `golden_remainder_size_lt`** である。

```lean
theorem golden_remainder_size_lt (x : GoldenInt) {y : GoldenInt} (hy : y ≠ 0) :
    goldenEuclideanSize (goldenRemainder x y) < goldenEuclideanSize y := by
  ...
```

0227 が

$$
N(r)=N(y)Q(\text{rounding error})
$$

を与えたので、0228 は `round` の誤差 bound と 0214 の $|Q|<1$ を適用して、ついに

$$
|N(r)|<|N(y)|
$$

を自然数 Euclidean size の strict inequality として確定する。

ここが Euclidean algorithm の decrease condition そのものとなる。