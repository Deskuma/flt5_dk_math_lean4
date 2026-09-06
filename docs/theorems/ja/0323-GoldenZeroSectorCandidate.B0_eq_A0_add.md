# 0323 — `GoldenZeroSectorCandidate.B0_eq_A0_add`

## 宣言種別

これは **`theorem`** である。

0316–0322 で `zeroSectorA`, `zeroSectorB` の正の自然数代表 `A0`, `B0` を構築し、積恒等式まで `ℕ` に移した後、整数上の factor difference を自然数上の **減算を使わない加法形** へ移す theorem である。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- Additive natural form of the factor difference, avoiding subtraction. -/
theorem B0_eq_A0_add (p : GoldenZeroSectorCandidate) :
    p.B0 = p.A0 + 8 * p.d ^ 5 := by
  have hdiff := p.factor_difference
  have hcasts : (p.B0 : ℤ) =
      (p.A0 : ℤ) + 8 * (p.d : ℤ) ^ 5 := by
    rw [p.A0_cast, p.B0_cast]
    linarith
  exact_mod_cast hcasts
```

型は

```lean
p.B0 = p.A0 + 8 * p.d ^ 5
```

であり、両辺は `ℕ` である。

## 数学的主張

signed integer factors を

$$
A=\operatorname{zeroSectorA}(r,s,d),\qquad
B=\operatorname{zeroSectorB}(r,s,d)
$$

と書く。上流の `factor_difference` では

$$
B-A=8d^5
$$

が `ℤ` 上で証明されている。

0318 `A0_cast` と 0319 `B0_cast` により

$$
(A_0:\mathbb Z)=A,
$$

$$
(B_0:\mathbb Z)=B
$$

が既に得られているため、整数上では

$$
(B_0:\mathbb Z)-(A_0:\mathbb Z)=8(d:\mathbb Z)^5
$$

である。これを減算を避けて整理すれば

$$
(B_0:\mathbb Z)=(A_0:\mathbb Z)+8(d:\mathbb Z)^5.
$$

最後に cast を `ℕ` へ戻して

$$
B_0=A_0+8d^5
$$

を得る。

重要なのは、自然数では一般の減算が切り詰め subtraction になるため、後続の可除性・偶奇・因数分解では `B0 - A0 = ...` よりも

$$
B_0=A_0+8d^5
$$

の方が安全で強い API になることである。

## 証明全体での役割

0322 `A0_mul_B0` が signed product

$$
AB=4Q^5
$$

を

$$
A_0B_0=4Q^5
$$

へ移したのに対し、本 0323 は signed difference

$$
B-A=8d^5
$$

を自然数上の additive identity

$$
B_0=A_0+8d^5
$$

へ移す。

これで zero-sector inversion candidate から後続で必要な自然数 factor data が揃う。直後の `GoldenZeroSectorInversionPacket` では、本 theorem がそのまま

```lean
factor_difference :
  source.B0 = source.A0 + 8 * source.d ^ 5
```

として保存され、後続の factorization module から直接参照される。

実際、下流ではこの恒等式を使って、`A0`, `B0` の共通素因子が `d` に入ることを導いたり、2 や 4 の可除性を両因子間で輸送したり、さらに odd/even branch の fifth-power difference を構築している。

したがって本 theorem は単なる表示変換ではなく、後続の自然数 divisibility reasoning の標準形を決める API 境界である。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate.factor_difference`

本 proof の起点である。

```lean
have hdiff := p.factor_difference
```

正本では

```lean
theorem factor_difference (p : GoldenZeroSectorCandidate) :
    zeroSectorB p.r p.s p.d - zeroSectorA p.r p.s p.d =
      8 * (p.d : ℤ) ^ 5 := by
  unfold zeroSectorA zeroSectorB zeroSectorW
  ring
```

であり、数学的には

$$
B-A=8d^5
$$

を与える。

### `GoldenZeroSectorCandidate.A0_cast`

0318 の theorem で、

```lean
(p.A0 : ℤ) = zeroSectorA p.r p.s p.d
```

すなわち

$$
(A_0:\mathbb Z)=A
$$

を与える。

### `GoldenZeroSectorCandidate.B0_cast`

0319 の theorem で、

```lean
(p.B0 : ℤ) = zeroSectorB p.r p.s p.d
```

すなわち

$$
(B_0:\mathbb Z)=B
$$

を与える。

### `linarith`

`factor_difference` の subtraction equality を、cast 後の additive equality へ変形する。

### `exact_mod_cast`

最終的な整数 equality

```lean
(p.B0 : ℤ) = (p.A0 : ℤ) + 8 * (p.d : ℤ) ^ 5
```

を自然数 equality へ戻す。

## 証明の流れ

1. `p.factor_difference` を `hdiff` として取得する。
2. 自然数代表を cast した整数 equality `hcasts` を目標として立てる。
3. `rw [p.A0_cast, p.B0_cast]` により `A0`, `B0` の cast を signed factors `A`, `B` に置き換える。
4. この時点で `hcasts` のゴールは、本質的に

   ```lean
   zeroSectorB ... = zeroSectorA ... + 8 * (p.d : ℤ) ^ 5
   ```

   となる。
5. `hdiff` は

   ```lean
   zeroSectorB ... - zeroSectorA ... = 8 * (p.d : ℤ) ^ 5
   ```

   なので、`linarith` が subtraction form から addition form へ線形変形する。
6. 得られた `hcasts` を `exact_mod_cast` で `ℕ` equality へ輸送し、証明を閉じる。

## Lean 固有の処理

### subtraction を一度 `ℤ` に留める設計

Lean の `Nat.sub` は切り詰め subtraction なので、整数上の

```lean
B - A = 8 * d ^ 5
```

をそのまま `ℕ` へ cast するより、先に `ℤ` 上で

```lean
B = A + 8 * d ^ 5
```

へ変形してから自然数へ戻す方が安全である。

本 theorem の docstring の `avoiding subtraction` は、この型理論上の事情を正確に表している。

### `rw` の向き

0322 では signed factors を natural representatives の cast へ戻すため `← p.A0_cast`, `← p.B0_cast` を使った。本 theorem では逆に `hcasts` 側に `(A0 : ℤ)`, `(B0 : ℤ)` があるため、

```lean
rw [p.A0_cast, p.B0_cast]
```

と正方向に rewrite する。

この対比は 0322 と 0323 を連続して読むと分かりやすい。

### `linarith`

ここでの `linarith` は fifth power 自体を展開・解析していない。`(p.d : ℤ)^5` を一つの項として扱い、

$$
B-A=C
$$

から

$$
B=A+C
$$

へ線形整理している。

### `exact_mod_cast`

最後の cast 除去も数学的推論ではなく、すでに同一の自然数式から来ている integer equality を型境界越しに戻す処理である。

## 冗長・重複箇所

proof は 7 行程度で役割が明確であり、大きな冗長性はない。

```lean
have hdiff := p.factor_difference
```

は一見すると `linarith [p.factor_difference]` のようにインライン化できそうだが、`hdiff` と名前を付けることで「上流の subtraction identity を使っている」ことが明確になる。

また 0322 `A0_mul_B0` と cast bridge の構造は似ているが、こちらには subtraction-to-addition の変形が必要であり、単純な重複ではない。

`A0_pos`, `B0_pos`, `A_lt_B` は proof term から直接参照されない。これは、それらの正性・順序情報が既に `A0_cast`, `B0_cast` と上流の signed identity を通じて必要な形に整理されているためである。

## 最適化候補

候補の一つは `hcasts` をより短く構築する形である。例えば概念的には

```lean
  have hcasts : (p.B0 : ℤ) =
      (p.A0 : ℤ) + 8 * (p.d : ℤ) ^ 5 := by
    rw [p.A0_cast, p.B0_cast]
    linarith [p.factor_difference]
  exact_mod_cast hcasts
```

として `hdiff` を省ける可能性がある。

また generic helper として

```lean
(x : ℤ) - y = z → x = y + z
```

型の変形補題を利用・用意すれば `linarith` 依存を減らせる可能性もある。数学的構造を明示するなら、この方向は Comparator 候補として価値がある。

ただし現行 proof は短く、`linarith` の用途も限定的で、読みやすさは高い。代替案は本作業では Lean build を行っていないため **未検証** である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem が直接利用する Mathlib 側の主な機能は

- `rw`
- `linarith`
- `exact_mod_cast`
- `Nat` / `Int` coercion
- multiplication と power に対する cast normalization

である。

project 側では

- `GoldenZeroSectorCandidate.factor_difference`
- `GoldenZeroSectorCandidate.A0_cast`
- `GoldenZeroSectorCandidate.B0_cast`

に依存する。

本 theorem 単体では `Mathlib` 全体より狭い import へ縮められる可能性が高いが、standalone 全体の依存閉包を含めた **正確な最小 import 集合は Lean build なしには確認していない**。したがって import 最適化は未検証候補である。

## Comparator challenge 化の可否

**可能。0322 よりも比較対象が豊富で、良質な小型 challenge になる。**

比較候補は

1. 現行の `rw` + `linarith` + `exact_mod_cast`
2. subtraction equality の標準 lemma を使い `linarith` を避ける proof
3. `omega` を用いて整数・自然数変換をまとめる proof
4. generic cast/additive-form helper を先に作って適用する proof

である。

評価軸は

- `Nat.sub` の切り詰め問題を安全に避けられているか
- `ℤ` / `ℕ` の境界が読み手に見えるか
- arithmetic automation が過剰でないか
- proof が上流 theorem の意味を保っているか
- 下流 API として `B0 = A0 + ...` の形を安定して提供できるか

とするのがよい。

特に「自然数 subtraction を避ける設計判断」は Lean の数論形式化で頻出するため、Comparator 教材として実用的である。

## PDF との照合

対象 branch には既存の日英 PDF

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを今回確認した。

ただし GitHub コネクタの通常の text fetch は binary PDF 本文を返さないため、本実行では PDF 内の具体的ページ・節・式番号との直接照合はできていない。したがって PDF 上の対応位置については **未確認であり、推測していない**。

本解説の技術的内容は、対象 branch の最新 `Flt5DkMath/FLT5StandAlone.lean` にある実際の宣言と、その前後の依存関係を正本としている。

## 次に読むべき宣言

次は **0324 `GoldenZeroSectorInversionPacket`** である。

種別は theorem ではなく **`structure`** である。

```lean
structure GoldenZeroSectorInversionPacket where
  source : GoldenZeroSectorCandidate
  H_pos : 0 < goldenFifthSndFactor source.r source.s
  s_neg : source.s < 0
  c_pos : 0 < source.c
  d_pos : 0 < source.d
  ...
  factor_product :
    source.A0 * source.B0 = 4 * zeroSectorQ source.c ^ 5
  factor_difference :
    source.B0 = source.A0 + 8 * source.d ^ 5
  ...
```

0323 までで candidate 上に散在していた正性・互いに素性・積・差・再構成の証明を、下流 factorization が利用する certified packet としてまとめる宣言である。