# 0392 `GoldenZeroSectorDescentPacket.fifthRoot_five_not_dvd_H`

## 宣言種別

`theorem`

`GoldenZeroSectorDescentPacket` namespace 内で、0387 以降に得られた第五根 `gamma : GoldenInt` に付随する quartic factor

```lean
goldenFifthSndFactor gamma.fst gamma.snd
```

が 5 で割れないことを回収する補題である。

## Lean コード

```lean
theorem fifthRoot_five_not_dvd_H
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hnorm : goldenNorm gamma = (p.D : ℤ)) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd := by
  intro hH
  have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq gamma
  have hnormSq : (5 : ℤ) ∣ goldenNorm gamma ^ 2 := by
    have h := dvd_sub hH hdiff
    ring_nf at h
    exact h
  have hnormFive : (5 : ℤ) ∣ goldenNorm gamma :=
    (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
  rw [hnorm] at hnormFive
  exact p.five_not_dvd_D (by exact_mod_cast hnormFive)
```

## Lean の型

概念的には次の型である。

```lean
GoldenZeroSectorDescentPacket.fifthRoot_five_not_dvd_H :
  (p : GoldenZeroSectorDescentPacket) →
  (gamma : GoldenInt) →
  goldenNorm gamma = (p.D : ℤ) →
  ¬ (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd
```

入力は descent packet `p`、黄金整数 `gamma`、および第五根の norm が packet の `D` に一致するという

```lean
hnorm : goldenNorm gamma = (p.D : ℤ)
```

である。出力は整数上の非可除性

$$
5 \nmid H(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}})
$$

である。

ここで

$$
H(a,b)
= a^4+2a^3b+4a^2b^2+3ab^3+b^4
$$

は `goldenFifthSndFactor a b` である。

## 数学的主張

`gamma=(a,b)` と書く。既存補題

```lean
five_dvd_goldenFifthSndFactor_sub_norm_sq gamma
```

は

$$
5 \mid H(a,b)-N(a,b)^2
$$

を与える。

いま反対に

$$
5\mid H(a,b)
$$

と仮定する。すると差を取ることで

$$
5\mid N(a,b)^2.
$$

5 は素数なので

$$
5\mid N(a,b).
$$

ところが `hnorm` により

$$
N(a,b)=D.
$$

従って

$$
5\mid D.
$$

これは 0382 `GoldenZeroSectorDescentPacket.five_not_dvd_D` の

$$
5\nmid D
$$

に矛盾する。

したがって

$$
5\nmid H(a,b)
$$

である。

## 証明全体での役割

0387 `exists_lift_eq_fifthPower` は元の quadratic lift を

$$
T(r,s)=\gamma^5,
\qquad
N(\gamma)=D
$$

という純粋な第五冪へ変換した。その後、0388–0391 で第五根 `gamma=(a,b)` について

$$
s^2=5bH(a,b),
$$

$$
H(a,b)>0,
$$

$$
b>0,
$$

$$
\gcd(|a|,|b|)=1
$$

を順に回収している。

0392 はさらに、元 packet が持っていた 5-adic invariant

$$
5\nmid H
$$

を第五根側でも再生する段階である。

この事実は単なる局所補題ではない。後続の strict descent では、第五根の第二座標と quartic factor の積構造を 5-adically 分離する必要がある。その際に `H(a,b)` 側へ 5 が逃げ込まないことが重要になる。

つまり 0392 は、第五根 `gamma` を次世代の descent datum として再利用するための **5-adic invariant の閉包性** を示す theorem である。

## 直接依存する定義・補題

主要な直接依存は次の通りである。

- `GoldenZeroSectorDescentPacket`
- `GoldenInt`
- `goldenNorm`
- `goldenFifthSndFactor`
- `five_dvd_goldenFifthSndFactor_sub_norm_sq`
- `GoldenZeroSectorDescentPacket.five_not_dvd_D`
- `dvd_sub`
- `Prime.dvd_of_dvd_pow`
- `norm_num`
- `ring_nf`
- `exact_mod_cast`

特に中心となる既存補題は

```lean
theorem five_dvd_goldenFifthSndFactor_sub_norm_sq (gamma : GoldenInt) :
    (5 : ℤ) ∣
      goldenFifthSndFactor gamma.fst gamma.snd - goldenNorm gamma ^ 2 := by
  refine ⟨gamma.fst * gamma.snd ^ 2 * (gamma.fst + gamma.snd), ?_⟩
  simp only [goldenFifthSndFactor, goldenNorm]
  ring
```

である。これは合同式として

$$
H(a,b) \equiv N(a,b)^2 \pmod 5
$$

を表している。

0392 自身では quartic polynomial を再展開せず、この既存の mod-5 bridge を利用している。

## 証明・構築の流れ

1. 結論を否定して

   ```lean
   intro hH
   ```

   により

   $$
   5\mid H(a,b)
   $$

   を仮定する。

2. mod-5 bridge を取得する。

   ```lean
   have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq gamma
   ```

   これは

   $$
   5\mid H(a,b)-N(a,b)^2
   $$

   である。

3. `dvd_sub hH hdiff` で二つの可除性を差し引き、`ring_nf` で式を正規化して

   $$
   5\mid N(a,b)^2
   $$

   を得る。

4. 5 の素性を使う。

   ```lean
   (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
   ```

   これにより

   $$
   5\mid N(a,b)
   $$

   を得る。

5. `hnorm` を rewrite して

   $$
   5\mid D
   $$

   に変換する。

6. 整数上の可除性を `exact_mod_cast` で自然数上へ移し、0382

   ```lean
   p.five_not_dvd_D
   ```

   と矛盾させる。

## Lean 固有の処理

### `dvd_sub hH hdiff`

数学上は

$$
5\mid H,
\qquad
5\mid H-N^2
$$

から直ちに

$$
5\mid N^2
$$

と書ける。

Lean では `dvd_sub` を用いて可除性証明を明示的に合成する。得られる式は syntactic に目的の `goldenNorm gamma ^ 2` と一致しない形を含むため、続けて

```lean
ring_nf at h
```

で正規化している。

### `Prime (5 : ℤ)`

ここで使っている素数性は自然数ではなく整数環上の `Prime (5 : ℤ)` である。

```lean
show Prime (5 : ℤ) by norm_num
```

により instance をその場で証明し、

```lean
.dvd_of_dvd_pow
```

で

$$
5\mid N^2 \Longrightarrow 5\mid N
$$

を得ている。

### `rw [hnorm] at hnormFive`

`goldenNorm gamma` は整数、`p.D` は自然数であるため、`hnorm` 自体が

```lean
goldenNorm gamma = (p.D : ℤ)
```

という cast を含む。この rewrite により `hnormFive` は整数上の

```lean
(5 : ℤ) ∣ (p.D : ℤ)
```

になる。

### `exact_mod_cast`

一方 0382 `five_not_dvd_D` の対象は自然数上の

```lean
¬ 5 ∣ p.D
```

である。最後に

```lean
by exact_mod_cast hnormFive
```

を使って整数可除性を自然数可除性へ移している。

この theorem の Lean 上の主な難所は、数学そのものよりも `ℤ` と `ℕ` の境界にある。

## 冗長・重複箇所

証明は短く、論理的な冗長性はほぼない。ただしコードベース全体では同型の証明が既に存在する。

`SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_sndFactor` でも、同じ

```lean
five_dvd_goldenFifthSndFactor_sub_norm_sq
```

から norm square の 5 可除性を作り、prime 性で norm 自身へ降ろしている。

0392 はその descent-packet 版であり、違いは contradiction endpoint が

- ramifier-stripped packet 側では `zeroSector_five_not_dvd_gamma_norm`
- descent packet 側では `five_not_dvd_D` と `hnorm`

である点にある。

この意味で algebraic core には重複がある。

## 最適化候補

### 1. mod-5 transfer helper の抽出

一般補題として例えば

```lean
theorem five_dvd_norm_of_five_dvd_sndFactor
    (gamma : GoldenInt)
    (hH : (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd) :
    (5 : ℤ) ∣ goldenNorm gamma := by
  ...
```

を用意すれば、0392 は

```lean
intro hH
have hNorm := five_dvd_norm_of_five_dvd_sndFactor gamma hH
rw [hnorm] at hNorm
exact p.five_not_dvd_D (by exact_mod_cast hNorm)
```

程度まで縮約できる。

これは既存の `zeroSector_five_not_dvd_sndFactor` とも共通化できるため、重複除去として自然である。

### 2. cast bridge の局所 helper

`(5 : ℤ) ∣ (D : ℤ)` から `5 ∣ D` への変換が複数箇所に現れるなら、明示的な helper を作ることで `exact_mod_cast` 依存を局所化できる。

ただし現状の1行は十分読みやすく、必須の変更ではない。

### 3. `ring_nf` の依存縮小

`dvd_sub hH hdiff` が返す式を別の可除性 combinator でより直接的に整形できれば `ring_nf` を避けられる可能性はある。ただしこの変更は可読性を改善するとは限らない。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は現在

```lean
import Mathlib
```

を使用している。

0392 が直接使用する Mathlib 機能は主に以下である。

- 整数の divisibility
- `Prime.dvd_of_dvd_pow`
- `norm_num`
- `ring_nf`
- `exact_mod_cast`

また `GoldenInt`、`goldenNorm`、`goldenFifthSndFactor`、packet 定義、0382、および mod-5 bridge はプロジェクト内部の先行宣言である。

理論上は `Mathlib` 全体ではなく、整数可除性、prime、ring tactic、norm-num、norm-cast 系の必要モジュールへ import を狭められる可能性がある。

ただし本作業では Lean build を実行していないため、**厳密な最小 import 集合は未確認** である。したがって import 最適化は候補に留める。

## Comparator challenge 化の可否

**可。** ただし単独の0392は短いため、難度は低〜中程度である。

良い challenge にするなら、次の先行 API を与える。

```lean
five_dvd_goldenFifthSndFactor_sub_norm_sq
p.five_not_dvd_D
hnorm
```

そして

```lean
¬ (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd
```

を再構成させる。

評価点は次の通りである。

1. `H ≡ N^2 (mod 5)` を可除性として正しく使えるか。
2. `5 ∣ N^2` から prime 性で `5 ∣ N` を取り出せるか。
3. `hnorm` を通して `D` へ移せるか。
4. `ℤ` から `ℕ` への cast を安全に処理できるか。

より substantive な challenge にするなら、先行補題 `five_dvd_goldenFifthSndFactor_sub_norm_sq` 自体も伏せて、

$$
H(a,b)-N(a,b)^2
$$

が 5 の倍数であることから再構成させるとよい。その場合は polynomial identity と divisibility/cast の二層を同時に評価できる。

## 次に読むべき宣言

次は

```lean
theorem fifthRoot_measure_lt
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    ...
```

である。

宣言種別は `theorem`。

これは第五根の見える第二座標について、元 packet の `|s|` より真に小さいことを示す strict descent の中心不等式である。

0392 までで第五根側には

$$
H(a,b)>0,
\qquad
b>0,
\qquad
\gcd(|a|,|b|)=1,
\qquad
5\nmid H(a,b)
$$

という次世代 packet に必要な局所 invariant が揃った。次の `fifthRoot_measure_lt` では、それらを用いて **同じ型のデータを保ちながら measure だけを真に減らす** ことが示される。
