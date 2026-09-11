# 0381 `five_not_dvd_H`

## 宣言種別

`theorem`

`GoldenZeroSectorDescentPacket` namespace 内で、packet の quartic factor `goldenFifthSndFactor` が 5 で割れないことを、base norm の 5 非可除性と `goldenFifthSndFactor - goldenNorm^2` の 5 可除性から引き出す補題である。

## Lean コード

```lean
theorem five_not_dvd_H (p : GoldenZeroSectorDescentPacket) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor p.base.fst p.base.snd := by
  intro hH
  apply p.five_not_dvd_norm
  have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq p.base
  have hnormSq : (5 : ℤ) ∣ goldenNorm p.base ^ 2 := by
    have h := dvd_sub hH hdiff
    ring_nf at h
    exact h
  exact (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
```

## Lean の型

namespace を展開すると、型は概念的に

```lean
GoldenZeroSectorDescentPacket.five_not_dvd_H :
  (p : GoldenZeroSectorDescentPacket) →
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor p.base.fst p.base.snd
```

である。

`p.base : GoldenInt` なので `p.base.fst`, `p.base.snd : ℤ`、

```lean
goldenFifthSndFactor p.base.fst p.base.snd : ℤ
```

である。したがって今回の divisibility は整数環 `ℤ` 上の可除性である。

packet 自身は field

```lean
five_not_dvd_norm : ¬ (5 : ℤ) ∣ goldenNorm base
```

を保持しており、今回の theorem はこの norm 側の 5 非可除性を quartic factor 側へ移送する。

## 数学的主張

`base = (r,s)` と置き、

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s),
\qquad
N(r,s)=\operatorname{goldenNorm}(r,s)
$$

と書く。

既存補題 `five_dvd_goldenFifthSndFactor_sub_norm_sq` は、この base に対して

$$
5 \mid H(r,s)-N(r,s)^2
$$

という合同関係を与える。

一方、descent packet は

$$
5\nmid N(r,s)
$$

を invariant として保持している。

もし反対に

$$
5\mid H(r,s)
$$

と仮定すると、上の差の可除性から

$$
5\mid N(r,s)^2
$$

が従う。5 は素数なので

$$
5\mid N(r,s)^2
\Longrightarrow
5\mid N(r,s),
$$

となり packet invariant に矛盾する。

したがって

$$
5\nmid H(r,s)
$$

である。

## 証明全体での役割

0380 `H_pos` は quartic factor について

$$
H(r,s)>0
$$

という順序情報を公開した。

今回の `five_not_dvd_H` は同じ因子について

$$
5\nmid H(r,s)
$$

という 5-adic / divisibility 情報を公開する。

これにより descent packet の quartic side は

$$
\text{positive}
\quad+\quad
\text{prime to }5
$$

という二つの重要な性質を持つことになる。

直後の `five_not_dvd_D` は `H_eq`

$$
H(r,s)=D^5
$$

と今回の theorem を組み合わせて

$$
5\nmid D
$$

を導く。さらにその情報は `lift_relPrime_conj` 内で `D^5` と 5 の coprimality を作る材料になり、quadratic lift とその共役が nonunit common divisor を持たないことを示す流れへ入る。

したがって今回の theorem は、packet に保存された norm 側の 5 非可除性を、fifth-power root `D` と re-entry factorization に利用できる形へ橋渡しする役割を持つ。

## 直接依存する定義・補題

直接依存するプロジェクト内宣言は次である。

- `GoldenZeroSectorDescentPacket`
- `GoldenZeroSectorDescentPacket.five_not_dvd_norm`
- `goldenFifthSndFactor`
- `goldenNorm`
- `five_dvd_goldenFifthSndFactor_sub_norm_sq`

今回の proof term から、`five_dvd_goldenFifthSndFactor_sub_norm_sq p.base` は少なくとも

```lean
(5 : ℤ) ∣
  goldenFifthSndFactor p.base.fst p.base.snd -
    goldenNorm p.base ^ 2
```

という形で利用されていることが確認できる。

Mathlib / Lean 側で直接使う主要機能は次である。

- `dvd_sub`
- `ring_nf`
- `Prime.dvd_of_dvd_pow`
- `norm_num`
- `intro`, `apply`, `have`, `exact`

0380 `H_pos` や 0379 `snd_natAbs_eq` には直接依存しない。今回の証明は `five_not_dvd_norm` と quartic/norm congruence だけで閉じている。

## 証明の流れ

1. 結論を否定し、quartic factor が 5 で割れると仮定する。

   ```lean
   intro hH
   ```

   すなわち

   $$
   5\mid H(r,s)
   $$

   を仮定する。

2. packet の

   ```lean
   p.five_not_dvd_norm
   ```

   に `apply` し、矛盾のために

   ```lean
   (5 : ℤ) ∣ goldenNorm p.base
   ```

   を示す問題へ変換する。

3. 既存の合同補題を取得する。

   ```lean
   have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq p.base
   ```

   これは数学的には

   $$
   5\mid H(r,s)-N(r,s)^2
   $$

   を与える。

4. `hH` と `hdiff` の差を取る。

   ```lean
   have h := dvd_sub hH hdiff
   ```

   左側の被除数は概念的に

   $$
   H-(H-N^2)=N^2
   $$

   となる。

5. `ring_nf` で多項式差を正規化する。

   ```lean
   ring_nf at h
   ```

   これにより

   ```lean
   (5 : ℤ) ∣ goldenNorm p.base ^ 2
   ```

   が得られる。

6. 整数 5 が prime であることを `norm_num` で供給し、prime が平方を割れば元も割ることを使う。

   ```lean
   exact (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
   ```

   よって

   $$
   5\mid N(r,s)^2
   \Longrightarrow
   5\mid N(r,s),
   $$

   となり `p.five_not_dvd_norm` と矛盾する。

## Lean 固有の処理

### `apply p.five_not_dvd_norm`

`five_not_dvd_norm` の型は否定命題

```lean
¬ (5 : ℤ) ∣ goldenNorm p.base
```

である。現在の goal が `False` なので `apply` すると、Lean はその否定命題が受け取るべき証拠

```lean
(5 : ℤ) ∣ goldenNorm p.base
```

を新しい goal にする。

これは contradiction proof を短く書く典型的な Lean の形である。

### `dvd_sub hH hdiff`

`dvd_sub` は同じ整数が二つの整数を割るなら、その差も割るという closure property を使う。

ここでは

```lean
hH    : 5 ∣ H
hdiff : 5 ∣ H - N^2
```

から

```lean
5 ∣ H - (H - N^2)
```

を得る。

### `ring_nf at h`

`dvd_sub` が作る式は syntactically には `N^2` そのものではない。`ring_nf` が ring normalization を行い、

$$
H-(H-N^2)=N^2
$$

を canonical form に直す。

この theorem で `ring_nf` が担うのは数論的推論ではなく、純粋な環式正規化である。

### `Prime.dvd_of_dvd_pow`

整数上で 5 が prime であることを

```lean
(show Prime (5 : ℤ) by norm_num)
```

として構成し、

```lean
.dvd_of_dvd_pow hnormSq
```

によって平方の可除性を底へ降ろしている。

指数は 2 だが、proof script では一般の `dvd_of_dvd_pow` API を使っているため、平方専用補題へ依存しない。

## 冗長・重複箇所

証明は短く、数学的重複はほとんどない。

ただし

```lean
have hnormSq : (5 : ℤ) ∣ goldenNorm p.base ^ 2 := by
  have h := dvd_sub hH hdiff
  ring_nf at h
  exact h
```

は `simpa` や `convert` で縮められる可能性がある。例えば概念的には

```lean
have hnormSq : (5 : ℤ) ∣ goldenNorm p.base ^ 2 := by
  simpa only [...] using dvd_sub hH hdiff
```

という形も考えられるが、必要な normalization lemma の具体形を確認していないため、現在の `ring_nf` の方が堅牢で読みやすい。

また `Prime (5 : ℤ)` は FLT5 proof 全体で繰り返し現れる可能性が高い。実際に重複が十分多いなら、5 の primality を named lemma として共有する余地はある。しかし `norm_num` で即時に閉じるため、抽象化の費用が利益を上回る可能性もある。

## 最適化候補

1. **現状維持が有力**

   `hH → hnormSq → norm divisibility → contradiction` という証明構造は数論的意味がそのまま Lean code に現れており、短さと可読性の均衡がよい。

2. **mod 5 congruence API の明示化**

   `five_dvd_goldenFifthSndFactor_sub_norm_sq` は本質的に

   $$
   H(r,s)\equiv N(r,s)^2\pmod 5
   $$

   を表す。下流で同じ congruence を何度も使うなら、`Int.ModEq 5 ...` 形式の theorem を追加し、divisibility difference と congruence のどちらを public API にするか整理する余地がある。

3. **`five_not_dvd_norm_sq` helper**

   `5 ∤ N` から `5 ∤ N^2` を頻繁に使うなら、prime property を一度包んだ helper が候補になる。ただし今回の proof は逆向きの contradiction で一度だけ用いるため、現段階では不要である。

4. **`ring_nf` の局所限定は良い**

   quartic definition や norm definitionを展開せず、`ring_nf` を `dvd_sub` 後の小さな式だけに適用している。これ以上大域的に `simp` / `ring_nf` をかけるより、現行の abstraction boundary を保つ方が望ましい。

## 必要 Mathlib import と import 最適化候補

standalone 正本は `import Mathlib` を使用している。

この theorem 単体で必要になる Mathlib 側の要素は概ね次である。

- 整数の可除性と `dvd_sub`
- prime element / `Prime.dvd_of_dvd_pow`
- polynomial normalization tactic `ring_nf`
- numeral arithmetic tactic `norm_num`
- 基本的な命題論理 tactic / term syntax

さらに実際の project module では、プロジェクト側の

- `GoldenZeroSectorDescentPacket`
- `goldenFifthSndFactor`
- `goldenNorm`
- `five_dvd_goldenFifthSndFactor_sub_norm_sq`

へ到達する import が必要である。

`ring_nf` と `norm_num` を使用するので、それぞれを提供する Mathlib tactic module が必要になる。厳密な最小 import 集合は Lean ビルドを行わない条件のため確認していない。したがって `import Mathlib` からの具体的削減は候補の提示に留める。

## Comparator challenge 化の可否

**可能。divisibility congruence と prime descent を組み合わせる良質な小規模 challenge に向く。**

challenge の本質は次の四段階である。

1. `5 ∣ H` を contradiction hypothesis として受け取る。
2. `5 ∣ H - N^2` と組み合わせて `5 ∣ N^2` を得る。
3. ring normalization で差の形を平方へ正規化する。
4. `Prime.dvd_of_dvd_pow` で `5 ∣ N` を得て packet invariant と矛盾させる。

単純な `ring` 問題だけではなく、可除性 closure・prime API・否定命題の goal transformation を同時に扱うため、0380 より一段よい Comparator challenge になる。

難度調整としては、

- `ring_nf` を許可する標準版
- `ring_nf` を禁止して等式変形を明示させる版
- `Prime.dvd_of_dvd_pow` の lemma 名を与えない探索版

が考えられる。

## 次に読むべき宣言

次は同じ namespace の

```lean
theorem five_not_dvd_D (p : GoldenZeroSectorDescentPacket) :
    ¬ 5 ∣ p.D := by
  intro hD
  apply p.five_not_dvd_H
  rw [p.H_eq]
  exact dvd_pow (Int.natCast_dvd.mpr hD) (by decide : 5 ≠ 0)
```

である。

今回得た

$$
5\nmid H(r,s)
$$

と packet invariant

$$
H(r,s)=D^5
$$

を使い、次は fifth root 自身について

$$
5\nmid D
$$

を得る。

つまり 5-adic clean property が

$$
N(r,s)
\longrightarrow
H(r,s)
\longrightarrow
D
$$

と順に伝播していく。その後 `coprime_s_H`, `coprime_D_s`, `lift_relPrime_conj` へ進み、re-entry element の relative primality を構成する流れになる。