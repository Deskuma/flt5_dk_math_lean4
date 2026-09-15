# 0398 `goldenZeroSectorDescentPacket_of_candidate`

## 宣言種別

`def`

`GoldenZeroSectorCandidate` から、0397 の無限降下閉包へ入力できる `GoldenZeroSectorDescentPacket` を構築する定義である。

## Lean コード

```lean
/-- Every certified zero-sector candidate enters the recursive descent invariant. -/
def goldenZeroSectorDescentPacket_of_candidate
    (p : GoldenZeroSectorCandidate) : GoldenZeroSectorDescentPacket where
  base := ⟨p.r, p.s⟩
  t := 5 * p.c ^ 2
  D := p.d ^ 2
  t_pos := mul_pos (by norm_num) (pow_pos p.c_pos 2)
  D_pos := pow_pos p.d_pos 2
  coprime_coords := p.coprime_coords
  snd_eq := Or.inr (by
    rw [p.s_eq_neg_five_pow_mul_tenth]
    push_cast
    ring)
  H_eq := by
    rw [p.H_eq_tenth]
    push_cast
    ring
  five_not_dvd_norm := by
    intro hFive
    apply p.five_not_dvd_b
    rcases p.norm_eq_or_eq_neg with h | h
    · rw [h] at hFive
      exact_mod_cast hFive
    · rw [h] at hFive
      exact_mod_cast (Int.dvd_neg.mp hFive)
```

## Lean の型

```lean
goldenZeroSectorDescentPacket_of_candidate :
  GoldenZeroSectorCandidate → GoldenZeroSectorDescentPacket
```

入力は zero-sector 算術をすでに満たす certified candidate `p`、出力は recursive descent invariant を満たす packet である。

この宣言は theorem ではなく `def` なので、新しい命題を証明するというより、既存の証明データを別の構造へ **再梱包する constructor** である。

## 数学的意味

候補 `p` は整数座標

$$
(r,s)
$$

と正の自然数パラメータ $c,d$ を持ち、zero-sector 由来の関係式を備えている。ここから descent packet のパラメータを

$$
\gamma=(r,s),\qquad
 t=5c^2,\qquad
 D=d^2
$$

と置く。

candidate 側の既知の十乗表示から、packet が要求する第五冪表示へ指数をまとめ直す。

`s` について candidate 側では負号付きの形

$$
s=-5^6c^{10}
$$

が与えられている。これを

$$
s=-5(5c^2)^5=-5t^5
$$

と書き換えることで、`snd_eq` の負側 branch を満たす。

同様に quartic factor $H(r,s)$ の十乗表示を

$$
H(r,s)=d^{10}=(d^2)^5=D^5
$$

と読み替え、packet の `H_eq` を得る。

さらに candidate の norm 条件

$$
N(r,s)=d^2
\quad\text{または}\quad
N(r,s)=-d^2
$$

と $5\nmid d$ を用いて

$$
5\nmid N(r,s)
$$

を回収する。

したがって、この定義の本質は

$$
\text{candidate arithmetic}
\longrightarrow
\text{recursive descent invariant}
$$

という型変換である。

## 証明全体での役割

0397 `goldenZeroSectorDescentPacket_false` は、任意の `GoldenZeroSectorDescentPacket` が存在すれば `False` を導く。しかし、その theorem 単独では元の zero-sector candidate を直接受け取れない。

0398 はそのインターフェース差を埋める bridge である。

依存関係は

$$
\text{GoldenZeroSectorCandidate}
\xrightarrow{\text{0398}}
\text{GoldenZeroSectorDescentPacket}
\xrightarrow{\text{0397}}
\bot
$$

となる。

このため次の 0399 `goldenZeroSectorCandidate_false` は、新しい算術をほとんど行わず、0398 の構築結果を 0397 に渡すだけで閉じられる。

## 直接依存する定義・補題

主要な直接依存は次である。

- `GoldenZeroSectorCandidate`
- `GoldenZeroSectorDescentPacket`
- `GoldenInt`
- `GoldenZeroSectorCandidate.r`
- `GoldenZeroSectorCandidate.s`
- `GoldenZeroSectorCandidate.c`
- `GoldenZeroSectorCandidate.d`
- `GoldenZeroSectorCandidate.c_pos`
- `GoldenZeroSectorCandidate.d_pos`
- `GoldenZeroSectorCandidate.coprime_coords`
- `GoldenZeroSectorCandidate.s_eq_neg_five_pow_mul_tenth`
- `GoldenZeroSectorCandidate.H_eq_tenth`
- `GoldenZeroSectorCandidate.five_not_dvd_b`
- `GoldenZeroSectorCandidate.norm_eq_or_eq_neg`
- `mul_pos`
- `pow_pos`
- `Int.dvd_neg`
- tactics `norm_num`, `push_cast`, `ring`, `exact_mod_cast`

`GoldenZeroSectorDescentPacket` 側で埋める field は

```lean
base
t
D
t_pos
D_pos
coprime_coords
snd_eq
H_eq
five_not_dvd_norm
```

である。

## 構築の流れ

1. base を candidate の整数座標そのものにする。

   ```lean
   base := ⟨p.r, p.s⟩
   ```

2. recursive fifth-power shape に合うように自然数パラメータを

   ```lean
   t := 5 * p.c ^ 2
   D := p.d ^ 2
   ```

   と定める。

3. `p.c_pos` と `p.d_pos` から `t_pos`, `D_pos` を即座に得る。

4. coordinate coprimality は candidate の field をそのまま再利用する。

   ```lean
   coprime_coords := p.coprime_coords
   ```

5. `snd_eq` は負 branch `Or.inr` を選ぶ。candidate の十乗式を rewrite した後、cast を整理し、ring normalization で

   $$
   -5^6c^{10}=-5(5c^2)^5
   $$

   を証明する。

6. `H_eq` も同様に candidate の十乗式を rewrite し、

   $$
   d^{10}=(d^2)^5
   $$

   を ring normalization で示す。

7. 最後に `five_not_dvd_norm` を証明する。$5$ が norm を割ると仮定し、candidate の norm が $d^2$ または $-d^2$ である二つの場合に分ける。

8. どちらの場合も整数可除性を自然数側へ `exact_mod_cast` で戻し、`p.five_not_dvd_b` と矛盾させる。

## Lean 固有の処理

### structure literal による依存データの再梱包

この定義の中心は

```lean
def ... : GoldenZeroSectorDescentPacket where
```

という structure literal である。各 field を順に埋めるため、数学的には「既知の性質をまとめ直す」だけでも Lean 上では target structure が要求する型に正確に合わせる必要がある。

### `Or.inr`

`GoldenZeroSectorDescentPacket.snd_eq` は符号を許す disjunction になっている。candidate から得られる `s` は負符号側なので、ここでは明示的に

```lean
Or.inr
```

を選択する。

### `push_cast`

candidate 側の $c,d$ は自然数であり、`s` や `H` の等式は整数世界にある。`push_cast` は

$$
((c^2 : \mathbb N):\mathbb Z)
$$

のような cast を積・冪の内側へ押し込み、後続の `ring` が処理できる多項式形へ正規化する。

### `ring`

ここでの `ring` は深い数論を証明しているのではない。すでに与えられた十乗形を、packet が要求する第五冪形へ代数的に再表現する役割である。

### `exact_mod_cast`

`five_not_dvd_norm` では norm の可除性は `ℤ` 上、一方 `p.five_not_dvd_b` は自然数側の非可除性である。`exact_mod_cast` はこの型境界を越える。

負 norm branch では先に

```lean
Int.dvd_neg.mp hFive
```

で

$$
5\mid -d^2 \Longrightarrow 5\mid d^2
$$

へ戻してから cast する。

## 冗長・重複箇所

この定義は比較的短く、算術的重複も限定的である。ただし次の二点は抽象化候補である。

第一に、十乗から第五冪への変換

$$
c^{10}=(c^2)^5
$$

と

$$
d^{10}=(d^2)^5
$$

は同じ指数恒等式を別 field で繰り返している。汎用 lemma

```lean
pow_ten_eq_sq_pow_five
```

のようなものがあれば `push_cast; ring` の局所依存を減らせる。

第二に、

```lean
N = D ∨ N = -D
```

と `¬ 5 ∣ D` から `¬ 5 ∣ N` を得るパターンは、符号付き norm を扱う他の箇所でも再利用可能である。整数可除性の符号不変性をまとめた helper に切り出せる。

ただし現在のコードは各 field の由来が近接しており、監査性は高い。短縮だけを目的とした抽象化は必須ではない。

## 最適化候補

### 1. exponent-normalization lemma

```lean
(c : ℤ) ^ 10 = ((c ^ 2 : ℕ) : ℤ) ^ 5
```

型の helper を用意すれば、`snd_eq` と `H_eq` の proof block を短くできる。

### 2. signed divisibility transport

例えば概念的に

```lean
not_dvd_of_eq_or_eq_neg
```

のような補題を用意し、

$$
N=D\lor N=-D,
\qquad 5\nmid D
$$

から

$$
5\nmid N
$$

を一度で処理できる。

### 3. candidate-to-packet API の明示化

0398 は proof pipeline の重要な境界なので、将来 source を分割するなら `CandidateToDescent` のような専用 module/interface に置く価値がある。算術発見層と well-founded descent 層の結合点がさらに明確になる。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は現在

```lean
import Mathlib
```

を使用している。

0398 自体で直接見える Mathlib 側の機能は、整数・自然数の基本算術、`pow_pos`、`mul_pos`、整数可除性、ならびに `norm_num`, `push_cast`, `ring`, `exact_mod_cast` の各 tactic である。

したがって理論上は `Mathlib` 全体より狭い import にできる可能性が高い。しかしこの宣言はリポジトリ内の `GoldenZeroSectorCandidate` と `GoldenZeroSectorDescentPacket` の定義・補題にも依存しており、今回は Lean build を行わない条件なので **正確な最小 import 集合は未確認** である。

import 最適化を行うなら、まず source module 側の局所 import を基準にし、tactic import を一つずつ削減してビルド確認するのが安全である。

## Comparator challenge 化の可否

**可能。難度は中程度。**

challenge として切り出す場合、`GoldenZeroSectorCandidate` と `GoldenZeroSectorDescentPacket` の完全な巨大定義を持ち込むより、0398 が実際に消費する field だけを持つ最小 structure を用意するとよい。

課題の本質は次の三点に集約できる。

1. $-5^6c^{10}$ を $-5(5c^2)^5$ に正規化する。
2. $d^{10}$ を $(d^2)^5$ に正規化する。
3. $N=\pm d^2$ と $5\nmid d$ から $5\nmid N$ を型を跨いで移送する。

特に `push_cast` / `exact_mod_cast` と structure construction の扱いを評価できるため、Comparator 用の実装力テストとして良い題材である。

一方、FLT5 全体の数学的難所そのものを測る challenge ではない。0398 はすでに確立した算術情報の **transport / packaging** が中心である。

## 次に読むべき宣言

次は **0399 `goldenZeroSectorCandidate_false`**、種別は `theorem` である。

```lean
theorem goldenZeroSectorCandidate_false
    (p : GoldenZeroSectorCandidate) : False :=
  goldenZeroSectorDescentPacket_false
    (goldenZeroSectorDescentPacket_of_candidate p)
```

0398 が candidate を descent packet に変換したため、0399 はその結果を 0397 `goldenZeroSectorDescentPacket_false` に渡すだけで zero-sector candidate 自体を排除する。

したがって局所的な流れは

$$
\text{candidate}
\xrightarrow{0398}
\text{descent packet}
\xrightarrow{0397}
\bot
$$

で閉じる。
