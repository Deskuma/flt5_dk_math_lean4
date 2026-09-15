# 0336 — `GoldenZeroSectorFactorData.odd_eleven_channel`

## 宣言種別

この宣言は **`theorem`** である。

odd branch の exact factor certificate から、素数 $11$ が `d` 側へ強制される一方で、`c` および `c` が所有する第五冪因子 `e`,`f`,`e*f` からは排除されることをまとめて取り出す。

```lean
/-- The odd branch exposes the forced eleven channel and excludes eleven from
every factor owned by `c`. -/
theorem GoldenZeroSectorFactorData.odd_eleven_channel
    {p : GoldenZeroSectorInversionPacket}
    (data : GoldenZeroSectorFactorData p)
    (hbranch : data.branch = .odd) :
    ∃ e f : ℕ,
      11 ∣ p.source.d ∧
      ¬ 11 ∣ p.source.c ∧
      ¬ 11 ∣ e ∧
      ¬ 11 ∣ f ∧
      ¬ 11 ∣ e * f := by
  cases data with
  | odd e f _ _ _ hefD _ _ _ _ _ hdiff =>
      have h11d : 11 ∣ p.source.d :=
        eleven_dvd_d_of_fifth_add_four_fifth hdiff
      have h11c : ¬ 11 ∣ p.source.c := by
        intro h11c
        exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) h11c h11d)
          p.coprime_c_d
      have h11ef : ¬ 11 ∣ e * f := by
        intro h11ef
        exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) h11ef h11d) hefD
      have h11e : ¬ 11 ∣ e := by
        intro h11e
        exact h11ef (dvd_mul_of_dvd_left h11e f)
      have h11f : ¬ 11 ∣ f := by
        intro h11f
        exact h11ef (dvd_mul_of_dvd_right h11f e)
      exact ⟨e, f, h11d, h11c, h11e, h11f, h11ef⟩
  | evenLeftLow => simp [GoldenZeroSectorFactorData.branch] at hbranch
  | evenRightLow => simp [GoldenZeroSectorFactorData.branch] at hbranch
```

## Lean の型

宣言の型は次である。

```lean
GoldenZeroSectorFactorData.odd_eleven_channel :
  {p : GoldenZeroSectorInversionPacket} →
  (data : GoldenZeroSectorFactorData p) →
  data.branch = .odd →
  ∃ e f : ℕ,
    11 ∣ p.source.d ∧
    ¬ 11 ∣ p.source.c ∧
    ¬ 11 ∣ e ∧
    ¬ 11 ∣ f ∧
    ¬ 11 ∣ e * f
```

固定された inversion packet `p` と、その packet に依存する exact factor data `data` を受け取る。さらに

```lean
hbranch : data.branch = .odd
```

により odd branch であることを要求する。

結論は existential で `e,f : ℕ` を返し、それらについて五つの $11$-進情報を同時に返す。

$$
11 \mid d,
\qquad
11 \nmid c,
\qquad
11 \nmid e,
\qquad
11 \nmid f,
\qquad
11 \nmid ef.
$$

ここで `e,f` は任意の自然数ではなく、`GoldenZeroSectorFactorData.odd` constructor 内に格納されていた第五冪因子である。

## 数学的主張

odd branch では 0334 の certificate により、ある正の互いに素な $e,f$ が存在し、特に

$$
A_0 = 2e^5,
\qquad
B_0 = 2f^5,
$$

および

$$
e^5 + 4d^5 = f^5
$$

を満たす。また certificate は

$$
\gcd(ef,d)=1
$$

も保持する。

0332 `eleven_dvd_d_of_fifth_add_four_fifth` を差分方程式へ適用すると

$$
11 \mid d
$$

が従う。

一方、inversion packet 自体は

$$
\gcd(c,d)=1
$$

を保持するため、$11\mid d$ と同時に $11\mid c$ は起こり得ない。したがって

$$
11 \nmid c.
$$

同様に factor certificate の

$$
\gcd(ef,d)=1
$$

から

$$
11 \nmid ef
$$

を得る。さらに $11\mid e$ なら $11\mid ef$、$11\mid f$ なら $11\mid ef$ なので、

$$
11 \nmid e,
\qquad
11 \nmid f
$$

も従う。

つまり素数 $11$ は odd branch の差分方程式によって **`d` 側へ強制される** 一方、互いに素性によって `c` が所有する側から一斉に排除される。この意味で theorem 名の `eleven_channel` は、素数 $11$ の所属先を一方向へ固定する channel を表している。

## 証明全体での役割

この theorem は 0331–0332 で作った局所的な mod $11$ 算術を、0334 の exact factorization packet へ接続する API である。

0331 では第五冪剰余を

$$
0,\pm1 \pmod{11}
$$

へ分類した。

0332 ではその分類を使い、

$$
e^5+4d^5=f^5
$$

から

$$
11\mid d
$$

を導いた。

しかし 0332 単体では `c`、`e`、`f` の ownership や互いに素性を知らない。今回の theorem が `GoldenZeroSectorFactorData.odd` に保存された

```lean
coprime_ef_d : Nat.Coprime (e * f) p.source.d
```

と inversion packet の

```lean
p.coprime_c_d
```

を組み合わせることで、mod $11$ の局所結論を factor packet 全体の構造的結論へ昇格させる。

この theorem により後続では、odd branch に入った瞬間に $11$ の所属について次を一括して利用できる。

$$
11\mid d,
\qquad
11\nmid c e f.
$$

厳密には最後の式は積にまとめた略記であり、Lean の結論は `c`,`e`,`f`,`e*f` について個別の非可除性を返す。

## 直接依存する定義・補題

### `GoldenZeroSectorFactorData`

0334 の dependent inductive。

今回の odd constructor から必要なのは主に

```lean
hefD : Nat.Coprime (e * f) p.source.d
hdiff : e ^ 5 + 4 * p.source.d ^ 5 = f ^ 5
```

である。

正性、`e` と `f` 自身の互いに素性、奇性、`A_eq`,`B_eq`,`ownership` はこの theorem の証明では直接使用しない。

### `GoldenZeroSectorFactorData.branch`

0335 の `def`。

仮定

```lean
hbranch : data.branch = .odd
```

を形成し、even branch を矛盾として排除するために使われる。

### `eleven_dvd_d_of_fifth_add_four_fifth`

0332 の theorem。

```lean
hdiff : e ^ 5 + 4 * p.source.d ^ 5 = f ^ 5
```

から

```lean
h11d : 11 ∣ p.source.d
```

を得る直接の算術エンジンである。

### `p.coprime_c_d`

`GoldenZeroSectorInversionPacket` の source 側から利用できる互いに素性。

$$
\gcd(c,d)=1
$$

により、$11\mid d$ から $11\nmid c$ を得る。

### `Nat.not_coprime_of_dvd_of_dvd`

同じ $q>1$ が二数をともに割るなら、それらは互いに素ではないことを表す Mathlib 補題。

ここでは $q=11$ として二度利用する。

### `dvd_mul_of_dvd_left` / `dvd_mul_of_dvd_right`

$11\mid e$ または $11\mid f$ から $11\mid ef$ を作るために使う。

## 証明の流れ

### 1. factor data を constructor ごとに分解する

```lean
cases data with
```

により `GoldenZeroSectorFactorData` の三 branch を直接調べる。

odd branch では多数の field のうち必要なものだけを

```lean
hefD
hdiff
```

として受け取る。

### 2. odd branch で $11\mid d$ を得る

```lean
have h11d : 11 ∣ p.source.d :=
  eleven_dvd_d_of_fifth_add_four_fifth hdiff
```

0332 をそのまま適用する。

### 3. $11\nmid c$ を互いに素性から得る

$11\mid c$ を仮定すると、既に $11\mid d$ なので `c,d` は互いに素でなくなる。

```lean
exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num) h11c h11d)
  p.coprime_c_d
```

`(by norm_num)` は $1<11$ の数値証明を埋める。

### 4. $11\nmid ef$ を得る

同じ構造を certificate の

```lean
hefD : Nat.Coprime (e * f) p.source.d
```

へ適用する。

$$
11\mid ef,
\quad
11\mid d
$$

なら $\gcd(ef,d)\neq1$ となるため矛盾する。

### 5. $11\nmid e$ と $11\nmid f$ へ分解する

例えば $11\mid e$ を仮定すると

```lean
dvd_mul_of_dvd_left h11e f
```

により $11\mid ef$ が得られ、直前の `h11ef` に矛盾する。

$f$ についても左右を入れ替えた同じ証明である。

### 6. existential packet を組み立てる

```lean
exact ⟨e, f, h11d, h11c, h11e, h11f, h11ef⟩
```

で必要な factor witness と五つの性質を返す。

### 7. even branch を `hbranch` で排除する

```lean
| evenLeftLow => simp [GoldenZeroSectorFactorData.branch] at hbranch
| evenRightLow => simp [GoldenZeroSectorFactorData.branch] at hbranch
```

0335 の `branch` 定義を展開すると、仮定はそれぞれ

```lean
.evenLeftLow = .odd
.evenRightLow = .odd
```

という異なる constructor の等式になるため、`simp` が矛盾として閉じる。

## Lean 固有の処理

### dependent inductive の `cases`

`data : GoldenZeroSectorFactorData p` は `p` に依存する inductive value である。`cases data` によって constructor 固有の証明 field を局所 context へ露出させる。

odd branch だけが結論を構築でき、他の二 branch は `hbranch` と constructor disjointness で消える。

### `_` による不要 field の破棄

odd constructor は多数の引数を持つが、pattern

```lean
| odd e f _ _ _ hefD _ _ _ _ _ hdiff =>
```

では必要な `e`,`f`,`hefD`,`hdiff` だけに名前を付けている。

これは proof certificate が豊富でも theorem が依存する最小情報を明示できる Lean らしい書き方である。

### Prop と否定の関数表現

```lean
¬ 11 ∣ p.source.c
```

は Lean では

```lean
11 ∣ p.source.c → False
```

なので、各非可除性証明は

```lean
intro h11c
...
```

という反証法ではなく、否定を関数として直接構築している。

### constructor disjointness を `simp` に任せる

0335 の `branch` を展開した後の異なる enum constructor の不等性は、手動で `cases hbranch` などを書く必要がなく `simp` が処理する。

## 冗長・重複箇所

`h11c` と `h11ef` の証明はほぼ同型である。

どちらも

1. $11$ が左側対象を割ると仮定
2. `h11d : 11 ∣ d` と合わせる
3. `Nat.not_coprime_of_dvd_of_dvd` で既知の `Nat.Coprime` に矛盾

という構造を持つ。

また `h11e` と `h11f` も左右対称である。

ただし全体は短く、抽象化するとかえって可読性を落とす可能性があるため、現行の明示的実装は妥当である。

constructor pattern では多くの `_` が並ぶため、`GoldenZeroSectorFactorData` の field 順序変更に対してはやや脆い。しかし constructor が positional argument を持つ inductive である以上、これは自然なコストでもある。

## 最適化候補

### 共通素因子排除の小補題化

局所的に

```lean
Nat.Coprime a d → 11 ∣ d → ¬ 11 ∣ a
```

のような helper を用意すれば `h11c`,`h11ef` は一行ずつにできる。

ただしこの theorem 単体では抽象化利益は小さい。

### `Nat.Coprime` の既存 API の直接利用

Mathlib に、prime divisibility と coprimality をより直接結ぶ適切な lemma があれば `Nat.not_coprime_of_dvd_of_dvd` より短くできる可能性がある。ただし今回の正本確認範囲では、その置換が確実に通ることまでは確認していない。

### branch-indexed API

`hbranch : data.branch = .odd` を受けてから `cases data` する代わりに、odd constructor 専用の accessor theorem を作る設計も可能である。

しかし現在の API は、呼び出し側が certificate の内部 constructor を露出させず branch label だけで条件指定できる利点がある。0335 の設計意図とも整合しており、現行形は十分合理的である。

### 結論 packet の structure 化

今後同じ五つの性質を複数 theorem が再利用するなら、existential conjunction

```lean
∃ e f, ... ∧ ... ∧ ...
```

を専用 structure にする余地がある。

現時点では一 theorem の局所 API としては existential の方が軽量である。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

今回の theorem が直接利用する Mathlib 機能は少なくとも

- `Nat.Coprime`
- `Nat.not_coprime_of_dvd_of_dvd`
- `dvd_mul_of_dvd_left`
- `dvd_mul_of_dvd_right`
- `norm_num`
- `simp`

である。

加えて `GoldenZeroSectorFactorData`、`GoldenZeroSectorInversionPacket`、0332 の theorem など前段の DkMath 宣言が必要である。

source module `SignedGoldenZeroSectorFactorization.lean` 全体はこの theorem 以外にも `omega`、`ring`、parity API、第五冪分解、自然数・整数 cast などを広く利用しているため、この一宣言だけから module 全体の最小 import 集合は確定できない。

理論上は `Mathlib` umbrella import を、coprimality・divisibility・numeric tactics を提供する個別 import へ縮小できる可能性がある。しかし本タスクでは Lean ビルドを行わないため、最小 import 候補の確定はしていない。

## Comparator challenge 化の可否

**可能。難度は中程度。**

良い challenge になる理由は、単なる算術計算ではなく、

- dependent inductive の branch elimination
- branch-specific field の抽出
- 既存 theorem `eleven_dvd_d_of_fifth_add_four_fifth` の再利用
- `Nat.Coprime` から prime exclusion を導く
- 個別因子から積への divisibility lifting

を短い証明の中で組み合わせる必要があるからである。

challenge では 0332–0335 を既知として与え、`odd_eleven_channel` の本体のみを穴埋めさせる形式が適している。

比較評価では、単に `11 ∣ d` を示すだけでは不十分で、`c`,`e`,`f`,`e*f` の四つの非可除性を正しく構築し、even branch を `hbranch` から排除できているかを確認できる。

## 次に読むべき宣言

次は

```lean
structure GoldenZeroSectorFactorPacket : Type where
  inversion : GoldenZeroSectorInversionPacket
  factors : GoldenZeroSectorFactorData inversion
```

を読むべきである。

これは theorem ではなく **`structure`** である。

今回まで個別に扱ってきた

- inversion certificate
- その inversion packet に依存する exact factor data

を一つの package に束ねる。

特に field

```lean
factors : GoldenZeroSectorFactorData inversion
```

は先行 field `inversion` に依存する dependent field であり、零セクター反転から第五冪 factorization branch までを一つの proof-carrying packet として後続 descent へ渡すための容器になる。