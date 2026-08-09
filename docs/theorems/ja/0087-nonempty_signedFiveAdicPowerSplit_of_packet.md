# 0087 — `nonempty_signedFiveAdicPowerSplit_of_packet`

## Lean の型

```lean
private theorem nonempty_signedFiveAdicPowerSplit_of_packet
    {u v w : ℕ} (p : SignedFiveAdicPacket u v w) :
    Nonempty (SignedFiveAdicPowerSplit u v w) := by
  ...
```

本宣言は `private theorem` であり、module 外へ公開する API ではない。公開される `signedFiveAdicPowerSplit_of_packet` の内部存在証明として使われる。

## 数学的主張

`SignedFiveAdicPacket u v w` が与えられると、正の互いに素な自然数 $a,b$ が存在し、packet の三つの主要量を

$$
\operatorname{carrier}=5^4a^5,
$$

$$
\operatorname{residual}=5b^5,
$$

$$
\operatorname{distinguished}=5ab
$$

という exact power split に書ける。

Lean では存在量を裸の `∃ a b, ...` として返さず、0083 で定義した `SignedFiveAdicPowerSplit u v w` を構築し、その `Nonempty` を返す。

## 証明全体での役割

0082 では

$$
\gcd(\operatorname{carrier},\operatorname{residual})=5
$$

を確定し、0083 では desired normal form を record 型として定義した。0084–0086 はその record が後続で使う補助性質を整えた。

本 theorem は初めて packet からその record の実データを構成する。

流れは概念的には

$$
\mathrm{SignedFiveAdicPacket}
\Longrightarrow
\text{common factor }5\text{ を除去}
\Longrightarrow
\text{coprime fifth-power factor split}
\Longrightarrow
\mathrm{SignedFiveAdicPowerSplit}
$$

である。

このため `SignedFiveAdicPowerSplit` 層の実質的な constructor theorem といえる。

## 直接依存する定義・補題

主な直接依存は次である。

- `SignedFiveAdicPacket`
- `SignedFiveAdicPowerSplit`
- `signedFiveAdicPacket_gcd_eq_five`（0082）
- `fifth_power_factor_split`（0027）
- packet field
  - `p.five_dvd_carrier`
  - `p.five_dvd_distinguished`
  - `p.residual_shape`
  - `p.residual_mod_twentyFive`
  - `p.factor_eq`
  - `p.carrier_pos`
  - `p.residual_pos`
- `Nat.mul_div_cancel'`
- `Nat.coprime_div_gcd_div_gcd`
- `Nat.Prime.coprime_iff_not_dvd`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.Coprime.mul_left`
- `Nat.eq_of_mul_eq_mul_left`
- `Nat.pow_left_injective`
- `Nat.coprime_pow_left_iff`
- `Nat.coprime_pow_right_iff`
- `Nat.mod_eq_zero_of_dvd`
- tactics `ring`, `omega`, `norm_num`

## 証明の流れ

### 1. まず共通因子 5 を一度剥がす

```lean
let c := p.carrier / 5
let r := p.residual / 5
let d := p.distinguished / 5
```

と置く。

`carrier` と `distinguished` の 5 可除性は packet field に既にある。`residual` については

```lean
p.residual_shape
```

から

$$
\operatorname{residual}=5+25M=5(1+5M)
$$

を得て $5\mid\operatorname{residual}$ を示す。

したがって

$$
\operatorname{carrier}=5c,
$$

$$
\operatorname{residual}=5r,
$$

$$
\operatorname{distinguished}=5d
$$

が `Nat.mul_div_cancel'` で得られる。

### 2. 5 を剥がした $c,r$ が互いに素であることを得る

0082 より

$$
\gcd(\operatorname{carrier},\operatorname{residual})=5.
$$

`Nat.coprime_div_gcd_div_gcd` を使えば、両辺を gcd で割った

$$
\frac{\operatorname{carrier}}5=c,
\qquad
\frac{\operatorname{residual}}5=r
$$

が互いに素になる。Lean では

```lean
have hcopcr : Nat.Coprime c r := by
  have h := Nat.coprime_div_gcd_div_gcd
    (show 0 < Nat.gcd p.carrier p.residual by rw [hgcd]; decide)
  simpa [c, r, hgcd] using h
```

という形で取得する。

### 3. $5\nmid r$ を mod 25 で確認する

もし $5\mid r$ なら

$$
\operatorname{residual}=5r
$$

より $25\mid\operatorname{residual}$ となる。しかし packet は

$$
\operatorname{residual}\bmod25=5
$$

を保持しているため矛盾する。

この部分は 0084 の `five_not_dvd_b` と非常によく似た mod-25 no-extra-five argument である。

そこから

$$
\gcd(5,r)=1
$$

さらに

$$
\gcd(25,r)=1
$$

を作る。

### 4. 元の第五冪積を正規化する

packet の

$$
\operatorname{carrier}\cdot\operatorname{residual}
  =\operatorname{distinguished}^5
$$

に

$$
\operatorname{carrier}=5c,
\quad
\operatorname{residual}=5r,
\quad
\operatorname{distinguished}=5d
$$

を代入し整理すると

$$
(25c)r=(5d)^5
$$

を得る。

さらに

$$
\gcd(25c,r)=1
$$

も `h25copr.mul_left hcopcr` で得られる。

### 5. `fifth_power_factor_split` を適用する

0027 の一般補題を

$$
(25c)r=(5d)^5,
\qquad
\gcd(25c,r)=1
$$

へ適用すると、ある $A,b$ が存在して

$$
25c=A^5,
$$

$$
r=b^5
$$

を得る。

ここが本 theorem の中心である。five-adic packet 固有の算術を、既に証明済みの一般的な「互いに素な積が第五冪なら各因子も第五冪」という factor split へ接続している。

### 6. $A$ からさらに 5 を一つ剥がす

$25c=A^5$ なので $5\mid A^5$。5 は素数だから

$$
5\mid A.
$$

そこで $A=5a$ と書く。

$$
25c=(5a)^5
$$

から 25 を cancellation すると

$$
c=5^3a^5
$$

を得る。

したがって

$$
\operatorname{carrier}=5c=5^4a^5.
$$

一方、$r=b^5$ から

$$
\operatorname{residual}=5b^5
$$

も得る。

### 7. distinguished の式を第五冪の injectivity で回収する

`p.factor_eq` と上の二式から

$$
\operatorname{distinguished}^5=(5ab)^5
$$

が従う。

自然数上の第五冪は injective なので

$$
\operatorname{distinguished}=5ab
$$

を得る。

Lean では

```lean
apply Nat.pow_left_injective (by decide : 5 ≠ 0)
```

で equality を第五冪 equality へ持ち上げている。

### 8. $a,b>0$ と $\gcd(a,b)=1$ を証明する

$a=0$ なら `carrier = 0`、$b=0$ なら `residual = 0` になり、それぞれ packet の positivity と矛盾するので

$$
a>0,
\qquad
b>0
$$

を得る。

また $c$ と $r$ の coprimality に

$$
c=5^3a^5,
\qquad
r=b^5
$$

を代入し、左側から $5^3$ を落として

$$
\gcd(a^5,b^5)=1
$$

を得る。

`Nat.coprime_pow_left_iff` と `Nat.coprime_pow_right_iff` によって

$$
\gcd(a,b)=1
$$

へ戻す。

最後にこれらをまとめて `SignedFiveAdicPowerSplit` record を構成し、その `Nonempty` を返す。

## Lean 固有の処理

本 theorem は数学そのもの以上に、自然数の除算・存在 witness・record construction を Lean の型へ載せる処理が多い。

特に重要なのは次である。

1. `let c := carrier / 5` と置いてから、可除性を使って exact equality を復元する。
2. gcd を割った二数の coprimality を `Nat.coprime_div_gcd_div_gcd` で直接得る。
3. $5\nmid r$ の contradiction では divisibility witness を `rcases` して `ring` で $25$ の witness を組み立てる。
4. `fifth_power_factor_split` の existential result を

```lean
rcases ... with ⟨⟨A, hA⟩, ⟨b, hb⟩⟩
```

と展開する。
5. $A^5$ から $5\mid A$ を `Nat.Prime.dvd_of_dvd_pow` で引き戻す。
6. $25c=25(5^3a^5)$ の cancellation に `Nat.eq_of_mul_eq_mul_left` を使う。
7. distinguished の等式では第五冪 injectivity を利用する。
8. positivity は `by_contra` + `omega` + `norm_num` で零の場合を排除する。
9. 最後は anonymous structure literal を `Nonempty` の witness として包む。

## 冗長・重複箇所

最も目立つ重複は $5\nmid r$ の mod-25 argument である。0084 の `five_not_dvd_b` と本質的に同じ形を別の中間変数 `r` に対して再実装している。

また、

- divisible by 5 から quotient equality を作る処理
- positivity を zero contradiction で作る処理
- fifth-power coprimality から base coprimality へ戻す処理

も一般 helper に切り出せる可能性がある。

ただし本 theorem は constructor の内部実装で `private` であり、局所的に一度しか使わない中間量も多い。細かく helper 化しすぎると、かえって証明の全体像が分散する危険もある。

## 最適化候補

### 候補 A — mod-25 no-extra-five helper の共有

一般に

$$
x=5r,
\qquad
x\bmod25=5
$$

なら $5\nmid r$ という補題を切り出せば、0084 と本 theorem の重複を減らせる。

### 候補 B — quotient-by-exact-gcd helper

`gcd carrier residual = 5` から

```lean
c := carrier / 5
r := residual / 5
Nat.Coprime c r
```

をまとめて返す小さな構造または補題を用意すると、gcd stripping の意図が明確になる。

### 候補 C — valuation に寄せる

packet は five-adic valuation 情報も保持しているため、mod 25 による $5\nmid r$ を valuation-one から導く設計も考えられる。ただし現行証明は elementary で監査しやすい。

### 候補 D — constructor API を直接返す

現在は

```lean
private theorem ... : Nonempty (SignedFiveAdicPowerSplit ...)
```

を証明し、直後の `noncomputable def` が `Classical.choice` で witness を選ぶ。この二段構成は specification と choice を分離していて明瞭だが、constructive に record を直接返せるよう proof を組み替えれば classical choice を除ける余地がある。

ただし existential factor split 自体がどの形で witness を供給するかを含め、module 全体の API 方針と合わせて判断すべきである。

## 必要 Mathlib import と import 最適化候補

対象ブランチの generated standalone artifact は `import Mathlib` で構築されている。manifest では本 theorem は `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` に属する。

本 theorem が直接使う Mathlib 側機能は、自然数の gcd/coprimality/divisibility、素数、冪、自然数除算、`ring`、`omega`、`norm_num` である。

したがって theorem 単体に `import Mathlib` は過大である可能性が高い。ただし実際の分割元 module の import 列をこの回では Lean build で検証していないため、最小 import の具体的 module 名は断定しない。

import 最適化を行うなら、まず `SignedFiveAdicPowerSplit.lean` の直接依存 module と使用 tactic を列挙し、`import Mathlib` を段階的に狭めて Lean build で確認するのが安全である。本タスクでは build は行わない。

## Comparator challenge 化の可否

非常に適している。ここまでの一行 adapter よりも比較対象が豊富である。

比較案として、

1. 現行の gcd stripping + mod 25 + `fifth_power_factor_split` route。
2. five-adic valuation を前面に出す route。
3. quotient/gcd stripping を一般 helper に抽象化した route。
4. `Nonempty` + `Classical.choice` ではなく direct constructive record を返す route。

を用意できる。

評価軸は、

- proof term の短さ
- mathematical transparency
- classical dependency の有無
- reusable helper の汎用性
- packet API への依存度
- Lean version / Mathlib update に対する頑健性

がよい。

## PDF との対応

既存の日英 PDF は叙述的な背景資料として扱うが、今回 GitHub code search は 502 upstream error となり、この private constructor theorem に一対一対応する PDF のページ・節番号を確認できなかった。

したがって PDF 固有の定理番号・ページ番号・文章は推測で補っていない。形式的な最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された Lean source である。

## 次に読むべき定理

source 上で直後に置かれるのは

```lean
noncomputable def signedFiveAdicPowerSplit_of_packet
    {u v w : ℕ} (p : SignedFiveAdicPacket u v w) :
    SignedFiveAdicPowerSplit u v w :=
  Classical.choice (nonempty_signedFiveAdicPowerSplit_of_packet p)
```

である。

本号で証明した `Nonempty` から実際の `SignedFiveAdicPowerSplit` witness を一つ選び、後続 theorem が直接消費できる公開 API にする selection layer である。

したがって次の依存順は

$$
\mathrm{SignedFiveAdicPacket}
\Longrightarrow
\mathrm{Nonempty}(\mathrm{SignedFiveAdicPowerSplit})
\Longrightarrow
\mathrm{SignedFiveAdicPowerSplit}
$$

となる。