# 0400 `GoldenZeroSectorArithmeticExclusion`

## 宣言種別

`abbrev`

zero-sector の算術的排除条件を、後続の closure / receiver 層から利用できる一つの `Prop` として公開する略記である。

0399 `goldenZeroSectorCandidate_false` まででは、具体的な `GoldenZeroSectorCandidate` を構成できれば無限降下によって矛盾することが示された。0400 は、その candidate を構成するために必要な生の算術仮定を、構造体を経由せずに受け取る外部契約として並べ直している。

## Lean コード

```lean
/--
The zero-sector Diophantine proposition exposed by the certified primitive and
tenth-power splits.
-/
abbrev GoldenZeroSectorArithmeticExclusion : Prop :=
  ∀ (r s : ℤ) (a b : ℕ),
    0 < a →
    0 < b →
    Nat.Coprime a b →
    ¬ 5 ∣ b →
    (goldenNorm ⟨r, s⟩ = (b : ℤ) ∨ goldenNorm ⟨r, s⟩ = -(b : ℤ)) →
    s * goldenFifthSndFactor r s = -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10 →
    Nat.Coprime r.natAbs s.natAbs →
    (∃ c d : ℕ,
      s.natAbs = 5 ^ 6 * c ^ 10 ∧
      (goldenFifthSndFactor r s).natAbs = d ^ 10) →
    False
```

## Lean の型

宣言自体の型は

```lean
GoldenZeroSectorArithmeticExclusion : Prop
```

である。

`abbrev` を展開すると、任意の整数座標 `r s` と自然数パラメータ `a b` に対し、以下の算術仮定がすべて成立すれば `False` が導かれる、という高階命題になる。

論理形を簡略化すると

$$
\forall r,s\in\mathbb Z,\;\forall a,b\in\mathbb N,
\quad
\mathcal H(r,s,a,b)\to\bot,
$$

ここで $\mathcal H$ は、正値性・互いに素性・5 非可除性・黄金 norm・zero-sector 積等式・座標の primitive 性・十乗分解をまとめた仮定群である。

したがって数学的には

$$
\neg\exists r,s,a,b,c,d
$$

で、列挙された全条件を同時に満たす zero-sector 算術データは存在しない、という公開インターフェースに相当する。

## 数学的主張

0400 の仮定を順に読むと、対象となる zero-sector データの構造が明瞭になる。

まず

$$
a>0,\qquad b>0,\qquad \gcd(a,b)=1,\qquad 5\nmid b
$$

を要求する。

次に黄金 norm が符号を除いて $b$ であることを要求する。

$$
N(r,s)=b
\quad\text{または}\quad
N(r,s)=-b,
$$

ここでコード上の `goldenNorm ⟨r,s⟩` が $N(r,s)$ に対応する。

さらに第二座標側の第五冪因子分解から得られる signed product

$$
s\,H(r,s)=-5^6 a^{10}
$$

を仮定する。ここで

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s)
$$

である。

座標自体にも primitive 条件

$$
\gcd(|r|,|s|)=1
$$

を課す。

最後に primitive 分離済みの十乗構造として、ある $c,d\in\mathbb N$ が存在し

$$
|s|=5^6 c^{10},
$$

$$
|H(r,s)|=d^{10}
$$

となることを要求する。

0400 が表す主張は、これらの条件をすべて同時に満たす組は存在しない、である。

重要なのは、0400 自身はこの排除を証明していない点である。`abbrev` は単に **「何を証明すれば zero-sector 算術を閉じたことになるか」** を命題として命名している。

## 証明全体での役割

0399 までの descent 層は、内部表現として `GoldenZeroSectorCandidate` と `GoldenZeroSectorDescentPacket` を用いていた。

一方、上流の signed-golden sector 側が自然に持つデータは、構造体ではなく個別の等式・可除性・coprimality である。

0400 はこの二つの層の間にある **公開 receiver contract** である。

概略は

$$
\text{raw zero-sector arithmetic}
\longrightarrow
\texttt{GoldenZeroSectorArithmeticExclusion}
\longrightarrow
\text{zero-sector exclusion}
\longrightarrow
\text{unit-sector closure}
$$

となる。

これにより後続コードは、descent の内部構造を知る必要がなくなる。必要なのは `GoldenZeroSectorArithmeticExclusion` という `Prop` を一つ供給することだけである。

これは証明アーキテクチャ上の境界として重要である。無限降下の詳細を downstream receiver から隠し、算術的前提と最終的な `False` だけを公開している。

## 0399 との対応

0400 の仮定は `GoldenZeroSectorCandidate` の field とほぼ一対一に対応する。

`GoldenZeroSectorCandidate` 側では、概略

```lean
r : ℤ
s : ℤ
a : ℕ
b : ℕ
c : ℕ
d : ℕ
a_pos : 0 < a
b_pos : 0 < b
coprime_a_b : Nat.Coprime a b
five_not_dvd_b : ¬ 5 ∣ b
norm_eq_or_eq_neg : ...
product_eq : ...
coprime_coords : ...
s_natAbs_eq : ...
H_natAbs_eq : ...
```

という形で保持されている。

0400 では `c,d` だけを existential にまとめ、その他を引数・仮定として直接受け取る。

したがって 0400 は candidate structure の **論理的な非構造化版** とみなせる。

0399 が

$$
\mathrm{GoldenZeroSectorCandidate}\to\bot
$$

であったのに対し、0400 は

$$
\text{candidate を構成する raw hypotheses}\to\bot
$$

という公開型を定義する。

## 直接依存する定義・補題

0400 は `abbrev` なので証明補題を呼び出さない。型の形成に直接必要なのは主に次である。

- `GoldenInt` の pair 表現 `⟨r, s⟩`
- `goldenNorm`
- `goldenFifthSndFactor`
- `Nat.Coprime`
- `Int.natAbs`
- 自然数・整数の冪、可除性、順序、存在量化

0399 `goldenZeroSectorCandidate_false` は 0400 の型定義そのものには直接現れない。ただし意味上は、後続でこの raw contract を証明するための核心的な排除定理である。

また `GoldenZeroSectorCandidate` も 0400 の Lean 型には現れない。これは意図的な抽象化境界である。

## 構築・利用の流れ

`abbrev` 自体には proof body がないため、「証明の流れ」ではなく「この命題をどう利用するか」を読むのが適切である。

1. 上流から `r s : ℤ` と `a b : ℕ` を受け取る。
2. $a,b$ の正値性を供給する。
3. $\gcd(a,b)=1$ を供給する。
4. $5\nmid b$ を供給する。
5. `goldenNorm ⟨r,s⟩ = ±b` を供給する。
6. signed product

   $$
   sH(r,s)=-5^6a^{10}
   $$

   を供給する。
7. 座標の primitive 性 $\gcd(|r|,|s|)=1$ を供給する。
8. $|s|$ と $|H|$ の十乗分解 witness `c d` を供給する。
9. これらすべてを受け取る `GoldenZeroSectorArithmeticExclusion` の実装が `False` を返す。

次の 0401 `signedGoldenZeroSectorExclusion_of_arithmetic` は、まさにこの contract を `SignedGoldenZeroSectorExclusion` に接続する。

## Lean 固有の処理

### `abbrev` と `def` の違い

ここでは `def` ではなく `abbrev` が使われている。

`abbrev` は elaboration / reduction で比較的透過的に展開される略記であり、後続 theorem がこの長い `∀ ... → False` 型を扱う際に、追加の unfold 負担を抑えやすい。

この用途では、新しい数学的対象を不透明な定義として作るというより、長い proposition に名前を与えることが目的なので `abbrev` は自然である。

### `Prop` としての receiver contract

構造体ではなく `Prop` なので、0400 はデータを保存する packet ではない。

これは

```lean
hArithmetic : GoldenZeroSectorArithmeticExclusion
```

という一つの仮定を後続 theorem に渡すための interface である。

### `→` の右結合

Lean では

```lean
A → B → C → False
```

は

```lean
A → (B → (C → False))
```

と右結合する。

したがって、この contract を使用する側は各仮定を順番に関数適用して最終的な `False` を得られる。

### `∃ c d` だけを末尾で束ねる設計

`c,d` は十乗分解の witness なので、外部 receiver に固定値として要求するより、存在証明として末尾に渡す設計になっている。

これは upstream の `zeroSector_tenthPower_split` のような existential theorem をそのまま接続しやすい。

## 冗長・重複箇所

0400 の仮定列は `GoldenZeroSectorCandidate` の field とかなり重複している。

これはコード重複ではあるが、アーキテクチャ上は意図があると読める。公開 contract に内部 structure 型を露出させず、必要な数学的条件だけを平坦な proposition として公開できるからである。

一方、保守性の観点では、candidate の field が変更された際に 0400 との同期が必要になる可能性がある。

特に以下は明確に重複する。

- `a_pos`
- `b_pos`
- `coprime_a_b`
- `five_not_dvd_b`
- `norm_eq_or_eq_neg`
- `product_eq`
- `coprime_coords`
- `s_natAbs_eq`
- `H_natAbs_eq`

ただし最後の二つは 0400 では `∃ c d` の内部へまとめられている。

## 最適化候補

### 1. raw contract と candidate constructor の対応を helper 化

0400 の仮定を受けて `GoldenZeroSectorCandidate` を作る theorem / def を一箇所に固定すると、後続の算術排除証明がより短くなる。

すでに repository には `goldenZeroSectorCandidate_of_raw` があり、この方向の constructor API が存在する。したがって公開 contract → candidate → 0399 という橋を明示する設計は自然である。

### 2. 十乗 split を専用 structure にする案

```lean
structure GoldenZeroSectorTenthSplit where
  c d : ℕ
  s_eq : s.natAbs = 5 ^ 6 * c ^ 10
  H_eq : ... = d ^ 10
```

のように witness を束ねれば、長い existential conjunction を再利用しやすくなる。

ただし現状の `∃ c d, ... ∧ ...` は theorem 接続に素直であり、単独用途なら現在の方が軽い。

### 3. norm の符号を専用 predicate にまとめる案

```lean
goldenNorm gamma = b ∨ goldenNorm gamma = -b
```

は複数箇所で現れるため、将来再利用が増えるなら

```lean
SignedNormAbs gamma b
```

のような predicate へ抽象化できる。

ただし名称を増やすことで数式との直接対応が見えにくくなるため、監査用途では現状の明示形にも利点がある。

### 4. `abbrev` 維持が妥当

この宣言は computation を隠す目的ではなく長い proposition の可読性を上げる目的なので、`def` へ変更する明確な利点は見当たらない。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は現在

```lean
import Mathlib
```

を使用している。

0400 自身は tactic を一切使用しない。必要なのは型形成に関わる次の機能である。

- `Nat.Coprime`
- 整数 `ℤ`
- `Int.natAbs`
- 可除性 `∣`
- 冪 `^`
- 順序 `<`
- `goldenNorm` と `goldenFifthSndFactor` を提供する local module

したがって source module の import 最適化では、0400 自身のために `Mathlib` 全体を要求する必要はない可能性が高い。

しかし正確な最小 Mathlib module 集合は、実際に import を縮小して Lean build しなければ保証できない。今回は Lean build を行わない条件なので、具体的な最小 import 名は未確認である。

## Comparator challenge 化の可否

**可能。ただし 0400 単体は「証明」ではなく型設計 challenge になる。**

単独で challenge 化するなら、長い zero-sector 条件を正確な `Prop` interface として再構成できるかを見る問題になる。

例えば skeleton として

```lean
abbrev ZeroSectorArithmeticExclusion : Prop :=
  ∀ (r s : ℤ) (a b : ℕ),
    ... →
    False
```

を与え、各条件の型、cast、`natAbs`、existential split を正確に埋めさせる形式が考えられる。

ただし proof-search 能力の比較には弱い。

Comparator 用としてより有益なのは、0400 と次の receiver theorem、さらに 0399 への bridge を一体化し、

$$
\text{raw hypotheses}
\to
\text{candidate construction}
\to
\text{descent contradiction}
$$

を実装させる challenge である。その場合、structure construction、existential elimination、整数/自然数 cast、既証明 API の合成まで評価できる。

## 次に読むべき宣言

次は **0401 `signedGoldenZeroSectorExclusion_of_arithmetic`**、種別は `theorem` である。

正本では 0400 の直後に続き、概略

```lean
theorem signedGoldenZeroSectorExclusion_of_arithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    SignedGoldenZeroSectorExclusion := by
  ...
```

という型を持つ。

0400 が raw arithmetic を `Prop` として公開したのに対し、0401 はその proposition を実際の `SignedGoldenRamifierStrippedPacket` と zero-sector fifth-power equation から呼び出す receiver bridge である。

したがって依存順では

$$
\text{0399 candidate contradiction}
\longrightarrow
\text{0400 public arithmetic contract}
\longrightarrow
\text{0401 zero-sector receiver bridge}
$$

と進む。