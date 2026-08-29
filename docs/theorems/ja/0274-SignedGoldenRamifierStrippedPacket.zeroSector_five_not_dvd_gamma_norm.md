# 0274 — `SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_gamma_norm`

## 宣言種別

これは **`theorem`** である。

`SignedGoldenZeroSector.lean` に置かれた zero-sector 専用の特殊化補題であり、一般の unit-times-fifth-power 表現に対して既に得られている `SignedGoldenRamifierStrippedPacket.five_not_dvd_gamma_norm` を、unit factor が `1` である pure fifth-power case に移す。

## Lean の型

```lean
/-- In the zero sector the base norm is not divisible by five. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_gamma_norm
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    ¬ (5 : ℤ) ∣ goldenNorm gamma := by
  apply p.five_not_dvd_gamma_norm goldenUnit_one
  rw [hbeta]
  ext <;> simp [goldenOne, goldenMul]
```

型を数学的に読むと、packet の `beta` が pure fifth power

$$
\beta=\gamma^5
$$

であるなら、`gamma` の golden norm は 5 で割れない、すなわち

$$
5\nmid N(\gamma)
$$

という主張である。

ここで `goldenNorm gamma` は整数値なので、Lean の結論も

```lean
¬ (5 : ℤ) ∣ goldenNorm gamma
```

と整数の可除性として表現される。

## 数学的主張の意味

一般の unit-times-fifth-power layer では

$$
\beta=\epsilon\gamma^5,
\qquad \epsilon\in\mathcal O^\times
$$

という表現から、`gamma` の norm が packet の power-split base `b` と符号を除いて一致することが既に証明されている。さらに packet は

$$
5\nmid b
$$

を保持しているため、一般 theorem

```lean
SignedGoldenRamifierStrippedPacket.five_not_dvd_gamma_norm
```

は

$$
5\nmid N(\gamma)
$$

を結論する。

zero sector では unit representative が

$$
\varphi^0=1
$$

であり、仮定は単に

$$
\beta=\gamma^5
$$

となる。本 theorem はこれを

$$
\beta=1\cdot\gamma^5
$$

と読み替え、一般 theorem に `goldenOne` を unit として渡している。

したがって、この theorem 自身が新しい five-adic arithmetic を証明しているわけではない。一般 layer にある「fifth-power base の norm は 5-adic unit である」という情報を zero-sector API へ運ぶ **specialization bridge** である。

## 証明全体での役割

0273 `zeroSector_gamma_norm_eq_or_eq_neg` は zero sector において

$$
N(\gamma)=b
\qquad\text{または}\qquad
N(\gamma)=-b
$$

という norm の値そのものを packet data に接続した。

0274 は同じ zero-sector base `gamma` に対して、その norm が 5 を因子に持たないこと

$$
5\nmid N(\gamma)
$$

を明示的な API として供給する。

この非可除性は後段の `SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_sndFactor` で直接利用される。そこでは仮に

$$
5\mid H(\gamma)
$$

とし、`five_dvd_goldenFifthSndFactor_sub_norm_sq` から得られる congruence 情報を組み合わせて

$$
5\mid N(\gamma)^2
$$

を作り、5 が素数であることから

$$
5\mid N(\gamma)
$$

を導く。最後に本 theorem と衝突させて仮定を排除する。

したがって 0274 は、zero-sector coordinate arithmetic に対する **5-adic exclusion boundary** を提供する theorem と見なせる。

## 直接依存する定義・補題

### `SignedGoldenRamifierStrippedPacket.five_not_dvd_gamma_norm`

本 theorem の実質的な数学内容をすべて担う一般 theorem である。

```lean
theorem SignedGoldenRamifierStrippedPacket.five_not_dvd_gamma_norm
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {epsilon gamma : GoldenInt} (hepsilon : GoldenUnit epsilon)
    (hbeta : p.beta = goldenMul epsilon (goldenPow gamma 5)) :
    ¬ (5 : ℤ) ∣ goldenNorm gamma := by
  ...
```

正本 source ではこの一般 theorem は、仮に `5 ∣ goldenNorm gamma` と置き、`p.gamma_norm_eq_or_eq_neg hepsilon hbeta` により

$$
N(\gamma)=b
\quad\text{または}\quad
N(\gamma)=-b
$$

へ分岐し、どちらの場合も packet field

```lean
p.five_not_dvd_b : ¬ 5 ∣ p.exceptional.powerSplit.b
```

に反することを示している。

0274 はこの一般 argument を再証明しない。

### `goldenUnit_one`

`goldenOne` が `GoldenUnit` であることを供給する theorem である。

```lean
apply p.five_not_dvd_gamma_norm goldenUnit_one
```

によって、一般 theorem の unit parameter `epsilon` を `goldenOne` に固定する。

### `goldenOne`

Golden integer ring の project-side 乗法単位元である。本 theorem の zero-sector 仮定を一般 theorem が要求する `unit × fifth power` の形へ埋め込むために使われる。

### `goldenMul`, `goldenPow`

一般 theorem は

```lean
p.beta = goldenMul epsilon (goldenPow gamma 5)
```

を要求する一方、zero-sector 仮定 `hbeta` は

```lean
p.beta = goldenPow gamma 5
```

である。`goldenMul goldenOne (...)` と pure fifth power の差を証明末尾で埋める。

### `goldenNorm`

結論の対象となる `GoldenInt` の norm。本 theorem 自身では定義展開も計算もせず、その arithmetic は一般 theorem に委譲される。

## 証明の流れ

### 1. 一般 theorem を unit `1` に特殊化する

```lean
apply p.five_not_dvd_gamma_norm goldenUnit_one
```

この時点で最終結論

```lean
¬ (5 : ℤ) ∣ goldenNorm gamma
```

の証明は一般 theorem 側へ移り、残る goal は factorization hypothesis の整合だけになる。

概念的には

$$
\beta=\gamma^5
\Longrightarrow
\beta=1\cdot\gamma^5
$$

を示せばよい。

### 2. `hbeta` で `p.beta` を pure fifth power に rewrite する

```lean
rw [hbeta]
```

一般 theorem が要求する左辺 `p.beta` が `goldenPow gamma 5` に置換され、goal は unit law に縮退する。

### 3. `GoldenInt` の座標等式として閉じる

```lean
ext <;> simp [goldenOne, goldenMul]
```

`ext` で `GoldenInt` の等式を座標ごとに分解し、`goldenOne` と `goldenMul` の concrete representation を `simp` に渡して両 goal を閉じる。

この 3 行の proof には norm 計算も可除性計算も現れない。それらはすべて一般 theorem に encapsulate されている。

## Lean 固有の処理

### namespace theorem を method のように適用

```lean
p.five_not_dvd_gamma_norm
```

という dot notation により、`SignedGoldenRamifierStrippedPacket.five_not_dvd_gamma_norm` の packet 引数 `p` を暗黙に先頭へ供給している。

### implicit unit parameter の推論

```lean
apply p.five_not_dvd_gamma_norm goldenUnit_one
```

では `goldenUnit_one` の型から一般 theorem の implicit `epsilon` が `goldenOne` と推論される。

### `rw [hbeta]` の向き

`p.beta` を `goldenPow gamma 5` へ置き換える向きを採用している。これにより残りが「pure fifth power と `1 × pure fifth power` が等しい」という単純な representation goal になる。

### `ext <;> simp`

`GoldenInt` の乗法単位元則を抽象 ring lemma で処理する代わりに、構造体の各座標へ落とし、project-side definitions を concrete に simplification している。

`<;>` は `ext` が生成した全 subgoal に同じ `simp` を適用するための tactic combinator である。

## 冗長・重複箇所

proof 自体は 3 行しかなく、局所的な冗長性はほぼない。

ただし直前の 0273 `zeroSector_gamma_norm_eq_or_eq_neg` もまったく同じ adaptation tail

```lean
rw [hbeta]
ext <;> simp [goldenOne, goldenMul]
```

を持っている。

つまり両 theorem は

$$
\beta=\gamma^5
\Rightarrow
\beta=1\cdot\gamma^5
$$

という representation alignment を個別に再構築している。

今後同じ形の zero-sector specialization が増えるなら、この部分は helper lemma として抽出できる。ただし現状では 2 行の重複に過ぎず、helper を追加することで navigation cost が増す可能性もあるため、最適化優先度は低い。

## 最適化候補

### 1. zero-sector factorization helper

例えば概念上

```lean
lemma zeroSector_eq_one_mul_fifth
    {beta gamma : GoldenInt}
    (h : beta = goldenPow gamma 5) :
    beta = goldenMul goldenOne (goldenPow gamma 5) := by
  ...
```

のような helper を用意すれば、0273・0274 などの specialization theorem は一般 theorem の適用だけに集中できる。

ただし実際にこの helper を導入する価値があるかは、同型 proof の出現数を source 全体で数えた上で判断するのがよい。

### 2. 抽象的な単位元則で閉じる

`goldenMul` と `GoldenInt` の ring multiplication の接続 API が十分安定しているなら、座標 `ext` をせず `one_mul` 系の lemma で

```lean
simpa [...] using hbeta
```

のように閉じられる可能性がある。

ただし具体的にどの rewrite lemma が現在の import graph で利用可能かは、本実行では Lean build を行っていないため **未確認** である。

### 3. 0273 と 0274 の paired API を維持する

数学的には 0273 の

$$
N(\gamma)=\pm b
$$

と packet field `5 ∤ b` から 0274 を短く導く別 proof も書ける。しかし現行実装は既存の一般 theorem `five_not_dvd_gamma_norm` を直接 reuse しており、dependency duplication を避けるという意味では現在の形の方が良い。

## 必要 Mathlib import と import 最適化候補

対象ブランチの standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem 自身が直接使う証明機構は `apply`, `rw`, structure extensionality, `simp` と既存 project theorem であり、個別の高度な Mathlib 数論 theoremを直接呼んでいない。

一方、一般 theorem `five_not_dvd_gamma_norm` の内部では整数可除性、符号、coercion などを利用しており、さらにそれより前段の golden arithmetic / packet API に依存する。

standalone artifact は生成時に source modules を結合しているため、元 `SignedGoldenZeroSector.lean` の正確な最小 import 集合をこの一ファイルだけから断定することはできない。本実行では Lean build もしないため、`import Mathlib` をどの個別 Mathlib modules へ縮小できるかは **未確認** とする。

import 最適化を行う場合は、少なくとも

- `SignedGoldenRamifierStrippedPacket.five_not_dvd_gamma_norm` を供給する前段 module
- golden unit API (`goldenUnit_one`, `goldenOne`)
- `GoldenInt` arithmetic (`goldenMul`, `goldenPow`, `goldenNorm`)

の project import graph を確認し、最後に Lean build で検証すべきである。

## Comparator challenge 化の可否

**可能。ただし難度は低い。**

良い challenge は、一般 theorem

```lean
p.five_not_dvd_gamma_norm
```

と unit proof

```lean
goldenUnit_one
```

を利用可能にした状態で、

```lean
hbeta : p.beta = goldenPow gamma 5
```

から zero-sector theorem を証明させる形である。

評価点は次の三点になる。

1. 一般の five-adic theorem を再証明せず reuse できるか。
2. zero sector の unit として `goldenOne` / `goldenUnit_one` を選択できるか。
3. `p.beta = gamma^5` と `p.beta = 1 * gamma^5` の representation mismatch を `rw`, `ext`, `simp` で解消できるか。

数論の核心そのものより、**API specialization / representation alignment challenge** として適している。

## PDF との対応

対象ブランチには

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

しかし GitHub コネクタは PDF binary 本文を直接返さず、今回 public raw PDF の取得も成功しなかった。TeX source も branch 上では zip archive としてのみ格納されており、この経路では本文照合を行えなかった。

したがって、本 theorem に対応する PDF の具体的ページ番号・節番号・文言は **未確認** であり、推測しない。本稿の技術的説明は、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された generated Lean source と既存 theorem API を直接根拠としている。

## 次に読むべき宣言

Lean 正本で 0274 の直後に置かれている次の宣言は 0275

```lean
/-- Exact signed second-coordinate equation in the zero sector. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_snd_factor_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd =
      -(5 : ℤ) ^ 6 * (p.exceptional.powerSplit.a : ℤ) ^ 10 := by
  ...
```

である。

0274 が norm 側に

$$
5\nmid N(\gamma)
$$

という exclusion を与えるのに対し、0275 は `gamma^5` の第二座標から exact signed product equation を抽出し、zero-sector coordinate arithmetic を具体化する。
