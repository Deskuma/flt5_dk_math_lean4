# 0273 — `SignedGoldenRamifierStrippedPacket.zeroSector_gamma_norm_eq_or_eq_neg`

## 宣言種別

これは **`theorem`** である。

`SignedGoldenZeroSector.lean` の入口に置かれた zero-sector 専用補題であり、一般の unit-times-fifth-power 表現に対して既に証明されている `SignedGoldenRamifierStrippedPacket.gamma_norm_eq_or_eq_neg` を、unit factor が `1` である pure fifth-power case へ特殊化する。

## Lean の型

```lean
/-- The zero-sector base has norm equal to the packet base up to sign. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_gamma_norm_eq_or_eq_neg
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    goldenNorm gamma = (p.exceptional.powerSplit.b : ℤ) ∨
      goldenNorm gamma = -(p.exceptional.powerSplit.b : ℤ) := by
  apply p.gamma_norm_eq_or_eq_neg goldenUnit_one
  rw [hbeta]
  ext <;> simp [goldenOne, goldenMul]
```

型を数学的に読むと、packet の `beta` が pure fifth power

$$
\beta=\gamma^5
$$

であるなら、`gamma` の golden norm は packet が保持する自然数 `b` の整数 coercion に対して

$$
N(\gamma)=b
\qquad\text{または}\qquad
N(\gamma)=-b
$$

となる、という主張である。

ここで

$$
b:=p.exceptional.powerSplit.b.
$$

## 数学的主張の意味

一般の factorization layer では packet の `beta` が

$$
\beta=\epsilon\gamma^5
$$

と表され、`epsilon` が golden unit であるとき、unit の norm が $\pm1$ であることを通じて `gamma` の norm が `b` と符号を除いて一致することが既に証明されている。

zero sector では unit representative が

$$
\varphi^0=1
$$

なので、仮定は単に

$$
\beta=\gamma^5
$$

となる。本 theorem はこれを

$$
\beta=1\cdot\gamma^5
$$

という一般 theorem が要求する形へ戻し、unit として `goldenOne` を与えるだけである。

したがって、新しい norm arithmetic を証明しているのではない。一般 theorem の情報を zero-sector API に持ち込む **specialization bridge** である。

## 証明全体での役割

0272 までは unit class を有限 sector に分け、nonzero sectors を排除し、zero sector を別系統の arithmetic に渡すところまで進んだ。

0273 から始まる `SignedGoldenZeroSector.lean` は、その残った sector $0$、すなわち

$$
\beta=\gamma^5
$$

を解析する。

zero-sector descent では `gamma` の二座標と norm の両方を packet の five-adic / power-split データに結び付ける必要がある。本 theorem はそのうち norm 側の最初の橋であり、後続 theorem が素因子 `q` の可除性を `gamma` の座標から `b` へ移す際にも直接使われる。

正本 standalone source では後段で

```lean
rcases p.zeroSector_gamma_norm_eq_or_eq_neg hbeta with hn | hn
```

と本 theorem を分岐消費し、`q ∣ goldenNorm gamma` から `q ∣ p.exceptional.powerSplit.b` を導いている。

## 直接依存する定義・補題

### `SignedGoldenRamifierStrippedPacket.gamma_norm_eq_or_eq_neg`

本 theorem の本体となる一般 theorem である。

```lean
theorem SignedGoldenRamifierStrippedPacket.gamma_norm_eq_or_eq_neg
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {epsilon gamma : GoldenInt} (hepsilon : GoldenUnit epsilon)
    (hbeta : p.beta = goldenMul epsilon (goldenPow gamma 5)) :
    goldenNorm gamma = (p.exceptional.powerSplit.b : ℤ) ∨
      goldenNorm gamma = -(p.exceptional.powerSplit.b : ℤ) := by
  ...
```

0273 はこの theorem に `epsilon := goldenOne` を与える specialization である。

### `goldenUnit_one`

`goldenOne` が `GoldenUnit` であることを与える theorem。

```lean
theorem goldenUnit_one : GoldenUnit goldenOne := by
  apply goldenUnit_of_norm_eq_one
  norm_num [goldenNorm, goldenOne]
```

本 proof の

```lean
apply p.gamma_norm_eq_or_eq_neg goldenUnit_one
```

で直接使われる。

### `goldenOne`

Golden integer ring における乗法単位元の project-side concrete representation である。証明末尾では `simp [goldenOne, goldenMul]` により、その座標表示まで展開される。

### `goldenMul`, `goldenPow`

project-side の golden multiplication / power API。本 theorem の入力 `hbeta` は

```lean
p.beta = goldenPow gamma 5
```

だが、一般 theorem は

```lean
p.beta = goldenMul goldenOne (goldenPow gamma 5)
```

という形を要求する。その差を最後の extensionality proof で埋める。

### `goldenNorm`

`GoldenInt` の norm。結論の主語であるが、本 theorem 自身では定義展開しない。norm arithmetic は一般 theorem に完全に委譲される。

## 証明の流れ

### 1. 一般 norm theorem を適用

```lean
apply p.gamma_norm_eq_or_eq_neg goldenUnit_one
```

これにより goal は、zero-sector 仮定を一般 theorem の factorization hypothesis に変換することだけになる。

概念的には

$$
\beta=\gamma^5
\Longrightarrow
\beta=1\cdot\gamma^5
$$

を示せばよい。

### 2. `hbeta` で packet の `beta` を rewrite

```lean
rw [hbeta]
```

goal の左辺 `p.beta` を `goldenPow gamma 5` へ置き換える。

残るのは、概ね

$$
\gamma^5=1\cdot\gamma^5
$$

という単位元則である。

### 3. GoldenInt の座標等式へ落とす

```lean
ext <;> simp [goldenOne, goldenMul]
```

`GoldenInt` の等式を各座標の等式へ分解し、`goldenOne` と `goldenMul` を展開して `simp` で閉じる。

この時点では norm そのものの計算は一切していない。

## Lean 固有の処理

### `apply` による specialization

```lean
apply p.gamma_norm_eq_or_eq_neg goldenUnit_one
```

は namespace theorem を packet `p` の method のように利用している。implicit parameter `epsilon` は、与えた unit proof `goldenUnit_one` から `goldenOne` と推論される。

### rewrite の向き

`rw [hbeta]` は `p.beta` を pure fifth power に置換する。ここで `← hbeta` を使うのではない。一般 theorem が要求する右辺との比較を簡単な単位元等式へするため、この向きが自然である。

### `ext`

`GoldenInt` の等式をその構造成分へ分解する。ring-level `one_mul` を直接使わず、project-side concrete coordinate representation を通して closure している。

### `<;>`

`ext` が生成した全座標 goal に同一の

```lean
simp [goldenOne, goldenMul]
```

を適用する。

## 冗長・重複箇所

証明は 3 行であり、大きな冗長性はない。

ただし、数学的には最後の

```lean
ext <;> simp [goldenOne, goldenMul]
```

は「`goldenOne` が `goldenMul` の左単位元」という事実を座標レベルで毎回再構成している。

もし project API に

```lean
goldenMul_one_left : goldenMul goldenOne x = x
```

または `goldenOne = 1` / `goldenMul = (*)` を安定して rewrite できる lemma があれば、より意味論的な proof にできる可能性がある。

一方、現行 proof は standalone artifact 内で確実に閉じる concrete proof であり、局所的には十分簡潔である。

## 最適化候補

### 1. 単位元 API の利用

可能なら概念的に

```lean
simpa [golden_mul_eq] using hbeta
```

あるいは `one_mul` を使う形へ短縮できる可能性がある。

ただし、実際にどの rewrite lemma が現行 source/import で利用可能かは Lean build を行っていないため未確認である。

### 2. zero-sector specialization 群の共通化

直後の `zeroSector_five_not_dvd_gamma_norm` も同じパターンで

```lean
apply p.five_not_dvd_gamma_norm goldenUnit_one
rw [hbeta]
ext <;> simp [goldenOne, goldenMul]
```

と証明されている。

したがって

$$
\beta=\gamma^5
\Rightarrow
\beta=1\cdot\gamma^5
$$

を作る helper lemma を一つ用意すれば、zero-sector specialization theorem 群の重複を減らせる。

ただし 2–3 行の proof を抽象化することで navigation cost が増える可能性もあり、優先度は低い。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem が直接利用する Lean 機能は主として構造体 extensionality、rewrite、simp、および既存 project theorem である。重い独自 Mathlib theorem を本 theorem 自身が直接呼んでいるわけではない。

元生成 module `SignedGoldenZeroSector.lean` の正確な最小 import 集合は、この repository の standalone artifact だけからは断定できない。さらに本実行では Lean build を行わないため、`import Mathlib` をどの個別 module 群へ縮小できるかは **未確認** である。

import 最適化を行うなら、まず直接依存する project modules

- `SignedGoldenFifthPower` / norm bridge を供給する module
- `SignedGoldenRamifierStripped`
- golden unit / arithmetic definitions

の import graph を元 `Deskuma/dkmath` 側で確認し、その後 Lean build で検証すべきである。

## Comparator challenge 化の可否

**可能。ただし難度は低い。**

challenge としては、一般 theorem

```lean
p.gamma_norm_eq_or_eq_neg
```

と

```lean
goldenUnit_one
```

を与えた上で、仮定

```lean
hbeta : p.beta = goldenPow gamma 5
```

から一般 theorem が要求する

```lean
p.beta = goldenMul goldenOne (goldenPow gamma 5)
```

を構成させる問題にできる。

評価点は

1. 一般 theorem を再証明せず再利用できるか。
2. unit argument として `goldenUnit_one` を選べるか。
3. `GoldenInt` 等式を `ext` と `simp` で閉じられるか。

となる。

高度な数論 challenge というより、**API specialization / representation alignment challenge** として適している。

## PDF との対応

対象ブランチには

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

ただし GitHub コネクタは PDF binary 本文を直接返せず、今回 public raw PDF の取得も成功しなかったため、本 theorem に対応する PDF の具体的ページ番号・節番号・文言は確認できていない。したがって PDF との具体的対応については推測しない。

本稿の技術的説明は、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された generated source と既存 theorem API を直接根拠としている。

## 次に読むべき宣言

次は 0274

```lean
theorem SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_gamma_norm
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    ¬ (5 : ℤ) ∣ goldenNorm gamma := by
  apply p.five_not_dvd_gamma_norm goldenUnit_one
  rw [hbeta]
  ext <;> simp [goldenOne, goldenMul]
```

を読むべきである。

0273 が zero-sector base norm の **大きさを `b` に固定する theorem** なら、0274 はその norm に **5 が入らないこと** を zero sector へ特殊化する theorem である。

この二つを揃えることで、後続の座標可除性・coprimality argument が `gamma` の norm と packet の power-split data を同時に利用できるようになる。
