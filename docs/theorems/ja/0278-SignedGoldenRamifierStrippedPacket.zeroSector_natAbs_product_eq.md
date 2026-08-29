# 0278 — `SignedGoldenRamifierStrippedPacket.zeroSector_natAbs_product_eq`

## 宣言種別

これは **`theorem`** である。

`SignedGoldenRamifierStrippedPacket` の zero sector で得られた符号付き整数の積等式を、`Int.natAbs` によって自然数の絶対値積等式へ移す補題である。

## Lean の型

```lean
/-- Natural absolute-value form of the zero-sector product equation. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_natAbs_product_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    gamma.snd.natAbs *
        (goldenFifthSndFactor gamma.fst gamma.snd).natAbs =
      5 ^ 6 * p.exceptional.powerSplit.a ^ 10 := by
  have h := congrArg Int.natAbs (p.zeroSector_snd_factor_eq hbeta)
  simpa [Int.natAbs_mul, pow_succ] using h
```

`gamma = (r,s)` とし、

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s),
\qquad
a=p.\operatorname{exceptional}.\operatorname{powerSplit}.a
$$

と書けば、主張は

$$
\beta=\gamma^5
\quad\Longrightarrow\quad
|s|\,|H(r,s)|=5^6a^{10}
$$

である。ここで Lean の `Int.natAbs` は整数の絶対値を自然数として返すため、左辺・右辺とも `ℕ` の等式になっている。

## 数学的主張の意味

直前の 0275 `zeroSector_snd_factor_eq` は、zero sector の第二座標から exact signed equation

$$
s\,H(r,s)=-5^6a^{10}
$$

を与える。

本 theorem はこの等式の両辺に絶対値を取り、

$$
|sH(r,s)|=|-5^6a^{10}|
$$

から

$$
|s|\,|H(r,s)|=5^6a^{10}
$$

を得る。

数学的には非常に素朴な変換だが、証明全体では重要な型境界である。0275 までは符号を持つ `ℤ` 上の equation を扱っていたが、本 theorem 以降は素因数分解・互いに素性・冪分解を `ℕ` の API で進められる。

したがって 0278 は、**signed coordinate arithmetic から natural-number factorization への橋** と見るのが最も適切である。

## 証明全体での役割

zero-sector descent では最終的に

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}
$$

という tenth-power split を得たい。

そのためにはまず積全体を

$$
|s|\,|H|=5^6a^{10}
$$

という自然数の積として持つ必要がある。本 theorem がその入力を供給する。

正本 source の直後の `zeroSector_coprime_coords` では、本 theorem を

```lean
have hprod := p.zeroSector_natAbs_product_eq hbeta
```

として直接取得し、共通素因子 `q` が `gamma.snd.natAbs` を割ることから

$$
q\mid 5^6a^{10}
$$

を導くために使う。

さらに後続 `zeroSector_tenthPower_split` でも再び

```lean
have hprod : gamma.snd.natAbs * H =
    5 ^ 6 * p.exceptional.powerSplit.a ^ 10 := by
  simpa [H] using p.zeroSector_natAbs_product_eq hbeta
```

と直接再利用される。そこで 0277 の $5\nmid H$ と coprimality を組み合わせ、$5^6$ を `|s|` 側へ強制した後、残りを互いに素な tenth powers へ分解する。

つまり依存の流れは概略

$$
\text{0275: }sH=-5^6a^{10}
\longrightarrow
\text{0278: }|s||H|=5^6a^{10}
\longrightarrow
\text{coprimality / 5-adic separation}
\longrightarrow
|s|=5^6c^{10},\ |H|=d^{10}
$$

となる。

## 直接依存する定義・補題

### `SignedGoldenRamifierStrippedPacket`

signed golden exceptional branch から得られる packet 構造。本 theorem では packet の内部 field を展開せず、0275 の packet-level theorem を利用する。

### `GoldenInt`

golden order の元を二整数座標で持つ型。`gamma.snd` が visible second coordinate であり、`gamma.fst`, `gamma.snd` が quartic factor の入力になる。

### `goldenPow`

`GoldenInt` 上の冪。仮定

```lean
hbeta : p.beta = goldenPow gamma 5
```

が zero sector、すなわち unit sector 0 の fifth-power representation を表す。

### `goldenFifthSndFactor`

fifth power の第二座標を因数分解したときに現れる quartic polynomial である。座標を `(r,s)` とすると

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4.
$$

### 0275 `SignedGoldenRamifierStrippedPacket.zeroSector_snd_factor_eq`

本 theorem の唯一の project-level 実質依存である。型は

```lean
gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd =
  -(5 : ℤ) ^ 6 * (p.exceptional.powerSplit.a : ℤ) ^ 10
```

であり、本 theorem はこの equality に `Int.natAbs` を作用させる。

### `congrArg`

等しい二項に同じ関数を作用させる標準原理。本 theorem では

```lean
congrArg Int.natAbs (...)
```

により signed equation の両辺へ `natAbs` を適用する。

### `Int.natAbs_mul`

整数積の自然数絶対値について

$$
|xy|_{\mathbb N}=|x|_{\mathbb N}|y|_{\mathbb N}
$$

を与える。

### `pow_succ`

冪の successor 展開を行う標準補題。本 proof では右辺の負号・積・冪に対して `simp` が期待する正規形を作るために使用される。

## 証明の流れ

### 1. 0275 の signed equation を取得する

```lean
p.zeroSector_snd_factor_eq hbeta
```

から

$$
sH=-5^6a^{10}
$$

を得る。

### 2. 等式の両辺へ `Int.natAbs` を作用させる

```lean
have h := congrArg Int.natAbs (p.zeroSector_snd_factor_eq hbeta)
```

これにより Lean 上では概念的に

```lean
Int.natAbs (gamma.snd * H) =
  Int.natAbs (-(5 : ℤ) ^ 6 * (a : ℤ) ^ 10)
```

という `ℕ` の equality が得られる。

### 3. `simp` で absolute value を積へ分配する

```lean
simpa [Int.natAbs_mul, pow_succ] using h
```

`Int.natAbs_mul` が左辺を

```lean
gamma.snd.natAbs * H.natAbs
```

へ分解する。

右辺では、5 と `a` が自然数由来の非負整数であり、負号は absolute value で消える。その結果

```lean
5 ^ 6 * p.exceptional.powerSplit.a ^ 10
```

という自然数式に正規化され、goal と一致する。

## Lean 固有の処理

### `Int.natAbs` による `ℤ → ℕ` の型移動

通常の絶対値 `abs` を使うと結果は `ℤ` に残るが、`Int.natAbs` を使うことで一度に `ℕ` へ移れる。後段が `Nat.Coprime`, `Nat.Prime`, 自然数冪の factor split を使うため、ここでの型選択は設計上重要である。

### `congrArg` による equation lifting

新たに arithmetic を証明し直すのではなく、既存 equality に関数を適用している。これは Lean で「等式から派生表現を作る」際の典型的かつ頑健な書き方である。

### `simpa` が符号と cast をまとめて処理する

右辺には

```lean
-(5 : ℤ) ^ 6 * (p.exceptional.powerSplit.a : ℤ) ^ 10
```

が現れるが、`natAbs` を通した後は cast、負号、積の absolute value が simplifier によって自然数式へ整理される。`pow_succ` はこの正規化を補助している。

## 冗長・重複箇所

本 theorem 自体は二行 proof で、局所的な冗長性はほぼない。

ただし設計上は、0275 と 0278 が「signed exact equation」と「natural absolute-value equation」のペアになっている。同様の signed-to-natAbs bridge が他の descent module でも複数出現するなら、`congrArg Int.natAbs` と `Int.natAbs_mul` の定型を共通化する余地はある。

現時点で本 theorem 単独をさらに抽象化する利益は小さい。むしろ 0275 を符号情報保存用、0278 を factorization API 用として明確に分けている現行設計は読みやすい。

## 最適化候補

### 1. `pow_succ` が本当に必要かの検証

現 proof は

```lean
simpa [Int.natAbs_mul, pow_succ] using h
```

としている。Mathlib の simp lemma 集合や cast normalization の状態によっては `pow_succ` を外しても通る可能性がある。

ただし本実行では Lean build を行わないため、これは **未検証の最適化候補** である。現在の proof は短く安定しており、無理に削る必要はない。

### 2. generic signed-product-to-natAbs lemma

同型の変換が多数ある場合には、例えば

```lean
x * y = -(m : ℤ) ^ k * (a : ℤ) ^ n
```

から自然数絶対値積を得る generic lemma を作れる。ただし cast と偶奇 exponent の条件を一般化すると、かえって API が重くなる可能性がある。

### 3. downstream 用の命名

`zeroSector_natAbs_product_eq` は役割を正確に表す良い名称である。より factorization-oriented に `zeroSector_abs_factorization_eq` のような名前も考えられるが、現名称は Lean の実装 primitive `natAbs` と直結しており、検索性では優れている。

## 必要 Mathlib import と import 最適化候補

対象ブランチの canonical standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

manifest 上、本 theorem は `DkMath/FLT/Five/SignedGoldenZeroSector.lean` に属する。

本 theorem が直接必要とする Mathlib 機構は非常に小さく、主として

- equality congruence `congrArg`
- `Int.natAbs`
- `Int.natAbs_mul`
- integer/natural casts と simp normalization
- `pow_succ`

である。project 側では `SignedGoldenRamifierStrippedPacket`, `GoldenInt`, `goldenPow`, `goldenFifthSndFactor`, 0275 が必要である。

ただし元 module の **最小 Mathlib import 集合は未確認** である。standalone artifact は全 source を `import Mathlib` で束ねており、本実行では Lean build を行わないため、具体的な import 縮小案は検証済みとは言えない。

## 既存 PDF との対応

対象ブランチの `docs/pdf` には

- `FLT5-main-ja-v0-r1.pdf`
- `FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

ただし GitHub コネクタの通常の repository-content 取得では PDF binary 本文を解析可能な形で得られなかったため、本 theorem に対応する具体的ページ番号・節番号・文章表現は **未確認** である。

したがって本解説の具体的な theorem-level 技術記述は `Flt5DkMath/FLT5StandAlone.lean` の `DkMath/FLT/Five/SignedGoldenZeroSector.lean` 生成区間を第一根拠としている。PDF との具体的位置対応は推測していない。

## Comparator challenge 化の可否

**適している。難度は低〜中程度。**

challenge では 0275 を既知として

```lean
p.zeroSector_snd_factor_eq hbeta
```

を与え、目標を

```lean
gamma.snd.natAbs *
    (goldenFifthSndFactor gamma.fst gamma.snd).natAbs =
  5 ^ 6 * p.exceptional.powerSplit.a ^ 10
```

とすればよい。

ポイントは algebra 展開ではなく、

1. equality に `Int.natAbs` を作用させる、
2. `Int.natAbs_mul` を使う、
3. casts と負号を `simp` で自然数へ正規化する、

という Lean の型移動技法にある。

短い proof だが、`ℤ` で得た arithmetic fact を downstream の `ℕ` factorization API へ接続する訓練として良い challenge になる。

## 次に読むべき宣言

次は

```lean
SignedGoldenRamifierStrippedPacket.zeroSector_coprime_coords
```

である。

正本 source では本 theorem の直後に配置されている。これは zero-sector fifth-power base `gamma` の二整数座標が primitive、すなわち

$$
\gcd(|r|,|s|)=1
$$

であることを示す。

証明では本 0278 の積等式を直接使い、仮想的な共通素因子 `q` を `5^6a^{10}` 側へ送り、packet の `five_not_dvd_b` と `powerSplit.coprime_a_b` のいずれかに矛盾させる。

したがって 0278 は単なる表示変換ではなく、次の primitive-coordinate theorem を起動する factorization input である。