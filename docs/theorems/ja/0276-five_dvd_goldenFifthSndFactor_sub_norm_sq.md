# 0276 — `five_dvd_goldenFifthSndFactor_sub_norm_sq`

## 宣言種別

これは **`theorem`** である。

`DkMath.FLT.Five.SignedGoldenZeroSector` に置かれた整数合同補題であり、GoldenInt の fifth-power 第二座標に現れる quartic factor `goldenFifthSndFactor` が、golden norm の平方と modulo 5 で一致することを示す。

## Lean の型

```lean
/-- The quartic factor is the square of the golden norm modulo five. -/
theorem five_dvd_goldenFifthSndFactor_sub_norm_sq (gamma : GoldenInt) :
    (5 : ℤ) ∣
      goldenFifthSndFactor gamma.fst gamma.snd - goldenNorm gamma ^ 2 := by
  refine ⟨gamma.fst * gamma.snd ^ 2 * (gamma.fst + gamma.snd), ?_⟩
  simp only [goldenFifthSndFactor, goldenNorm]
  ring
```

`gamma = (r,s)` と書く。定義より

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4
$$

および

$$
N(r,s)=r^2+rs-s^2
$$

である。本 theorem は

$$
5\mid\bigl(H(r,s)-N(r,s)^2\bigr)
$$

を述べる。

より強く、証明中で実際に与えている witness を展開すると

$$
H(r,s)-N(r,s)^2
=5rs^2(r+s)
$$

という整数恒等式である。したがって

$$
H(r,s)\equiv N(r,s)^2\pmod 5
$$

が直ちに従う。

## 数学的主張の意味

`goldenFifthSndFactor` は GoldenInt の fifth power

$$
(r+s\varphi)^5
$$

の第二座標を

$$
5s\,H(r,s)
$$

と因数分解したときに現れる quartic factor である。一方 `goldenNorm` は

$$
N(r+s\varphi)=r^2+rs-s^2
$$

である。

一見すると fifth-power coordinate の quartic polynomial $H$ と norm の平方 $N^2$ は別物に見える。しかし差を取ると必ず 5 の倍数になり、しかも

$$
H-N^2=5rs^2(r+s)
$$

という非常に単純な補正項しか残らない。

この congruence が重要なのは、5 に関する可除性を $H$ と $N$ の間で移送できるからである。特に

$$
5\mid H
$$

なら、本 theorem と `dvd_sub` を組み合わせて

$$
5\mid N^2
$$

を得る。5 は素数なので

$$
5\mid N
$$

まで降ろせる。zero sector では直前の 0274 が

$$
5\nmid N(\gamma)
$$

を保証しているため、結局

$$
5\nmid H(r,s)
$$

が導かれる。

したがって 0276 は、fifth-power coordinate 側の quartic factor に packet の norm 側の five-adic exclusion を転送するための **mod-5 bridge** である。

## 証明全体での役割

0275 `SignedGoldenRamifierStrippedPacket.zeroSector_snd_factor_eq` は zero sector で

$$
sH(r,s)=-5^6a^{10}
$$

という exact signed product equation を作った。

その後 descent 用にこの積を分離するには、5 の因子が $H$ 側へ紛れ込まないことを示す必要がある。そこで 0276 が

$$
H\equiv N^2\pmod 5
$$

を与え、0274 の $5\nmid N$ と接続する。

正本 source の直後の theorem

```lean
SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_sndFactor
```

はまさにこの二つを組み合わせる。`hH : 5 ∣ H` を仮定し、0276 から $5\mid N^2$、素数性から $5\mid N$ を得て、0274 と矛盾させる。

さらに正本全体を追うと、本 theorem は zero-sector packet だけに閉じていない。後続の `GoldenZeroSectorCandidate.five_not_dvd_H`、`GoldenZeroSectorDescentPacket.five_not_dvd_H`、および fifth-root 側の `fifthRoot_five_not_dvd_H` でも再利用されている。したがってこれは局所的な一回限りの補題ではなく、Golden fifth-power arithmetic 全体で使われる基礎 congruence である。

## 直接依存する定義・補題

### `GoldenInt`

Golden order の元を二整数座標で表す型である。本 theorem は `gamma.fst`, `gamma.snd` のみを使う。

### `goldenFifthSndFactor`

正本では次の quartic polynomial として定義される。

```lean
def goldenFifthSndFactor (r s : ℤ) : ℤ :=
  r ^ 4 + 2 * r ^ 3 * s + 4 * r ^ 2 * s ^ 2 +
    3 * r * s ^ 3 + s ^ 4
```

これは fifth power の第二座標を因数分解したときの $H(r,s)$ である。

### `goldenNorm`

正本では

```lean
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

と定義される。

したがって `gamma=(r,s)` に対して

$$
N(\gamma)=r^2+rs-s^2
$$

である。

### 整数の可除性 `Dvd.dvd`

goal は equality ではなく

```lean
(5 : ℤ) ∣ expression
```

であるため、Lean では witness を明示して

```lean
⟨k, equality⟩
```

を構築する。

### `ring`

定義展開後に残る純粋な整数 polynomial identity を正規化して閉じる。

## 証明または構築の流れ

### 1. 5 の倍数であることの witness を直接与える

```lean
refine ⟨gamma.fst * gamma.snd ^ 2 * (gamma.fst + gamma.snd), ?_⟩
```

`a ∣ b` は「ある整数 $k$ が存在して $b=a k$」という形なので、ここでは

$$
k=r s^2(r+s)
$$

を選んでいる。

つまり証明は単なる congruence reasoning ではなく、最初からより強い exact factorization

$$
H-N^2=5rs^2(r+s)
$$

を知っている。

### 2. 二つの定義だけを展開する

```lean
simp only [goldenFifthSndFactor, goldenNorm]
```

`H` と `N` を座標多項式へ展開する。`simp only` を用いているので、不要な simp lemma による式変形を避け、証明の依存をこの二定義に限定している。

### 3. polynomial identity を `ring` で閉じる

```lean
ring
```

展開後の goal は整数係数多項式の恒等式である。`ring` が双方を正規形へ変換して一致を確認する。

ここには素数性、packet data、zero-sector 仮定は一切登場しない。0276 自体は GoldenInt の任意の元に対して成立する純粋代数恒等式である。

## Lean 固有の処理

### divisibility witness の構築

Lean の `a ∣ b` は existential data を持つため、

```lean
refine ⟨..., ?_⟩
```

で商を直接提示できる。本 theorem ではこの witness 自体が数学的情報を持っており、差の factorization を明示している。

### `simp only`

通常の `simp` ではなく

```lean
simp only [goldenFifthSndFactor, goldenNorm]
```

とすることで、定義展開以外の自動簡約を抑えている。これは小さな代数補題では良い設計であり、simp set の将来変更による proof drift も減らす。

### `ring`

`ring` は整数環の polynomial identity を決定的に処理する。ここでは `nlinarith` よりも適切である。仮定から inequality/equality を導くのではなく、定義展開後の恒等式そのものを証明しているからである。

## 冗長・重複箇所

本 proof は三行であり、局所的な冗長性はほぼない。

むしろ注目すべきは、statement が可除性だけを公開している一方で proof 内部では exact identity

$$
H-N^2=5rs^2(r+s)
$$

を証明している点である。

後続でこの quotient $rs^2(r+s)$ 自体を使う必要がないなら、現行 API は適切である。しかし同じ exact difference formula を別箇所で再導出するなら、より強い equality theorem を先に置き、本 theorem をその corollary にする余地がある。

## 最適化候補

### 1. exact identity の API 化

例えば

```lean
theorem goldenFifthSndFactor_sub_norm_sq_eq (gamma : GoldenInt) :
  goldenFifthSndFactor gamma.fst gamma.snd - goldenNorm gamma ^ 2 =
    5 * gamma.fst * gamma.snd ^ 2 * (gamma.fst + gamma.snd) := by
  simp only [goldenFifthSndFactor, goldenNorm]
  ring
```

のような theorem を基礎 API とし、0276 を

```lean
rw [goldenFifthSndFactor_sub_norm_sq_eq]
exact dvd_mul_right ...
```

型の corollary にできる。

これは quotient を downstream で利用する場合に有益である。一方、現状の用途は mod 5 可除性だけなので、現行の短い theorem の方が API surface は小さい。

### 2. generic congruence lemma の検討

後続では

$$
5\mid H,
\qquad
5\mid(H-N^2)
$$

から $5\mid N^2$ を得るパターンが複数箇所で再出現する。これは 0276 自身の問題ではないが、`H ≡ N² [ZMOD 5]` 形式の API や専用 transfer lemma を作れば downstream の `dvd_sub` + `ring_nf` を短縮できる可能性がある。

### 3. statement を `Int.ModEq` にする案

数学的意味を直接表すなら

```lean
Int.ModEq 5
  (goldenFifthSndFactor gamma.fst gamma.snd)
  (goldenNorm gamma ^ 2)
```

も候補になる。ただし現行 downstream は divisibility API を使っているため、既存コードとの接続性では現在の `5 ∣ H - N²` の方が実用的である。

## 必要 Mathlib import と import 最適化候補

対象ブランチの canonical standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

standalone manifest では `five_dvd_goldenFifthSndFactor_sub_norm_sq` は `DkMath/FLT/Five/SignedGoldenZeroSector.lean` に属し、その前段で `GoldenOrder.lean` と `GoldenFifthPowerCoordinates.lean` などが読み込まれている。

0276 自身が Mathlib から直接必要とする主要機構は、整数環、可除性、`simp only`、および `ring` tactic である。project 側では `GoldenInt`, `goldenNorm`, `goldenFifthSndFactor` が必要である。

ただし元 module の **最小 Mathlib import 集合は未確認** である。`ring` に必要な tactic import と project module の transitive imports を切り分けて Lean で検証しなければ、安全な縮小案は確定できない。本実行では Lean build を行わないため、`import Mathlib` の具体的置換は提案レベルに留める。

## 既存 PDF との対応

対象ブランチ `docs/pdf` には

- `FLT5-main-ja-v0-r1.pdf`
- `FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

ただし GitHub コネクタでは PDF binary 本文を直接解析可能な形で取得できず、本実行では 0276 に対応する具体的ページ番号、節番号、あるいは

$$
H-N^2=5rs^2(r+s)
$$

が PDF 本文に同じ形で現れるかどうかは **未確認** である。したがって PDF の具体的位置は推測せず、技術的記述は対象ブランチの Lean 正本を第一根拠とする。

## Comparator challenge 化の可否

**非常に適している。難度は低〜中程度。**

challenge では次の定義を与える。

```lean
def goldenFifthSndFactor (r s : ℤ) : ℤ :=
  r ^ 4 + 2 * r ^ 3 * s + 4 * r ^ 2 * s ^ 2 +
    3 * r * s ^ 3 + s ^ 4

def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

そして goal を

```lean
(5 : ℤ) ∣
  goldenFifthSndFactor gamma.fst gamma.snd - goldenNorm gamma ^ 2
```

とする。

評価点は、

1. divisibility goal に対して witness を構成できるか、
2. witness $r s^2(r+s)$ を polynomial structure から見抜けるか、
3. 定義展開後を `ring` で適切に閉じられるか、

である。

特に theorem statement だけを見ると「mod 5 の証明」に見えるが、最短 proof は exact factorization の witness を発見することである。このため Comparator では algebraic structure recognition の良い題材になる。

## 次に読むべき宣言

次は **0277 `SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_sndFactor`** を読むべきである。

正本では概ね次の流れである。

```lean
theorem SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_sndFactor
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd := by
  intro hH
  apply p.zeroSector_five_not_dvd_gamma_norm hbeta
  have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq gamma
  have hnormSq : (5 : ℤ) ∣ goldenNorm gamma ^ 2 := by
    have h := dvd_sub hH hdiff
    ring_nf at h
    exact h
  exact (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
```

0276 が $H\equiv N^2\pmod5$ という transfer bridge を用意し、0277 が直前の 0274 `zeroSector_five_not_dvd_gamma_norm` と組み合わせて

$$
5\nmid H(r,s)
$$

を確定する。

したがって依存順は

$$
\text{0274: }5\nmid N
\quad\longrightarrow\quad
\text{0276: }H\equiv N^2\pmod5
\quad\longrightarrow\quad
\text{0277: }5\nmid H
$$

となる。