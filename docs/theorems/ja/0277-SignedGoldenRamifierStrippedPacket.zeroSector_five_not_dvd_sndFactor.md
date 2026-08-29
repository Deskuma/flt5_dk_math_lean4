# 0277 — `SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_sndFactor`

## 宣言種別

これは **`theorem`** である。

`SignedGoldenRamifierStrippedPacket` の zero sector において、fifth power の第二座標に現れる quartic factor `goldenFifthSndFactor` が 5 で割れないことを示す。

## Lean の型

```lean
/-- The zero-sector quartic factor is not divisible by five. -/
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

`gamma = (r,s)` とし、

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s),
\qquad
N(\gamma)=\operatorname{goldenNorm}(\gamma)
$$

と書けば、主張は

$$
\beta=\gamma^5
\quad\Longrightarrow\quad
5\nmid H(r,s)
$$

である。

## 数学的主張の意味

直前の 0276 は

$$
5\mid\bigl(H(r,s)-N(\gamma)^2\bigr)
$$

すなわち

$$
H(r,s)\equiv N(\gamma)^2\pmod 5
$$

を与える。一方 0274 `zeroSector_five_not_dvd_gamma_norm` は zero sector で

$$
5\nmid N(\gamma)
$$

を保証する。

そこで仮に

$$
5\mid H(r,s)
$$

とすると、0276 との引き算から

$$
5\mid N(\gamma)^2
$$

となる。5 は素数なので

$$
5\mid N(\gamma)
$$

が従い、0274 と矛盾する。

したがって本 theorem は、norm 側で既に確立された five-adic exclusion を quartic factor 側へ転送する theorem である。

## 証明全体での役割

0275 では zero sector の第二座標から

$$
s\,H(r,s)=-5^6a^{10}
$$

という exact signed product equation が得られた。

この積を後で `Nat` の absolute-value equation に移し、互いに素な因子へ分解するためには、右辺にある $5^6$ が quartic factor $H$ 側へ吸収されないことを先に示しておく必要がある。

0277 はまさに

$$
5\nmid H(r,s)
$$

を確立するため、その後の factor separation で

$$
\gcd(5^6,H)=1
$$

を作る入口になる。

正本 source の後続では、`zeroSector_natAbs_product_eq` で

$$
|s|\,|H(r,s)|=5^6a^{10}
$$

へ移した後、本 theorem が `Nat.Coprime (5^6) |H|` を作るために直接再利用される。

## 直接依存する定義・補題

### `SignedGoldenRamifierStrippedPacket`

FLT5 の signed golden exceptional branch から得られる packet 構造である。本 theorem では packet 自身の詳細を直接展開せず、packet-level API である `zeroSector_five_not_dvd_gamma_norm` を利用する。

### `GoldenInt`

Golden order の元を二整数座標で表す型である。`gamma.fst` と `gamma.snd` が quartic factor の入力となる。

### `goldenFifthSndFactor`

fifth power の第二座標に現れる quartic polynomial である。正本では

```lean
def goldenFifthSndFactor (r s : ℤ) : ℤ :=
  r ^ 4 + 2 * r ^ 3 * s + 4 * r ^ 2 * s ^ 2 +
    3 * r * s ^ 3 + s ^ 4
```

という形で定義される。

### `goldenNorm`

GoldenInt の norm で、座標では

$$
N(r,s)=r^2+rs-s^2
$$

である。

### 0274 `SignedGoldenRamifierStrippedPacket.zeroSector_five_not_dvd_gamma_norm`

zero sector 仮定 `hbeta : p.beta = goldenPow gamma 5` のもとで

$$
5\nmid N(\gamma)
$$

を与える。本 theorem の最終 contradiction target である。

### 0276 `five_dvd_goldenFifthSndFactor_sub_norm_sq`

任意の `gamma : GoldenInt` に対して

$$
5\mid(H-N^2)
$$

を与える。本 theorem では `hH : 5 ∣ H` と組み合わせて $5\mid N^2$ を作る。

### `dvd_sub`

整数の可除性について、同じ整数が二つの項を割るなら差も割るという標準補題である。

### `Prime.dvd_of_dvd_pow`

素数が冪を割るなら底を割るという性質。本 theorem では 5 が `goldenNorm gamma ^ 2` を割ることから `goldenNorm gamma` を割ることを得る。

## 証明の流れ

### 1. 結論の否定を仮定する

```lean
intro hH
```

ここで

```lean
hH : (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd
```

を仮定する。

### 2. 最終的に 0274 へ矛盾を渡す

```lean
apply p.zeroSector_five_not_dvd_gamma_norm hbeta
```

goal を

```lean
(5 : ℤ) ∣ goldenNorm gamma
```

へ変える。これにより証明全体が「$5\mid H$ なら $5\mid N$」という transfer proof になる。

### 3. 0276 の合同情報を取得する

```lean
have hdiff := five_dvd_goldenFifthSndFactor_sub_norm_sq gamma
```

これで

$$
5\mid(H-N^2)
$$

を得る。

### 4. `dvd_sub` で norm の平方へ可除性を移す

```lean
have hnormSq : (5 : ℤ) ∣ goldenNorm gamma ^ 2 := by
  have h := dvd_sub hH hdiff
  ring_nf at h
  exact h
```

`hH` は $5\mid H$、`hdiff` は $5\mid(H-N^2)$ なので、差

$$
H-(H-N^2)=N^2
$$

も 5 で割れる。

Lean では `dvd_sub hH hdiff` の結果が syntactically そのまま `5 ∣ N^2` にはならないため、`ring_nf at h` で差を正規化する。

### 5. 素数 5 から平方根側へ降ろす

```lean
exact (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow hnormSq
```

`norm_num` で整数 5 の素数性を示し、`Prime.dvd_of_dvd_pow` で

$$
5\mid N^2 \Longrightarrow 5\mid N
$$

を得る。これが 0274 と矛盾して proof が閉じる。

## Lean 固有の処理

### `apply` による否定命題の反転

`p.zeroSector_five_not_dvd_gamma_norm hbeta` の型は

```lean
¬ (5 : ℤ) ∣ goldenNorm gamma
```

なので、これを `apply` すると現在の contradiction goal が `5 ∣ goldenNorm gamma` に置き換わる。Lean では `¬ P` が `P → False` なので自然な処理である。

### `dvd_sub` の向き

`dvd_sub hH hdiff` が作る式は数学的には

$$
5\mid H-(H-N^2)
$$

であり、これを `ring_nf` が $N^2$ へ正規化する。ここでは可除性 API と polynomial normalizer を組み合わせている。

### `show Prime (5 : ℤ) by norm_num`

`Prime.dvd_of_dvd_pow` を整数上で使うため、Lean に `(5 : ℤ)` の素数性を明示的に供給している。自然数の `Nat.Prime 5` ではなく整数の `Prime (5 : ℤ)` である点が Lean 固有の型合わせである。

## 冗長・重複箇所

本 theorem 自体は短く、局所的な冗長性は小さい。

ただし正本後段には、同じ 0276 を使って

1. `hH : 5 ∣ H` を仮定し、
2. `dvd_sub hH hdiff` で $5\mid N^2$ を作り、
3. `Prime.dvd_of_dvd_pow` で $5\mid N$ に降ろす

というパターンが再出現する。特に fifth-root 側の `fifthRoot_five_not_dvd_H` は非常に近い骨格を持つ。

したがって重複は 0277 内部よりも **downstream transfer pattern** に存在する。

## 最適化候補

### 1. generic transfer lemma の抽出

例えば整数 `H N` に対し、

```lean
(5 : ℤ) ∣ H - N ^ 2 → ¬ (5 : ℤ) ∣ N → ¬ (5 : ℤ) ∣ H
```

という一般補題を抽出できる。そうすれば 0277 と後続類似 theorem は、0276 と norm exclusion を渡すだけで済む。

ただしこの抽象化が一度か二度しか使われないなら、現行 proof の方が局所的で読みやすい。

### 2. `Int.ModEq` API の利用

0276 を

$$
H\equiv N^2\pmod5
$$

の `Int.ModEq` 形式でも提供すれば、可除性の移送を congruence API で記述できる可能性がある。ただし現行 downstream は `Dvd` API を広く使っているため、必ずしも短くなるとは限らない。

### 3. `ring_nf at h` の除去可能性

`dvd_sub` の向きを変える、あるいは補助 equality を挟むことで `ring_nf at h` を避けられる可能性はある。ただし現行の一行正規化は頑健であり、最適化効果は小さい。

## 必要 Mathlib import と import 最適化候補

対象ブランチの canonical standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem が直接利用する Mathlib 側の主要機構は、整数の可除性、`Prime`, `dvd_sub`, `Prime.dvd_of_dvd_pow`, `norm_num`, `ring_nf` である。project 側では `SignedGoldenRamifierStrippedPacket`, `GoldenInt`, `goldenNorm`, `goldenFifthSndFactor`, 0274, 0276 が必要である。

生成 artifact の manifest では本 theorem は `DkMath/FLT/Five/SignedGoldenZeroSector.lean` に属する。

ただし元 module の **最小 Mathlib import 集合は未確認** である。本実行では Lean build を行わないため、`import Mathlib` からの具体的な縮小案は検証済み提案としては出さない。`Mathlib` の tactic/import 分割と project module の transitive import を実際に Lean で検証する必要がある。

## 既存 PDF との対応

対象ブランチには日本語版・英語版の FLT5 PDF が置かれていることをリポジトリ上で確認している。

ただし本実行では PDF binary 本文を解析可能な形で取得できていないため、0277 に対応する具体的ページ番号・節番号、および PDF 中で同じ quartic-factor congruence argument がどの表現で記述されているかは **未確認** である。したがって技術的記述は Lean 正本を第一根拠とし、PDF の具体的位置は推測しない。

## Comparator challenge 化の可否

**適している。難度は中程度。**

challenge としては、次のものを与えるとよい。

- `hbeta : p.beta = goldenPow gamma 5`
- 0274 `p.zeroSector_five_not_dvd_gamma_norm hbeta`
- 0276 `five_dvd_goldenFifthSndFactor_sub_norm_sq gamma`

そして目標を

```lean
¬ (5 : ℤ) ∣ goldenFifthSndFactor gamma.fst gamma.snd
```

とする。

解答者は

1. contradiction を仮定する、
2. `dvd_sub` で $5\mid N^2$ を作る、
3. 5 の素数性から $5\mid N$ を得る、
4. norm exclusion と衝突させる

という流れを発見する必要がある。

単なる `ring` exercise ではなく、可除性・素数・既存 API の合成を試すため、Comparator 用として良い題材である。

## 次に読むべき宣言

次は **0278 `SignedGoldenRamifierStrippedPacket.zeroSector_natAbs_product_eq`** を読むべきである。

正本では 0277 の直後に置かれ、0275 の signed equation

$$
sH(r,s)=-5^6a^{10}
$$

を `Int.natAbs` へ移して

$$
|s|\,|H(r,s)|=5^6a^{10}
$$

という自然数の積等式へ変換する。

0277 が quartic factor から 5 を排除した直後に、0278 が積を `Nat` の factorization world へ運ぶため、依存順としてここを続けて読むのが自然である。
