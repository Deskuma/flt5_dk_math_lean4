# 0231 — `SignedGoldenRamifierStrippedPacket`

## Lean の型

```lean
/-- The exceptional packet after removing the unique visible ramifier `tau`. -/
structure SignedGoldenRamifierStrippedPacket (u v w : ℕ) : Type where
  exceptional : SignedSquareGoldenExceptionalPacket u v w
  alpha : GoldenInt
  beta : GoldenInt
  k : ℤ
  alpha_eq : alpha = ⟨exceptional.M, exceptional.N⟩
  linear_eq : 2 * exceptional.M + exceptional.N = 5 * k
  alpha_eq_tau_mul : alpha = goldenMul goldenTau beta
  beta_eq : beta = ⟨exceptional.M - k, 2 * k - exceptional.M⟩
  beta_norm : goldenNorm beta = (exceptional.powerSplit.b : ℤ) ^ 5
  beta_snd : beta.snd = -(5 : ℤ) ^ 7 * (exceptional.powerSplit.a : ℤ) ^ 10
  five_not_dvd_b : ¬ 5 ∣ exceptional.powerSplit.b
  five_not_dvd_beta_norm : ¬ (5 : ℤ) ∣ goldenNorm beta
  tau_not_dvd_beta : ¬ ∃ gamma : GoldenInt, beta = goldenMul goldenTau gamma
```

これは theorem ではなく `structure` 宣言であり、FLT5 の signed exceptional branch から、可視な ramified factor `tau = 2 + φ` を一度だけ取り除いた後の全データと証明を一つの packet にまとめる。

## 数学的主張・宣言の意味

この structure が表している中心的な状況は、exceptional packet から得られる黄金整数

$$
\alpha=M+N\varphi
$$

について、線形条件

$$
2M+N=5k
$$

を用いて norm-five element

$$
\tau=2+\varphi
$$

を因子として抽出し、

$$
\alpha=\tau\beta
$$

と書くことである。

`beta` は具体的に

$$
\beta=(M-k)+(2k-M)\varphi
$$

であり、そのノルムは

$$
N(\beta)=b^5
$$

まで純粋な第五冪へ落ちる。一方で第二座標は

$$
\beta_2=-5^7 a^{10}
$$

という明示式を持つ。

さらに packet は、

$$
5\nmid b,
$$

$$
5\nmid N(\beta),
$$

および

$$
\tau\nmid\beta
$$

を保持する。最後の条件は「可視な ramified factor `tau` は既に一度取り除かれ、`beta` にはもう残っていない」ことを表す。

したがってこの packet は、単なる因数分解結果ではなく、**ramified factor の除去がちょうど一段で完了したことまで証明済みの正規化状態** を表している。

## 証明全体での役割

0230 までで `GoldenInt` 自体の Euclidean-domain infrastructure が完成した。0231 からは再び FLT5 exceptional branch の本体へ戻り、その Euclidean-domain 構造を fifth-power factor splitting に利用するための入力データを整理する。

module header では、square/norm packet が

$$
N(\alpha)=5b^5
$$

を与え、対角線形座標の 5-整除から `tau` を抽出して

$$
\alpha=\tau\beta
$$

とし、stripped element `beta` が

$$
N(\beta)=b^5
$$

を満たす、と説明されている。

この structure の下流では、まず `nonempty_signedGoldenRamifierStrippedPacket_of_exceptional` が実際にこの packet を構築する。その後、選択関数を介して normal form から stripped packet を得る API が作られる。

さらに次 module `SignedGoldenConjugateCoprime.lean` では `beta` とその共役の差を調べ、packet の `beta_norm`、`beta_snd`、`five_not_dvd_b` を使って任意の共通因子のノルムが `±1` であることを示し、

$$
GoldenRelPrime(\beta,\overline\beta)
$$

を得る。

その coprimality が第五冪因子抽出へ渡され、最終的に

$$
\beta=\varepsilon\gamma^5
$$

という「unit × fifth power」形へ進むため、0231 は exceptional branch の代数的正規化を保持する重要な packet 境界である。

## 各 field の意味

### `exceptional`

```lean
exceptional : SignedSquareGoldenExceptionalPacket u v w
```

上流の signed square-golden exceptional data を丸ごと保持する。`M`、`N`、power split の `a`、`b`、five-adic 情報などはこの field 経由で参照される。

### `alpha`

```lean
alpha : GoldenInt
```

exceptional packet の整数座標 `(M,N)` を黄金整数へ持ち上げた元。

### `beta`

```lean
beta : GoldenInt
```

`alpha` から可視な ramifier `tau` を除いた stripped element。以後の conjugate-coprime / fifth-power extraction の主役になる。

### `k`

```lean
k : ℤ
```

線形 5-整除

$$
2M+N=5k
$$

の商 witness。

### `alpha_eq`

```lean
alpha_eq : alpha = ⟨exceptional.M, exceptional.N⟩
```

abstract field `alpha` と上流整数座標の対応を固定する。

### `linear_eq`

```lean
linear_eq : 2 * exceptional.M + exceptional.N = 5 * k
```

`goldenTau` 因子を抽出するための整数線形条件。

### `alpha_eq_tau_mul`

```lean
alpha_eq_tau_mul : alpha = goldenMul goldenTau beta
```

packet の中心となる factorization

$$
\alpha=\tau\beta
$$

を保持する。

### `beta_eq`

```lean
beta_eq : beta = ⟨exceptional.M - k, 2 * k - exceptional.M⟩
```

stripped element の明示座標式。この式により下流で `beta.snd` などを整数算術へ直接落とせる。

### `beta_norm`

```lean
beta_norm : goldenNorm beta = (exceptional.powerSplit.b : ℤ) ^ 5
```

`tau` の norm が `5` であることを用いて、元の `N(alpha)=5*b^5` から 5 を一つ取り除いた結果を保持する。

### `beta_snd`

```lean
beta_snd : beta.snd = -(5 : ℤ) ^ 7 * (exceptional.powerSplit.a : ℤ) ^ 10
```

共役差

$$
\beta-\overline\beta
$$

の norm を明示化するための重要な第二座標式。次 module で

$$
N(\beta-\overline\beta)=-5^{15}a^{20}
$$

を導く際に直接使われる。

### `five_not_dvd_b`

```lean
five_not_dvd_b : ¬ 5 ∣ exceptional.powerSplit.b
```

power split の residual fifth-power base `b` が 5 を含まないことを保持する。

### `five_not_dvd_beta_norm`

```lean
five_not_dvd_beta_norm : ¬ (5 : ℤ) ∣ goldenNorm beta
```

`beta_norm = b^5` と `5 ∤ b` から、stripped element の norm 自体にも 5 が残っていないことを明示する。

### `tau_not_dvd_beta`

```lean
tau_not_dvd_beta : ¬ ∃ gamma : GoldenInt, beta = goldenMul goldenTau gamma
```

`beta` がさらに `tau` で割れないことを直接保証する。もし `beta = tau * gamma` なら norm の乗法性と `N(tau)=5` により `5 ∣ N(beta)` となり、直前 field と矛盾する。

## 直接依存する定義・補題

structure 宣言そのものが型として直接参照する主な上流要素は次の通りである。

- `SignedSquareGoldenExceptionalPacket`
- `GoldenInt`
- `goldenTau`
- `goldenMul`
- `goldenNorm`
- power-split packet 内の `a`, `b`
- 整数および自然数の整除 `∣`

structure 宣言自体には proof script はないが、各 field を実際に埋める直後の constructor theorem では、特に次を利用する。

- `exists_goldenTau_factor_of_five_dvd`
- `goldenNorm_mul`
- `goldenNorm_tau`
- prime `5` の `dvd_of_dvd_pow`
- 上流 packet の `golden_eq`, `tenth_boundary`, five-adic residual facts

## 構築の流れ

0231 自体は structure 宣言なので、ここでは「証明」ではなく **必要な certificate の仕様** を定義している。

直後の `nonempty_signedGoldenRamifierStrippedPacket_of_exceptional` は概ね次の順に field を埋める。

1. $A=2M+N$ と置き、上流 discriminant identity から $5\mid A^2$ を得る。
2. 5 が prime であることから $5\mid A$ を得る。
3. `exists_goldenTau_factor_of_five_dvd` を使い、`k`, `beta` と
   $$
   \alpha=\tau\beta
   $$
   を構成する。
4. ノルム乗法性と `N(tau)=5` から
   $$
   N(\beta)=b^5
   $$
   を導く。
5. `beta_eq` と上流の tenth-boundary relation から `beta_snd` を計算する。
6. five-adic residual 条件から $5\nmid b$ を導く。
7. `beta_norm` から $5\nmid N(\beta)$ を得る。
8. もし `tau | beta` なら `N(tau)=5` により $5|N(beta)$ となるので矛盾し、`tau_not_dvd_beta` を得る。

この流れにより、structure の各 field は互いに独立な飾りではなく、**一つの ramifier stripping argument の各段階を保存した certificate** になっている。

## Lean 固有の処理

`structure ... : Type where` なので、これは命題ではなくデータ型である。各等式・非整除命題も field としてデータに付随し、packet を受け取る downstream theorem は別途仮定を再構築せず `p.beta_norm`、`p.beta_snd`、`p.tau_not_dvd_beta` のように projection で利用できる。

`exceptional : SignedSquareGoldenExceptionalPacket u v w` を最初に保持しているため、後続 field の型は dependent field として `exceptional.M` や `exceptional.powerSplit.b` を直接参照している。これにより packet 内部の証明対象が同じ exceptional source に結び付けられ、異なる source の値を混同できない。

`tau_not_dvd_beta` は標準 `∣` ではなく raw `goldenMul` による existential factorization を直接書いている。これは前段の explicit-coordinate API と整合する一方、既に `EuclideanDomain GoldenInt` が存在する段階なので標準 divisibility API へ寄せる余地もある。

## 冗長・重複箇所

いくつかの field は論理的には他の field から再導出できる。

- `five_not_dvd_beta_norm` は `beta_norm` と `five_not_dvd_b` から導ける。
- `tau_not_dvd_beta` は `five_not_dvd_beta_norm`、`goldenNorm_mul`、`goldenNorm_tau` から導ける。
- `alpha` は `alpha_eq` があるため、原理的には常に `⟨exceptional.M, exceptional.N⟩` を直接使える。
- `beta` も `beta_eq` により座標式から再構成可能である。

したがって論理的最小性だけなら packet をかなり縮小できる。

しかし現在の設計には、下流 theorem が重要な semantic milestone を field projection 一つで取り出せる利点がある。特に `beta_norm`、`beta_snd`、`tau_not_dvd_beta` は後続 proof の読みやすさと依存監査性を大きく改善するため、意図的な cached certificate と見るのが自然である。

## 最適化候補

1. **derived field と primitive field を明確に分ける**
   - `five_not_dvd_beta_norm` や `tau_not_dvd_beta` を theorem として structure 外へ出す設計と比較できる。

2. **`alpha` / `beta` の explicit field を削減する**
   - 座標式から `def` で算出する方式にすれば coherence equality を減らせるが、projection が長くなる。

3. **標準 divisibility API へ統一する**
   - `tau_not_dvd_beta` を `¬ goldenTau ∣ beta` とし、0230 で得た `EuclideanDomain` をより直接利用する案がある。

4. **ramifier stripping certificate を小さな sub-structure に分ける**
   - factorization (`alpha=tau*beta`) と strippedness (`5∤N(beta)`, `tau∤beta`) を別構造へ分離すれば再利用性が上がる可能性がある。

5. **`beta_norm` を fifth-power witness として bundle する**
   - 単なる equality ではなく「norm が exact fifth power」という専用 predicate / structure を作る案もある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。structure 宣言そのものは主として既存の project 型・定義と基本的な整除命題しか必要としない。

ただし同一 `SignedGoldenRamifierStripped.lean` module の直後の constructor theorem では、prime 整除、`norm_num`、`nlinarith`、`omega`、`ring`、整数 cast、ノルム乗法性などを使うため、module 全体の最小 import は structure 単独より大きい。

今回 Lean build は行わないため、正確な最小 Mathlib import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。特に packet design の比較として面白い。

比較候補は次の通り。

- A: 現行の proof-rich structure。derived certificate も field として保持する。
- B: 最小 data structure + derived theorem 群。
- C: `alpha`, `beta` を座標から計算する normalized structure。
- D: 標準 `Dvd.dvd` / `IsUnit` / Euclidean-domain API を全面利用する structure。
- E: ramifier factorization と strippedness を別 packet に分ける staged design。

比較軸は、field 数、constructor proof の長さ、downstream theorem の長さ、coherence obligation、再利用性、Mathlib 標準 API との整合、証明監査時の読みやすさである。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` generated section である。

source の module header は、`alpha` の norm が `5*b^5` である状態から可視 ramifier `tau` を除き、`beta` が `N(beta)=b^5`、明示的第二座標、5-free norm、再度 `tau` で割れないという stripped state を得ることを、この module の目的として明記している。

対象ブランチには `docs/pdf/FLT5-main-ja-v0-r1.pdf` と `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし本 structure に対応する具体的 PDF ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0232 `five_not_dvd_powerSplit_b`** である。

```lean
private theorem five_not_dvd_powerSplit_b
    {u v w : ℕ} (p : SignedSquareGoldenExceptionalPacket u v w) :
    ¬ 5 ∣ p.powerSplit.b := by
  ...
```

これは private theorem であり、five-adic residual が modulo 25 で持つ既知の条件から `5 ∤ b` を取り出す。0231 の `five_not_dvd_b` field を実際に構築するための最初の補助 certificate である。
