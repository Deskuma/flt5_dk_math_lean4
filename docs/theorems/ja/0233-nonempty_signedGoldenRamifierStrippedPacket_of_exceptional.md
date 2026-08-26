# 0233 — `nonempty_signedGoldenRamifierStrippedPacket_of_exceptional`

## Lean の型

```lean
private theorem nonempty_signedGoldenRamifierStrippedPacket_of_exceptional
    {u v w : ℕ} (p : SignedSquareGoldenExceptionalPacket u v w) :
    Nonempty (SignedGoldenRamifierStrippedPacket u v w) := by
  ...
```

これは `private theorem` であり、`SignedSquareGoldenExceptionalPacket u v w` から 0231 `SignedGoldenRamifierStrippedPacket u v w` の inhabitant が存在することを証明する構築定理である。

公開 API ではなく同一 module 内部の証明部品として使われ、直後の `signedGoldenRamifierStrippedPacket_of_exceptional` が `Classical.choice` で実際の packet を選ぶための存在証明を提供する。

## 数学的主張

入力 packet `p` は、exceptional branch における整数座標 `M,N` と exact five-adic power split を保持している。0233 はそこから黄金整数

$$
\alpha=M+N\varphi
$$

を作り、可視 ramifier

$$
\tau=2+\varphi
$$

を一度取り除いた

$$
\alpha=\tau\beta
$$

という factorization を構成する。

さらに構成された `β` について、packet 0231 が要求する主要な証明データをすべて満たすことを示す。

$$
N(\beta)=b^5,
$$

$$
\beta_{\mathrm{snd}}=-5^7a^{10},
$$

$$
5\nmid b,
$$

$$
5\nmid N(\beta),
$$

$$
\tau\nmid\beta.
$$

したがって本 theorem は、「exceptional packet から ramified factor を一本だけ除去し、その残余が 5 に関して primitive である」という正規化操作を存在 theorem として完成させる。

## 証明全体での役割

0231 では `SignedGoldenRamifierStrippedPacket` という目標 structure だけが定義され、0232 ではその field の一つである

$$
5\nmid b
$$

を five-adic residual の mod 25 情報から抽出した。

0233 はそれらを統合する中心的な constructor theorem である。proof の流れは概念的に

$$
\text{exceptional packet}
\longrightarrow 5\mid(2M+N)
\longrightarrow \alpha=\tau\beta
\longrightarrow N(\beta)=b^5
\longrightarrow 5\nmid N(\beta)
\longrightarrow \tau\nmid\beta
$$

となる。

この packet が得られると、次 module `SignedGoldenConjugateCoprime.lean` では `β` とその共役の共通因子を調べ、最終的に相対素性を確立する。その後は Euclidean-domain / gcd infrastructure を使って fifth-power factor splitting へ進む。

つまり 0233 は、five-adic exceptional data を黄金整数環の **ramifier-stripped primitive factor** へ変換する境界 theorem である。

## 直接依存する定義・補題

直接・主要な依存は次の通りである。

- 0231 `SignedGoldenRamifierStrippedPacket`
- 0232 `five_not_dvd_powerSplit_b`
- `SignedSquareGoldenExceptionalPacket`
- 0186 `exists_goldenTau_factor_of_five_dvd`
- 0174 `goldenNorm_mul`
- 0184 `goldenNorm_tau`
- 0172 `goldenNorm_eq_GoldenNorm`
- `goldenNorm`
- `goldenTau`
- `GoldenInt`
- `Prime.dvd_of_dvd_pow`
- `exact_mod_cast`
- `mul_left_cancel₀`
- `nlinarith`, `omega`, `ring`, `norm_num`

入力 packet 側では `p.discriminant_five_eq`、`p.golden_eq`、`p.tenth_boundary`、`p.powerSplit.b`、`p.powerSplit.a` などの certificate を利用する。

## 証明・構築の流れ

### 1. 線形量 `A = 2M+N` を置く

proof はまず

```lean
let A : ℤ := 2 * p.M + p.N
```

と置き、入力 packet の discriminant relation から

```lean
have hAeq : A ^ 2 = 5 * (p.N ^ 2 + 4 * (p.powerSplit.b : ℤ) ^ 5) := by
  dsimp [A]
  nlinarith [p.discriminant_five_eq]
```

を得る。

右辺が `5` の倍数なので、

$$
5\mid A^2
$$

であり、`5` が素数であることから

$$
5\mid A
$$

を得る。

Lean では

```lean
have h5sq : (5 : ℤ) ∣ A ^ 2 := ⟨_, hAeq⟩
have h5A : (5 : ℤ) ∣ A :=
  (show Prime (5 : ℤ) by norm_num).dvd_of_dvd_pow h5sq
```

という形で certificate を作る。

### 2. `τ` 因子を具体的に抽出する

0186 を使い、`5 ∣ 2*M+N` から

```lean
rcases exists_goldenTau_factor_of_five_dvd h5A with
  ⟨k, beta, hk, hbeta, halpha⟩
```

を得る。

これにより

$$
2M+N=5k,
$$

$$
\beta=\langle M-k,\,2k-M\rangle,
$$

$$
\langle M,N\rangle=\tau\beta
$$

が一度に得られる。

続いて

```lean
let alpha : GoldenInt := ⟨p.M, p.N⟩
```

とし、`alpha` を packet の整数座標に固定する。

### 3. `α` のノルムを入力 packet から読む

入力 packet の `p.golden_eq` を 0172 bridge で `goldenNorm` へ移し、

```lean
have hnormAlpha : goldenNorm alpha = 5 * (p.powerSplit.b : ℤ) ^ 5 := by
  simpa [alpha, goldenNorm_eq_GoldenNorm] using p.golden_eq
```

を得る。

すなわち

$$
N(\alpha)=5b^5.
$$

### 4. `β` のノルムが `b^5` であることを証明する

`α=τβ` とノルムの乗法性から

$$
N(\alpha)=N(\tau)N(\beta)=5N(\beta)
$$

である。一方、前段から

$$
N(\alpha)=5b^5.
$$

したがって整数環で 5 を消去して

$$
N(\beta)=b^5
$$

を得る。

Lean proof では `goldenNorm_mul goldenTau beta` と 0184 `goldenNorm_tau` を使い、`omega` で最終の整数 cancel を処理する。

### 5. `β.snd` の exact five-adic 形を得る

`hbeta` の座標式からまず

$$
5\,\beta_{\mathrm{snd}}=-(M-2N)
$$

を導く。

次に入力 packet の `p.tenth_boundary` を使って

$$
M-2N=5^8a^{10}
$$

の形へ置き換え、`5 ≠ 0` による cancellation を行って

$$
\beta_{\mathrm{snd}}=-5^7a^{10}
$$

を得る。

source では

```lean
apply (mul_left_cancel₀ (by norm_num : (5 : ℤ) ≠ 0))
```

を使い、両辺へ 5 を掛けた等式を証明してから cancel する。

### 6. `5 ∤ b` を 0232 から継承する

```lean
have h5b : ¬ 5 ∣ p.powerSplit.b := five_not_dvd_powerSplit_b p
```

により 0232 の結果をそのまま packet 構築へ取り込む。

### 7. `5 ∤ N(β)` を証明する

仮に

$$
5\mid N(\beta)
$$

とする。`hnormBeta` により

$$
5\mid b^5
$$

となるので、5 の素性から

$$
5\mid b
$$

を得る。これは `h5b` に矛盾する。

Lean では整数側の divisibility を `Prime.dvd_of_dvd_pow` で処理し、最後に

```lean
exact_mod_cast
```

で `ℤ` 上の `5 ∣ (b : ℤ)` を `ℕ` 上の `5 ∣ b` へ戻している。

### 8. `τ ∤ β` をノルムで排除する

最後に、仮に

$$
\beta=\tau\gamma
$$

ならばノルム乗法性と `N(τ)=5` により

$$
N(\beta)=5N(\gamma),
$$

従って

$$
5\mid N(\beta)
$$

となる。これは直前の `h5norm` に矛盾する。

source は非常に短く、

```lean
have htau : ¬ ∃ gamma : GoldenInt, beta = goldenMul goldenTau gamma := by
  rintro ⟨gamma, hgamma⟩
  apply h5norm
  use goldenNorm gamma
  rw [hgamma, goldenNorm_mul, goldenNorm_tau]
```

で閉じる。

### 9. structure を組み立てる

最後に、ここまで得た witness と certificate を

```lean
exact ⟨{
  exceptional := p
  alpha := alpha
  beta := beta
  k := k
  alpha_eq := rfl
  linear_eq := hk
  alpha_eq_tau_mul := halpha
  beta_eq := hbeta
  beta_norm := hnormBeta
  beta_snd := hsnd
  five_not_dvd_b := h5b
  five_not_dvd_beta_norm := h5norm
  tau_not_dvd_beta := htau }⟩
```

という形で 0231 structure に詰め、`Nonempty` witness として返す。

## Lean 固有の処理

本 theorem は複数の domain 境界をまたぐため、Lean 固有の処理が比較的多い。

1. `let A : ℤ := ...` と `dsimp [A]` により局所変数を導入し、非線形整数式を `nlinarith` に渡している。
2. `Prime.dvd_of_dvd_pow` で平方・第五冪から素因子 divisibility を引き戻している。
3. `rcases` で 0186 の multiple existential witness を一度に展開している。
4. `simpa [alpha, goldenNorm_eq_GoldenNorm] using p.golden_eq` で旧二変数 norm API と `GoldenInt` norm API を橋渡ししている。
5. `mul_left_cancel₀` により整数 `5` の非零性を明示して cancellation を行う。
6. `exact_mod_cast` で `ℤ` と `ℕ` の divisibility statement を移送している。
7. 最終的な `Nonempty` は explicit structure literal を `⟨...⟩` で包んで構築する。

数学的には一本の ramifier stripping argument だが、Lean では整数・自然数・黄金整数・existential packet の各層を明示的に接続している点が特徴である。

## 冗長・重複箇所

### 1. `Nonempty` + `Classical.choice` の二段構成

本 theorem の直後には

```lean
noncomputable def signedGoldenRamifierStrippedPacket_of_exceptional ... :=
  Classical.choice
    (nonempty_signedGoldenRamifierStrippedPacket_of_exceptional p)
```

がある。

つまり「存在証明」と「選択された object」の二層構成になっている。これは proof / data を分離する標準的な設計だが、constructor が実際にはすべて明示的 witness から作られているため、直接 `noncomputable def` または computable `def` として構成できる余地があるかは検討可能である。

### 2. `5 ∤ b` と `5 ∤ N(β)` の双方を packet に保持

`N(β)=b^5` が field として存在するため、`5 ∤ b` から `5 ∤ N(β)` は導出可能である。両方を packet に保存するのは論理的には冗長だが、downstream で norm-side certificate を即利用できる利点がある。

### 3. `τ ∤ β` も `5 ∤ N(β)` から導出可能

`N(τ)=5` と norm multiplicativity があるため、`tau_not_dvd_beta` も `five_not_dvd_beta_norm` から一般的に導ける。これも packet を consumer-friendly にするための cached theorem field とみなせる。

## 最適化候補

1. **ramifier stripping の一般補題化**
   - `α=τβ`、`N(τ)=p`、`p∤N(β)` から `τ∤β` を導く generic lemma を作れば末尾の proof を再利用できる。

2. **norm primitive chain の helper 化**
   - `N(β)=b^5` と `5∤b` から `5∤N(β)` を導く部分を独立 lemma にできる。

3. **packet field の最小化**
   - `five_not_dvd_beta_norm` と `tau_not_dvd_beta` を theorem として外出しし、structure には primitive data だけを保持する設計と比較できる。

4. **explicit constructor 化**
   - witness `k`,`beta` が 0186 由来 existential であるため現状は choice layer が自然だが、factor extraction を function として再設計すれば `Classical.choice` を減らせる可能性がある。

5. **valuation API との比較**
   - mod 25 と素因子 divisibility の明示 chain を `padicValNat` / valuation 系で表現できる可能性がある。ただし現行 proof の方が依存が浅く監査しやすい利点も大きい。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem が直接利用する主要な Mathlib 表面は次の通りである。

- `Prime.dvd_of_dvd_pow`
- `mul_left_cancel₀`
- `exact_mod_cast`
- `nlinarith`
- `omega`
- `ring`
- `norm_num`
- `Nonempty`
- existential / conjunction elimination

一方、`GoldenInt`、`goldenNorm_mul`、`goldenNorm_tau`、0186 factor extraction などは DkMath 側の上流依存である。

宣言単独の最小 import は `Mathlib` 全体より小さくできる可能性が高いが、`SignedGoldenRamifierStripped.lean` module 全体では five-adic packet、整数 divisibility、黄金整数 arithmetic を横断するため、正確な import 最小化には Lean build による検証が必要である。今回は build を行わないので候補としてのみ記録する。

## Comparator challenge 化の可否

適している。0233 は proof architecture の選択肢が多い。

比較候補は次の通り。

- A: 現行の explicit divisibility + norm + coordinate construction
- B: valuation API を中心にした ramifier stripping
- C: `Associated` / prime element / gcd API を使った Euclidean-domain 的構成
- D: packet field を最小化し、derived certificate を theorem として外出しする設計
- E: `Classical.choice` を減らす explicit factor extraction function 設計

比較軸は proof 長、依存深度、computability、数学的 provenance、downstream API の使いやすさ、Lean elaboration の安定性、five-adic argument の監査性である。

特に A と C の比較は、0230 で完成した `EuclideanDomain GoldenInt` をどこまで積極的に使うべきかを測るよい Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` generated section である。

今回 source から、0232 の直後に本 private theorem があり、その直後に

```lean
noncomputable def signedGoldenRamifierStrippedPacket_of_exceptional ... :=
  Classical.choice
    (nonempty_signedGoldenRamifierStrippedPacket_of_exceptional p)
```

が続くことを確認した。

対象ブランチには日本語・英語 PDF が存在することはこれまでの museum 作業で確認されているが、今回 GitHub code search が一時的に 502 を返し、PDF の具体的ページ・節番号は再特定していない。そのためページ番号は推測しない。

## 次に読むべき宣言

依存順の次は **0234 `signedGoldenRamifierStrippedPacket_of_exceptional`** である。

```lean
noncomputable def signedGoldenRamifierStrippedPacket_of_exceptional
    {u v w : ℕ} (p : SignedSquareGoldenExceptionalPacket u v w) :
    SignedGoldenRamifierStrippedPacket u v w :=
  Classical.choice
    (nonempty_signedGoldenRamifierStrippedPacket_of_exceptional p)
```

0233 が packet の存在を証明し、0234 はその `Nonempty` proof から `Classical.choice` によって一つの packet を標準代表として選ぶ。ここで存在 theorem から downstream が直接参照できる object-level API へ移る。
