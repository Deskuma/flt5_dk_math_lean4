# 0232 — `five_not_dvd_powerSplit_b`

## Lean の型

```lean
private theorem five_not_dvd_powerSplit_b
    {u v w : ℕ} (p : SignedSquareGoldenExceptionalPacket u v w) :
    ¬ 5 ∣ p.powerSplit.b := by
  intro h5b
  have h25 : 25 ∣ p.powerSplit.fiveAdic.residual := by
    rcases h5b with ⟨c, hc⟩
    use 5 ^ 4 * c ^ 5
    rw [p.powerSplit.residual_eq, hc]
    ring
  have hzero := Nat.mod_eq_zero_of_dvd h25
  rw [p.powerSplit.fiveAdic.residual_mod_twentyFive] at hzero
  omega
```

これは `private theorem` であり、`SignedSquareGoldenExceptionalPacket` に含まれる exact five-adic power split の基底 `b` が 5 で割れないことを証明する。

## 数学的主張

主張は単純に

$$
5\nmid b
$$

である。

ただし証明の情報源は単純な gcd 条件ではなく、packet が保持する five-adic residual の modulo 25 certificate である。

`powerSplit.residual_eq` により residual は概念的に

$$
R=5^5 b^5
$$

型の明示式を持つ。もし仮に

$$
5\mid b
$$

なら $b=5c$ と書けるため、residual にはさらに 5 の冪が入り、特に

$$
25\mid R
$$

が従う。

一方 packet の `residual_mod_twentyFive` は residual の mod 25 値が 0 ではない特定値であることを保証している。したがって `25 ∣ residual` から得られる

$$
R\equiv0\pmod{25}
$$

と衝突し、矛盾となる。

つまり本 theorem は、five-adic residual に残された mod 25 の情報を、第五冪 base `b` の **5-primitive 性** へ変換する。

## 証明全体での役割

0231 `SignedGoldenRamifierStrippedPacket` は field

```lean
five_not_dvd_b : ¬ 5 ∣ exceptional.powerSplit.b
```

を要求する。本 theorem は、その field を実際に埋めるための最初の private certificate である。

直後の `nonempty_signedGoldenRamifierStrippedPacket_of_exceptional` では

```lean
have h5b : ¬ 5 ∣ p.powerSplit.b := five_not_dvd_powerSplit_b p
```

として直接使われる。

その後、`beta_norm = b^5` と組み合わせて

$$
5\nmid N(\beta)
$$

を導き、さらにもし

$$
\beta=\tau\gamma
$$

なら `N(τ)=5` により $5∣N(β)$ となることから矛盾し、

$$
\tau\nmid\beta
$$

を得る。

したがって 0232 は、単に `5 ∤ b` を示すだけでなく、stripped packet の

$$
5\nmid b
\Longrightarrow
5\nmid N(\beta)
\Longrightarrow
\tau\nmid\beta
$$

という **ramifier-strippedness chain の起点** である。

さらに後続の conjugate-coprime / unit-sector elimination でも `five_not_dvd_b` が packet invariant として再利用されるため、exceptional branch 全体の five-adic primitive condition を支える。

## 直接依存する定義・補題

直接依存する主な要素は次の通りである。

- `SignedSquareGoldenExceptionalPacket`
- packet 内の `powerSplit`
- `p.powerSplit.b`
- `p.powerSplit.residual_eq`
- `p.powerSplit.fiveAdic.residual`
- `p.powerSplit.fiveAdic.residual_mod_twentyFive`
- `Nat.mod_eq_zero_of_dvd`
- `ring`
- `omega`

証明は `GoldenInt` や `goldenNorm` を直接使わない。完全に整数・自然数側の five-adic residual arithmetic だけで閉じている。

## 証明の流れ

### 1. 反証法で `5 ∣ b` を仮定する

```lean
intro h5b
```

目標 `¬ 5 ∣ b` を証明するため、

$$
5\mid b
$$

を仮定する。

### 2. residual が 25 で割れることを構成する

```lean
have h25 : 25 ∣ p.powerSplit.fiveAdic.residual := by
  rcases h5b with ⟨c, hc⟩
  use 5 ^ 4 * c ^ 5
  rw [p.powerSplit.residual_eq, hc]
  ring
```

`h5b` から witness `c` を取り出して $b=5c$ と置く。

その後 residual の明示式へ代入し、25 の商 witness として

```lean
5 ^ 4 * c ^ 5
```

を与える。最後の `ring` は、residual の冪積を展開して

$$
R=25\cdot(5^4c^5)
$$

という多項式恒等式を閉じる。

### 3. 25-整除を mod 25 の 0 条件へ変換する

```lean
have hzero := Nat.mod_eq_zero_of_dvd h25
```

これにより

$$
R\bmod25=0
$$

を得る。

### 4. packet の residual mod 25 certificate と衝突させる

```lean
rw [p.powerSplit.fiveAdic.residual_mod_twentyFive] at hzero
omega
```

既知の residual modulo 25 値で `hzero` を書き換えると、自然数上の明示的な不可能等式になる。最後は `omega` が矛盾を閉じる。

## Lean 固有の処理

`rcases h5b with ⟨c, hc⟩` は `Nat` の整除 witness を直接取り出す。ここで `hc` の向きは Mathlib の `Dvd.dvd` witness 形式に依存するが、その後 `rw [hc]` で `b` を `5*c` に置換できる形になっている。

`use 5 ^ 4 * c ^ 5` は `25 ∣ residual` の existential quotient を明示的に構成している。これは単に divisibility tactic に任せるより、residual がどの程度 5-adic valuation を増やすかを proof term 上でも可視にする。

`Nat.mod_eq_zero_of_dvd h25` は divisibility を congruence 条件へ落とす標準 bridge である。最終段の `omega` は線形 Presburger arithmetic を担当し、mod 25 certificate を具体値へ rewrite した後の矛盾を処理する。

## 冗長・重複箇所

本 theorem の five-adic 内容は、より一般には

$$
5\mid b
\Longrightarrow
25\mid residual
$$

という補題と、

$$
residual\not\equiv0\pmod{25}
$$

という packet invariant の組合せである。

もし同型の議論が他の residual base にも現れるなら、`five_dvd_base_implies_twentyFive_dvd_residual` のような一般 helper を切り出す余地がある。

また `5 ^ 4 * c ^ 5` という quotient witness は residual の具体的指数に強く依存するため、valuation API を使えば概念的には短くできる可能性がある。ただし現行 proof は完全に elementary arithmetic であり、依存が軽く監査しやすい利点がある。

## 最適化候補

1. **five-adic valuation 補題へ抽象化する**
   - `5 ∣ b` なら residual の 5-adic valuation が少なくとも 2 増える、という形に一般化する。

2. **mod 25 contradiction helper を作る**
   - `25 ∣ n` と既知の `n % 25 = r`, `r ≠ 0` から矛盾を出す小補題を再利用できる。

3. **packet invariant を `¬ 25 ∣ residual` として直接保持する**
   - downstream が mod 値そのものを必要としないなら、より semantic な certificate に変換して packet に格納する案がある。

4. **現行の explicit witness proof を維持する**
   - valuation machinery を導入せず、どの 5 の冪が quotient に残るかを明示できるので、監査性では現行案が強い。

現時点では proof は短く明瞭で、局所最適化の優先度は低い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が直接必要とする Mathlib 表面は比較的小さい。

- `Nat` の整除
- `Nat.mod_eq_zero_of_dvd`
- `ring`
- `omega`

一方 `SignedGoldenRamifierStripped.lean` 全体では GoldenInt、norm、prime divisibility、`exact_mod_cast` なども使うため、module 単位の最小 import は本 theorem 単独より広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行の explicit divisibility witness + mod 25 contradiction
- B: `Nat.factorization` / valuation 系 API を使う proof
- C: `Nat.ModEq` を中心にした proof
- D: packet に `¬ 25 ∣ residual` を直接保持して一段で contradiction を出す proof

比較軸は、proof 長、import 依存、five-adic 意味の可視性、計算量、一般化可能性、Lean tactic 依存度である。

特に A と B の比較は、「初等的な witness arithmetic」と「valuation abstraction」のどちらが FLT5 監査に向くかを見るよい Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` generated section である。

正本 source では 0231 `SignedGoldenRamifierStrippedPacket` の直後に本 `private theorem` が置かれ、その後 `nonempty_signedGoldenRamifierStrippedPacket_of_exceptional` が本 theorem を利用して `five_not_dvd_b` field を埋める。

対象ブランチには日本語・英語 PDF も存在するが、本 private theorem に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0233 `nonempty_signedGoldenRamifierStrippedPacket_of_exceptional`** である。

```lean
private theorem nonempty_signedGoldenRamifierStrippedPacket_of_exceptional
    {u v w : ℕ} (p : SignedSquareGoldenExceptionalPacket u v w) :
    Nonempty (SignedGoldenRamifierStrippedPacket u v w) := by
  ...
```

0232 が `5 ∤ b` という five-adic primitive certificate を準備したので、0233 では `k`, `beta`, norm equation, second-coordinate formula, `5 ∤ N(beta)`, `tau ∤ beta` をすべて構成し、0231 の structure が実際に inhabited であることを証明する。これは ramifier stripping argument 本体の constructor theorem である。
