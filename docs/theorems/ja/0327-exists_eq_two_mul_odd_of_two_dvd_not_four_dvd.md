# 0327 — `exists_eq_two_mul_odd_of_two_dvd_not_four_dvd`

## 宣言種別

これは **`private theorem`** である。

`SignedGoldenZeroSectorFactorization.lean` 内部だけで用いられる局所補題であり、公開 API ではない。

## Lean の型

```lean
private theorem exists_eq_two_mul_odd_of_two_dvd_not_four_dvd
    {n : ℕ} (h2 : 2 ∣ n) (h4 : ¬ 4 ∣ n) :
    ∃ m : ℕ, n = 2 * m ∧ Odd m := by
  rcases h2 with ⟨m, hm⟩
  refine ⟨m, hm, Nat.not_even_iff_odd.mp ?_⟩
  rw [even_iff_two_dvd]
  intro h2m
  rcases h2m with ⟨k, hk⟩
  apply h4
  refine ⟨k, ?_⟩
  omega
```

型としては

```lean
{n : ℕ} → 2 ∣ n → ¬ 4 ∣ n → ∃ m : ℕ, n = 2 * m ∧ Odd m
```

である。

## 数学的主張

自然数 `n` が

$$
2 \mid n,
$$

かつ

$$
4 \nmid n
$$

を満たすなら、ある自然数 `m` が存在して

$$
n = 2m
$$

かつ `m` は奇数である。

すなわち 2-adic valuation の言葉では、`n` に含まれる 2 の指数がちょうど 1 であるとき、その唯一の 2 を取り除いた商が奇数になるという基本事実である。

## FLT5 証明全体での役割

直前の 0326 は「奇数因子に共通奇素因子がないなら互いに素」という bridge を与えた。本 theorem はそれに先立つ二進正規化を担う。

零セクター反転 packet では

$$
A_0 B_0 = 4Q^5
$$

と

$$
B_0 = A_0 + 8d^5
$$

が得られている。後続 theorem `GoldenZeroSectorInversionPacket.odd_factor_halves` は、条件から `A0` と `B0` がともに 2 で割れ、しかし 4 では割れないことを示した後、本 theorem をそれぞれへ適用して

$$
A_0 = 2A_1, \qquad B_0 = 2B_1
$$

かつ

$$
A_1, B_1 \text{ は奇数}
$$

を得る。

したがって本 theorem は「2 の指数がちょうど 1」という可除性情報を、後続で直接利用できる `2 × odd` 形式へ変換する局所的な正規化 lemma である。

## 直接依存する定義・補題

### `Nat.not_even_iff_odd`

`¬ Even m ↔ Odd m` を与える。証明では `.mp` を使い、`¬ Even m` を示す問題へ変換する。

### `even_iff_two_dvd`

`Even m ↔ 2 ∣ m` を与える。`rw [even_iff_two_dvd]` により、否定すべき偶性を具体的な 2 の可除性へ変換する。

### `omega`

最後に、

```lean
hm : n = 2 * m
hk : m = 2 * k
```

から

```lean
n = 4 * k
```

を算術的に閉じるために使われる。

### 仮定 `h2`, `h4`

`h2 : 2 ∣ n` が商 `m` を生成し、`h4 : ¬ 4 ∣ n` がその `m` の偶数可能性を排除する。

## 証明の流れ

1. `h2 : 2 ∣ n` を `rcases` し、`n = 2 * m` を満たす witness `m` を得る。
2. 求める witness として同じ `m` を採用する。
3. 残る目標 `Odd m` を `Nat.not_even_iff_odd.mp` により `¬ Even m` へ変換する。
4. `even_iff_two_dvd` で `Even m` を `2 ∣ m` に書き換える。
5. `2 ∣ m` と仮定し、`m = 2 * k` となる witness `k` を取り出す。
6. すると `n = 2m = 4k` なので `4 ∣ n` となる。
7. これは `h4 : ¬ 4 ∣ n` に矛盾する。
8. よって `m` は偶数ではなく、したがって奇数である。

数学的には

$$
2 \mid n,\quad 4 \nmid n
\Longrightarrow v_2(n)=1
\Longrightarrow n=2m,\quad 2\nmid m
\Longrightarrow m\text{ odd}
$$

という一本道である。

## Lean 固有の処理

### `rcases h2 with ⟨m, hm⟩`

Lean の `a ∣ b` は witness を持つ存在命題として扱えるため、可除性仮定から商 `m` と等式 `hm` を直接取り出している。

### `refine ⟨m, hm, ...⟩`

存在 witness、積表示、奇数性を一度に組み立てる。構造が単純なので tactic を細かく分割するより見通しがよい。

### `Nat.not_even_iff_odd.mp`

`Odd m` を直接構築するのではなく、`m` が偶数でないことを示してから標準同値で戻す。今回の仮定 `¬ 4 ∣ n` と非常に相性がよい証明形である。

### `rw [even_iff_two_dvd]`

抽象的な `Even m` を `2 ∣ m` へ落とすことで、可除性 witness を再び `rcases` できる形にしている。

### `omega`

最後の等式変形を自動化する。ここで必要なのは線形算術だけであり、数論的な推論はすでに終わっている。

## 冗長・重複箇所

証明は十分に短く、大きな冗長性はない。

ただし最後の

```lean
rcases h2m with ⟨k, hk⟩
apply h4
refine ⟨k, ?_⟩
omega
```

は、積の結合・交換を利用して `dvd_mul` 系 lemma だけで `4 ∣ n` を構築できる可能性がある。その場合 `omega` 依存を除去できるかもしれない。ただし具体的に最短となる Mathlib lemma の組み合わせは本実行では Lean build を行っていないため **未確認** である。

また「`2 ∣ n` かつ `¬ 4 ∣ n` なら半分は奇数」という内容は一般性が高い。Mathlib に既存の同値 lemma が存在する可能性もあるが、本実行では完全な API 検索を行っていないため **未確認** である。

## 最適化候補

第一候補は、Mathlib に 2-adic valuation または `Even` / `Odd` に関する既存 lemma があれば、この theorem 自体をそれへの薄い wrapper にすることである。

第二候補は `omega` を除去し、可除性 lemma のみで

$$
2 \mid m \Longrightarrow 4 \mid 2m = n
$$

を示すことである。これは依存 tactic を減らし、proof term の意図をより数論的に明示できる可能性がある。

一方で現行証明は非常に読みやすく、局所 lemma としては十分に合理的である。短縮のために可読性を落とす必要は薄い。

## 必要 Mathlib import と import 最適化候補

確認できる正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem が直接必要とする主要 API は、

- 自然数の可除性 `∣`
- `Odd`, `Even`
- `Nat.not_even_iff_odd`
- `even_iff_two_dvd`
- `omega`

である。

したがって `Mathlib` 全体より狭い import に縮約できる可能性は高い。しかし exact minimal import は Lean build / import minimization を行っていないため **未確認** である。

## Comparator challenge 化の可否

**非常に適している。**

小さく自己完結しており、同じ主張を複数の表現で証明できる。

比較候補は、

1. 現行の `Even` / `Odd` bridge + `omega`。
2. 可除性 lemma のみを使い `omega` を除く証明。
3. 2-adic valuation を用いて `v₂(n)=1` から導く証明。
4. Mathlib に直接対応する既存 lemma があれば、その wrapper 証明。

評価軸は proof length、依存 tactic、可読性、Mathlib API への頑健性、数論的意味の明瞭さである。

## 次に読むべき宣言

次は

```lean
theorem GoldenZeroSectorInversionPacket.odd_factor_halves
    (p : GoldenZeroSectorInversionPacket) (hc : Odd p.source.c) :
    ∃ A1 B1 : ℕ,
      p.source.A0 = 2 * A1 ∧ Odd A1 ∧
      p.source.B0 = 2 * B1 ∧ Odd B1 := by
  ...
```

である。

これは今回の private theorem を `A0` と `B0` の双方へ実際に適用し、零セクターの自然数因子を

$$
A_0 = 2A_1,\qquad B_0 = 2B_1
$$

という奇数半因子へ分解する公開 theorem である。museum の依存順では **0328 `GoldenZeroSectorInversionPacket.odd_factor_halves`** として読むのが自然である。
