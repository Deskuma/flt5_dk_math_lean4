# 0027 — `fifth_power_factor_split`

## 宣言

```lean
theorem fifth_power_factor_split
    {g n x : ℕ} (hcop : Nat.Coprime g n) (hbody : g * n = x ^ 5) :
    (∃ a : ℕ, g = a ^ 5) ∧ (∃ b : ℕ, n = b ^ 5) := by
  have hunit : IsUnit (GCDMonoid.gcd g n) := by
    simpa [gcd_eq_nat_gcd, Nat.Coprime, Nat.isUnit_iff] using hcop
  constructor
  · exact exists_eq_pow_of_mul_eq_pow hunit hbody
  · have hunit' : IsUnit (GCDMonoid.gcd n g) := by
      simpa [gcd_comm] using hunit
    exact exists_eq_pow_of_mul_eq_pow hunit' (by simpa [mul_comm] using hbody)
```

## Lean の型

この定理は、自然数 `g` と `n` が互いに素であり、その積が自然数 `x` の第五冪であるとき、`g` と `n` がそれぞれ自然数の第五冪であることを返す。

```lean
Nat.Coprime g n →
  g * n = x ^ 5 →
  ((∃ a : ℕ, g = a ^ 5) ∧ (∃ b : ℕ, n = b ^ 5))
```

## 数学的主張

仮定は

$$
\gcd(g,n)=1,
\qquad
 gn=x^5
$$

である。互いに素な二因子は素因数を共有しない。積 `gn` に現れる各素数の指数は第五冪なので $5$ の倍数であり、その指数は `g` 側または `n` 側のどちらか一方に全て属する。したがって両因子の各素数指数も $5$ の倍数となり、ある $a,b\in\mathbb N$ が存在して

$$
g=a^5,
\qquad
n=b^5
$$

となる。

## 証明全体での役割

Branch B では前号により

$$
\gcd\bigl(z-y,GN5(z-y,y)\bigr)=1
$$

が得られる。また第五冪方程式と差の因数分解から

$$
(z-y)GN5(z-y,y)=x^5
$$

を得る。本定理はこの二事実を入力として、gap と `GN5` をそれぞれ完全第五冪へ分離する一般エンジンである。

本定理は FLT5 固有の多項式を知らない。互いに素な積と冪という一般的な `GCDMonoid` の構造だけを扱うため、Reduction 層と後続の Branch B normal form の境界に位置する。

## 直接依存する定義・補題

1. `Nat.Coprime`
   - 自然数 `g,n` の gcd が `1` であることを表す。
2. `GCDMonoid.gcd`
   - 一般的な gcd API。Mathlib の冪分離定理が要求する形へ合わせるために使う。
3. `gcd_eq_nat_gcd`
   - 一般 gcd と `Nat.gcd` の橋。
4. `Nat.isUnit_iff`
   - 自然数が単元であることと値が `1` であることを結ぶ。
5. `exists_eq_pow_of_mul_eq_pow`
   - gcd が単元で、積が冪なら、一方の因子も同じ指数の冪であることを与える Mathlib 補題。
6. `gcd_comm`、`mul_comm`
   - 第二因子へ同じ一般補題を適用するため、因子順を反転する。

## 証明の流れ

1. `hcop : Nat.Coprime g n` を、一般 gcd が単元であるという形へ変換する。

```lean
have hunit : IsUnit (GCDMonoid.gcd g n) := by
  simpa [gcd_eq_nat_gcd, Nat.Coprime, Nat.isUnit_iff] using hcop
```

2. 結論の連言を `constructor` で二つに分ける。
3. 第一因子について `exists_eq_pow_of_mul_eq_pow hunit hbody` を直接使い、`g=a^5` を得る。
4. 第二因子用に gcd の順序を交換して `hunit' : IsUnit (gcd n g)` を作る。
5. 積の順序も `n*g=x^5` へ交換し、同じ Mathlib 補題を再適用して `n=b^5` を得る。

## Lean 固有の処理

### `Nat.Coprime` から `IsUnit gcd` への変換

中心的な Mathlib 補題は `Nat.Coprime g n` そのものではなく、`IsUnit (GCDMonoid.gcd g n)` を要求する。そのため、

```lean
simpa [gcd_eq_nat_gcd, Nat.Coprime, Nat.isUnit_iff] using hcop
```

で三つの表現を一度に正規化している。

### 一方向の補題を左右へ再利用

`exists_eq_pow_of_mul_eq_pow` は積の左因子について結論を返す。右因子へ適用するため、`gcd_comm` と `mul_comm` で引数順を反転している。数学的には対称な主張だが、Lean API 上は明示的な交換が必要である。

### 指数 `5` の推論

補題適用時に指数を明示していない。`hbody` の右辺 `x ^ 5` と目標 `g = a ^ 5`、`n = b ^ 5` から Lean が指数を推論する。

## 冗長・重複箇所

左右の因子に対して同じ Mathlib 補題を二度適用しており、第二枝では gcd と積の可換性を個別に整えている。これは論理的重複ではあるが、証明は短く明確である。

`hunit'` を独立した `have` にせず、第二の適用内へ埋め込むことも可能だが、現在の形は型変換の失敗箇所を局所化し、可読性が高い。

## 最適化候補

1. `exists_eq_pow_of_mul_eq_pow` の左右両因子版、または連言を直接返す Mathlib 補題が存在するなら、二度の適用を一回へまとめられる可能性がある。これは未検証である。
2. `hunit'` を `by simpa [gcd_comm] using hunit` としてインライン化できるが、証明速度への実質的効果はない。
3. 指数を一般化して、任意の `k` に対する `coprime_power_factor_split` を DkMath の共通補題として置き、本定理を `k=5` の特殊化にする設計が考えられる。これは再利用性の高い未検証提案である。
4. 定理名は第五冪専用で内容を正確に表しており、FLT5 読解経路では現状が分かりやすい。

## 必要 Mathlib import と import 最適化候補

standalone 版は `import Mathlib` で検証されているため、最小 import は確定していない。

本証明が直接用いるのは、自然数の gcd・coprime、`GCDMonoid`、単元、冪、`exists_eq_pow_of_mul_eq_pow`、および可換性補題である。個別モジュールの import を確認したうえで、`Mathlib.Algebra.GCDMonoid.Finset` や自然数 gcd 関連モジュールなどへ縮小できる可能性があるが、正確なモジュール名と十分性は Lean ビルドを行っていないため未検証である。

## Comparator challenge 化の可否

非常に適している。数学的内容と Lean API 変換の双方を比較できる。

### 課題案

```lean
{g n x : ℕ}
(hcop : Nat.Coprime g n)
(hbody : g * n = x ^ 5)
⊢ (∃ a : ℕ, g = a ^ 5) ∧ (∃ b : ℕ, n = b ^ 5)
```

比較候補は次の通り。

1. 現行の `exists_eq_pow_of_mul_eq_pow` 再利用版。
2. 素因数指数や `padicValNat` を展開する版。
3. 左右対称補題を先に作ってから適用する版。
4. 指数を一般化した補題を作り、`5` へ特殊化する版。

評価軸は、証明長、一般性、Mathlib API の理解、型変換の明示性、ビルドコスト、将来の Mathlib 変更への耐性である。

## 根拠と推測の区別

宣言の型、証明本体、使用補題、直後に `branchB_fifth_power_factor_split` が続くことはリポジトリ内 Lean コードで確認した。素因数指数による数学的説明は標準的な解釈である。最小 import、左右同時版補題の存在、任意指数への一般化案は未検証である。

## 次に読むべき定理

```lean
DkMath.FLT.Five.branchB_fifth_power_factor_split
```

`CounterexamplePack`、Branch B 条件、第五冪差の因数分解、本号の一般分離定理を合成し、具体的に

$$
z-y=a^5,
\qquad
GN5(z-y,y)=b^5
$$

を得る Branch B の exact elementary normal form である。