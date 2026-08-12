# 0084 — `SignedFiveAdicPowerSplit.five_not_dvd_b`

## Lean の型

```lean
theorem SignedFiveAdicPowerSplit.five_not_dvd_b
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) : ¬ 5 ∣ s.b := by
  intro h5b
  have h25 : 25 ∣ s.fiveAdic.residual := by
    rcases h5b with ⟨c, hc⟩
    use 5 ^ 4 * c ^ 5
    rw [s.residual_eq, hc]
    ring
  have hzero := Nat.mod_eq_zero_of_dvd h25
  rw [s.fiveAdic.residual_mod_twentyFive] at hzero
  omega
```

## 数学的主張

`SignedFiveAdicPowerSplit` では residual が

$$
\mathrm{residual}=5b^5
$$

と分解される。本定理は、その第五冪基底 `b` にさらに 5 が残っていないこと、すなわち

$$
5\nmid b
$$

を示す。

これは `residual` の 5-adic valuation がちょうど 1 であることを、power-split 後の座標 `b` に読み替えた主張と見なせる。

## 証明全体での役割

0083 `SignedFiveAdicPowerSplit` は

$$
\mathrm{carrier}=5^4a^5,\qquad
\mathrm{residual}=5b^5,\qquad
\mathrm{distinguished}=5ab
$$

という exact power split を保持する。しかし `residual = 5b^5` だけでは `b` 自身が 5 を含む可能性を排除していない。

本定理で $5\nmid b$ を確定することで、residual から ramified prime 5 を一度だけ剥がした後の部分が 5 と互いに素であることが保証される。直後の `SignedFiveAdicPowerSplit.coprime_scaled_a20_b5` はこの事実を使って、5 の高い冪を含む左因子と $b^5$ の coprimality を構築する。

## 直接依存する定義・補題

- `SignedFiveAdicPowerSplit`
  - 特に `s.residual_eq : s.fiveAdic.residual = 5 * s.b ^ 5`
- `SignedFiveAdicPacket.residual_mod_twentyFive`
  - `s.fiveAdic.residual % 25 = 5`
- `Nat.mod_eq_zero_of_dvd`
- `ring`
- `omega`

0083 より前の `GN5`、`SumGN5`、orientation 分岐、gcd 証明などには本定理は直接触れない。それらは `SignedFiveAdicPowerSplit` と `SignedFiveAdicPacket` の field に封じ込められている。

## 証明の流れ

1. 反証法ではなく、否定命題の導入として `h5b : 5 ∣ s.b` を仮定する。
2. `h5b` を `⟨c, hc⟩` と展開し、$b=5c$ を得る。
3. `s.residual_eq` に代入すると

$$
\mathrm{residual}=5(5c)^5=5^6c^5
$$

となるため、特に $25\mid\mathrm{residual}$ が従う。
4. `Nat.mod_eq_zero_of_dvd h25` から

$$
\mathrm{residual}\bmod25=0
$$

を得る。
5. packet が保持する

$$
\mathrm{residual}\bmod25=5
$$

で書き換えると $5=0$ という矛盾になり、`omega` で閉じる。

## Lean 固有の処理

`¬ 5 ∣ s.b` は関数型なので、`intro h5b` で divisibility witness を仮定する。

```lean
rcases h5b with ⟨c, hc⟩
```

で `Nat` の divisibility を具体的な積表示へ展開している。`use 5 ^ 4 * c ^ 5` は `25 ∣ residual` の witness を明示する部分であり、その後 `ring` が冪と積の正規化を処理する。

最後は `Nat.mod_eq_zero_of_dvd` により divisibility を剰余の等式へ変換し、既存 field `residual_mod_twentyFive` と衝突させる。`omega` が最終的な自然数算術の矛盾を閉じる。

## 冗長・重複箇所

後続 source には、同型の「$5\mid b$ を仮定して $25\mid residual$ を作り、`residual % 25 = 5` と衝突させる」証明が別 packet 層でも再出現する。したがって本定理のローカル証明は短いが、開発全体では同じ mod-25 obstruction が複数回複製されている。

また `SignedFiveAdicPacket` 自体は `residual_padicValNat : padicValNat 5 residual = 1` も保持しているため、valuation API を使えば $5\nmid b$ を別経路で導出できる可能性がある。ただし、その経路が現行 Mathlib API で本証明より短いかは未確認であり、ここは推測である。

## 最適化候補

最も自然なのは、次のような一般補題への抽象化である。

```lean
-- 概念形
theorem not_dvd_base_of_mul_pow_mod_sq
    (p x b n : ℕ)
    (hshape : x = p * b ^ n)
    (hmod : x % (p ^ 2) = p) :
    ¬ p ∣ b := ...
```

実際には素数条件、`n > 0`、`p > 1` などを適切に付ける必要がある。本 FLT5 固有版では $p=5$, $n=5$ に固定されているため、現在の三行程度の算術証明を保つ方が可読性では優れる可能性も高い。

もう一つの候補は、`residual_mod_twentyFive` ではなく `residual_padicValNat = 1` を主要 API として使う設計との比較である。mod 25 route は elementary で kernel trace が短く、valuation route は後段の 5-adic reasoning との統一性が高い。

## 必要 Mathlib import と import 最適化候補

博物館ブランチの standalone artifact は `import Mathlib` で構築されているため、本定理が `Mathlib` 全体で利用可能であることは確認できる。

本証明で直接見えている機能は少なくとも `Nat` の divisibility/mod、`ring`、`omega` である。したがって最小 import は `Mathlib` より大幅に縮小できるはずだが、分割元 `SignedFiveAdicPowerSplit.lean` の正確な import 列をこの博物館ブランチ上で独立確認できていないため、具体的な最小 import 名は断定しない。

最適化するなら、まず source module の import graph を確認し、`Nat` の divisibility/mod と `Mathlib` tactics `Ring` / `Omega` に必要な module のみに落とせるかを Lean build で検証するのが安全である。本回では Lean build は行わない。

## Comparator challenge 化の可否

可能。小さく独立した比較課題に向いている。

比較案は次の三方式である。

1. 現行の mod 25 証明。
2. `padicValNat 5 residual = 1` から直接導く valuation 証明。
3. 一般補題 `x = p*b^n` と `x % p^2 = p` から `p ∤ b` を導く抽象版。

評価軸は proof length、必要 import、算術 tactic 依存度、再利用性、後段 API との整合性がよい。

## PDF との対応

既存の日英 PDF は本開発の叙述的根拠として扱うが、今回 GitHub code search が一時的に 502 を返し、private/短補題相当の PDF 内位置を一意に特定できなかった。そのため PDF のページ番号や節番号は推測で付与していない。

本記事の形式的主張と証明コードの最終根拠は、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` にある実際の Lean 宣言である。

## 次に読むべき定理

次は

```lean
theorem SignedFiveAdicPowerSplit.coprime_scaled_a20_b5
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    Nat.Coprime (5 ^ 15 * s.a ^ 20) (s.b ^ 5) := by
  ...
```

を読むべきである。

本定理の $5\nmid b$ と `s.coprime_a_b` を組み合わせ、

$$
\gcd(5^{15}a^{20},b^5)=1
$$

を構築する。これは ramifier 5 を剥がした後の因子分離を、後続の square/golden bridge が使える形へ整える補題である。
