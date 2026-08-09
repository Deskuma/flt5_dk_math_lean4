# 0081 — `dvd_five_mul_left_pow_four_of_dvd_sum_of_dvd_sumGN5`

## Lean の型

```lean
private theorem dvd_five_mul_left_pow_four_of_dvd_sum_of_dvd_sumGN5
    {u v q : ℕ} (hqsum : q ∣ u + v) (hqres : q ∣ SumGN5 u v) :
    q ∣ 5 * u ^ 4 := by
  have hsumZ : (u : ZMod q) + (v : ZMod q) = 0 := by
    rw [← Nat.cast_add]
    exact (ZMod.natCast_eq_zero_iff (u + v) q).2 hqsum
  have hvZ : (v : ZMod q) = -(u : ZMod q) :=
    eq_neg_of_add_eq_zero_right hsumZ
  have hresZ : (SumGN5 u v : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff (SumGN5 u v) q).2 hqres
  apply (ZMod.natCast_eq_zero_iff (5 * u ^ 4) q).1
  by_cases h : v ≤ u
  · rw [SumGN5, if_pos h] at hresZ
    push_cast at hresZ ⊢
    rw [Nat.cast_sub h] at hresZ
    rw [hvZ] at hresZ
    ring_nf at hresZ ⊢
    exact hresZ
  · have huv : u ≤ v := Nat.le_of_not_ge h
    rw [SumGN5, if_neg h] at hresZ
    push_cast at hresZ ⊢
    rw [Nat.cast_sub huv] at hresZ
    rw [hvZ] at hresZ
    ring_nf at hresZ ⊢
    exact hresZ
```

## 数学的主張

自然数 $u,v,q$ について、$q$ が carrier $u+v$ と residual `SumGN5 u v` の双方を割るなら、

$$
q\mid 5u^4
$$

が従う。

証明の核心は法 $q$ で $u+v\equiv0$、したがって $v\equiv-u$ と置き、`SumGN5 u v` を法 $q$ で評価すると $5u^4$ と同じ剰余になることにある。仮定 $q\mid\mathrm{SumGN5}(u,v)$ によりその剰余は $0$ なので、$q\mid5u^4$ となる。

この補題自体は gcd が $5$ であるとはまだ言っていない。共通因子 $q$ の行き先を $5u^4$ に制限するための中間補題である。

## 証明全体での役割

0080 までで common five-adic packet の構築と Branch B への contradiction routing が整った。本補題から `SignedFiveAdicPowerSplit.lean` の層に入り、packet 内の carrier と residual の共通因子をさらに解析する。

直後の `signedFiveAdicPacket_gcd_eq_five` の sum source では

```lean
exact dvd_five_mul_left_pow_four_of_dvd_sum_of_dvd_sumGN5
  (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
```

として、$q=\gcd(u+v,\mathrm{SumGN5}(u,v))$ に本補題を適用する。その gcd は一方で $u$ と互いに素なので、$u^4$ の因子を除去して gcd が $5$ を割ることを導く。difference source には既存の `dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5` が対応している。

従って本補題は、sum orientation における gcd 上界 $\gcd(carrier,residual)\mid5$ を作るための局所 algebraic bridge である。

## 直接依存する定義・補題

- `SumGN5`
- `ZMod.natCast_eq_zero_iff`
- `eq_neg_of_add_eq_zero_right`
- `Nat.cast_add`
- `Nat.cast_sub`
- `Nat.le_of_not_ge`
- `push_cast`
- `ring_nf`

後続利用として `signedFiveAdicPacket_gcd_eq_five` が直接依存する。

数学的には `q ∣ u+v` と `q ∣ SumGN5 u v` だけを使い、`CounterexamplePack`、Fermat 方程式、coprimality、five-adic valuation は本補題の仮定には現れない。そのためかなり局所化された補題である。

## 証明の流れ

1. `hqsum : q ∣ u + v` を `ZMod q` 上の等式

   $$
   u+v=0
   $$

   に移す。
2. そこから

   $$
   v=-u
   $$

   を得る。
3. `hqres : q ∣ SumGN5 u v` を

   $$
   \mathrm{SumGN5}(u,v)=0\quad\text{in }\mathrm{ZMod}(q)
   $$

   へ移す。
4. 目標 $q\mid5u^4$ も `ZMod q` 上の $5u^4=0$ に変換する。
5. `SumGN5` は自然数減算を含む piecewise definition なので、`v ≤ u` とその否定で場合分けする。
6. 各 branch で `Nat.cast_sub` を安全に適用し、$v=-u$ を代入する。
7. `ring_nf` で residual の式と $5u^4$ を同一正規形へ落とし、既知の `hresZ` をそのまま目標にする。

## Lean 固有の処理

最大の Lean 固有点は `SumGN5` が `Nat` 上の差を使う piecewise definition であることじゃ。整数や環上の多項式なら単に $v=-u$ を代入すれば済むが、`Nat.cast_sub` は減算が実際の差として成立する順序証明を要求する。

そのため `by_cases h : v ≤ u` を行い、第一 branch では `Nat.cast_sub h`、第二 branch では `huv : u ≤ v` を作って `Nat.cast_sub huv` を使う。

また `ZMod.natCast_eq_zero_iff` は divisibility と modular vanishing の橋であり、本証明では入口と出口の双方で使われる。`push_cast` は自然数式を `ZMod q` 上の環式へ移し、`ring_nf` が最終的な polynomial normalization を担う。

`q = 0` を別処理していない点も興味深い。`ZMod q` と `ZMod.natCast_eq_zero_iff` の既存 API がこの一般形を受け持つため、proof script は $q>0$ を仮定せずに済んでいる。

## 冗長・重複箇所

二つの branch はほぼ同型で、異なるのは `SumGN5` の展開式と `Nat.cast_sub` に渡す順序証明だけである。

また difference orientation には既に

```lean
dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5
```

という対応補題がある。両者は「carrier と residual を割る共通因子を、5 倍の第四冪へ送る」という同じ gcd-control pattern を持つ。

したがって、局所的には branch duplication、より大域的には difference/sum orientation 間の pattern duplication が存在する。ただし `GN5` と `SumGN5` の定義形が異なるため、抽象化が本当に簡潔になるかは未検証である。

## 最適化候補

第一候補は `SumGN5` について先に合同式補題

$$
q\mid u+v
\Longrightarrow
\mathrm{SumGN5}(u,v)\equiv5u^4\pmod q
$$

を独立させることじゃ。そうすれば本補題は、その合同式と `hqres` から divisibility を取り出す薄い wrapper にできる。

第二候補は `v ≤ u` / `u ≤ v` の二 branch で共通する `push_cast`、代入、`ring_nf` のパターンを補助補題へ寄せること。ただし数行の削減のために API を増やし過ぎる危険もある。

第三候補は difference 側の既存補題と共通する abstract gcd-control lemma を設計することだが、これは `GN5` / `SumGN5` の residual polynomial をどのレベルで抽象化するかに依存するので、現時点では設計案に留める。

## 必要 Mathlib import と import 最適化候補

対象ブランチの生成 standalone `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用している。本補題が直接使う Mathlib 機能は主に `ZMod`、自然数 cast、`push_cast`、`ring_nf`、基本順序補題である。

概念的には `Mathlib.Data.ZMod.Basic`、cast 関連、ring normalization 関連の import が中心になると推測できる。ただし博物館ブランチ上の分割元 `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` の正確な import graph を今回確認できていないため、最小 import 集合は未検証である。`import Mathlib` からの削減候補は、分割モジュールを単独ビルドして確認すべき事項である。

## 既存 PDF との関係

数学的な内容は、$u+v$ の共通因子を使って sum residual を合同式で簡約し、共通因子を $5u^4$ 側へ制限する局所 gcd 議論である。具体的な Lean 型と proof script の一次根拠は対象ブランチの Lean source である。

既存の日英 PDF に本 private helper と一対一対応する定理番号・ページは今回確定できなかった。そのため PDF 固有の番号、文言、ページ対応は推測で補っていない。

## Comparator challenge 化の可否

かなり適している。少なくとも次の比較が可能である。

- 現行の `ZMod q` + case split + `ring_nf`
- `Nat.ModEq` を主表現として使う証明
- `SumGN5` の一般合同式を先に補題化してから divisibility へ戻す証明
- difference/sum の gcd-control を共通抽象化する API

評価軸は proof length だけでなく、自然数減算の扱いやすさ、`q=0` edge case の自動処理、エラーメッセージ、後続 `signedFiveAdicPacket_gcd_eq_five` からの再利用性である。

## 次に読むべき定理

次は直後の

```lean
theorem signedFiveAdicPacket_gcd_eq_five
    {u v w : ℕ} (p : SignedFiveAdicPacket u v w) :
    Nat.gcd p.carrier p.residual = 5 := by
  ...
```

を読むべきである。本補題と difference 側の既存 gcd-control 補題を source provenance ごとに使い分け、上界

$$
\gcd(p.carrier,p.residual)\mid5
$$

を証明する一方、packet に保存された `five_dvd_carrier` と `residual_shape` から

$$
5\mid\gcd(p.carrier,p.residual)
$$

を得て、反対称性で gcd をちょうど $5$ に固定する。ここが `SignedFiveAdicPowerSplit` の最初の主要 theorem である。