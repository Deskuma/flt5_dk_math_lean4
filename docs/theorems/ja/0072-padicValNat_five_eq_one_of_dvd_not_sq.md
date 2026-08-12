# 0072 — `padicValNat_five_eq_one_of_dvd_not_sq`

## Lean の型

```lean
theorem padicValNat_five_eq_one_of_dvd_not_sq
    {n : ℕ} (h5 : 5 ∣ n) (h25 : ¬ 25 ∣ n) :
    padicValNat 5 n = 1 := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hnz : n ≠ 0 := by
    intro hn0
    apply h25
    simp [hn0]
  have hge : 1 ≤ padicValNat 5 n :=
    (@padicValNat_dvd_iff_le 5 (Fact.mk (by decide)) n 1 hnz).mp (by simpa using h5)
  have hle : padicValNat 5 n ≤ 1 := by
    by_contra hnot
    have htwo : 2 ≤ padicValNat 5 n := by omega
    have hsq : 5 ^ 2 ∣ n :=
      (@padicValNat_dvd_iff_le 5 (Fact.mk (by decide)) n 2 hnz).mpr htwo
    exact h25 (by simpa using hsq)
  exact le_antisymm hle hge
```

## 数学的主張

自然数 $n$ が $5$ では割れるが $25$ では割れないなら、$n$ の $5$-進付値はちょうど $1$ である。

$$
5\mid n,\qquad 25\nmid n
\Longrightarrow
v_5(n)=1.
$$

ここで Lean の `padicValNat 5 n` が自然数上の $5$-進付値に対応する。

## 証明全体での役割

0068–0071 では residual に対して法 $25$ の情報を段階的に通常の可除性へ変換した。本補題はその終点で、

$$
(residual : ZMod\ 25)=5
\Longrightarrow residual\bmod25=5
\Longrightarrow 5\mid residual
\quad\text{and}\quad
25\nmid residual
\Longrightarrow v_5(residual)=1
$$

と、合同算術を **exact valuation** に変換する。

`nonempty_signedFiveAdicPacket_of_normalForm` の difference orientation では `GN5 (w - v) v`、sum orientation では `SumGN5 u v` に本補題を適用し、その結果を `residual_padicValNat` として packet に格納する。したがって後続層は法 $25$ の計算を再展開せず、`v_5(residual)=1` という正規化済み不変量だけを利用できる。

さらに直後の `padicValNat_carrier_shape_of_mul_eq_fifth` は、

$$
carrier\cdot residual=distinguished^5,
\qquad v_5(residual)=1
$$

から carrier 側の付値が $4\pmod5$ の形になることを導く。本補題は residual の局所情報から carrier の合同形へ進む接続点である。

## 直接依存する定義・補題

- `padicValNat`
- `padicValNat_dvd_iff_le`
- `Nat.Prime 5`
- `Fact (Nat.Prime 5)`
- `le_antisymm`
- `omega`
- `simp`

特に本質的なのは `padicValNat_dvd_iff_le` で、非零な $n$ に対し

$$
p^k\mid n
\Longleftrightarrow
k\le v_p(n)
$$

を Lean 上で使う橋である。

## 証明の流れ

1. `letI : Fact (Nat.Prime 5)` により、5 が素数であるという typeclass instance を局所的に供給する。
2. `h25 : ¬ 25 ∣ n` から $n\neq0$ を示す。もし $n=0$ なら $25\mid0$ なので矛盾する。
3. `h5 : 5 ∣ n` と `padicValNat_dvd_iff_le` を使って
   $$
   1\le v_5(n)
   $$
   を得る。
4. 反対に $v_5(n)>1$ と仮定すると、自然数なので
   $$
   2\le v_5(n)
   $$
   となる。
5. 再び `padicValNat_dvd_iff_le` を使い、$5^2\mid n$、すなわち $25\mid n$ を得て `h25` に矛盾する。
6. よって $v_5(n)\le1$。
7. `le_antisymm hle hge` により $v_5(n)=1$ を結論する。

## Lean 固有の処理

### `Fact (Nat.Prime 5)` の注入

`padicValNat_dvd_iff_le` は素数性を typeclass 経由で要求するため、

```lean
letI : Fact (Nat.Prime 5) := ⟨by decide⟩
```

で局所 instance を作っている。数学では「5 は素数」と一言で済む部分だが、Lean では API の前提として明示的に解決する必要がある。

### `@padicValNat_dvd_iff_le` の明示引数

証明では

```lean
@padicValNat_dvd_iff_le 5 (Fact.mk (by decide)) n 1 hnz
```

のように `@` を用いて implicit argument まで明示している。これは elaborator に依存しない堅牢な書き方である一方、直前の `letI` と素数性証明を重複して渡している。

### 非零条件 `hnz`

valuation API は $n=0$ を別扱いするため、`hnz : n ≠ 0` が必要になる。本証明では `25 ∤ n` からこれを短く取り出している。

### `omega` の用途

`by_contra hnot` 後の `¬ v_5(n) ≤ 1` から `2 ≤ v_5(n)` を作る純粋な自然数順序算術だけを `omega` に任せている。数論そのものを自動化しているわけではない。

## 冗長・重複箇所

最も目立つのは素数 instance の二重指定である。冒頭に

```lean
letI : Fact (Nat.Prime 5) := ⟨by decide⟩
```

を置いているにもかかわらず、二回の `padicValNat_dvd_iff_le` 呼び出しで `Fact.mk (by decide)` を直接渡している。

また lower bound と upper bound の双方が同じ equivalence を方向だけ変えて使うため、proof term は対称的である。この対称性は読みやすい反面、一般化できる余地もある。

## 最適化候補

第一候補は typeclass inference に任せて呼び出しを短くすることである。Mathlib の現在の elaboration が許せば概念的には、

```lean
have hge : 1 ≤ padicValNat 5 n :=
  (padicValNat_dvd_iff_le hnz).mp (by simpa using h5)
```

のような形へ寄せられる可能性がある。ただし正確な implicit argument の形は Mathlib バージョン依存なので、これは **要ビルド確認の最適化候補** であり、本記事では成立を断定しない。

第二候補は一般補題化である。任意の素数 $p$ に対して

$$
p\mid n,\qquad p^2\nmid n
\Longrightarrow
v_p(n)=1
$$

を reusable helper として切り出せば、5 固有のラッパーはほぼ `simpa` だけになる。FLT5 本体では 5 しか使わないため、現状の特殊化は監査性という利点もある。

第三候補は `h25` の型を最初から `¬ 5^2 ∣ n` に揃えることである。現在は人間に読みやすい `¬ 25 ∣ n` を採用し、最後に `simpa` で $5^2=25$ を正規化している。ここは可読性と API 一致性のトレードオフである。

## 必要 Mathlib import と import 最適化候補

対象ブランチの生成済み standalone artifact は `import Mathlib` を用いており、manifest 上では本定理は `DkMath/FLT/Five/SignedFiveAdic.lean` に由来する。ただしこの博物館ブランチには分割元 `DkMath/FLT/Five/SignedFiveAdic.lean` 自体が存在せず、正確な元 import 行は直接確認できなかった。

本証明が少なくとも必要とする機能は次の系統である。

- `padicValNat` と `padicValNat_dvd_iff_le` を提供する Mathlib の $p$-進付値 API
- `Nat.Prime`
- `omega`
- 標準的な `simp` / order 補題

したがって `import Mathlib` より狭い import へ削減できる可能性は高いが、正確な最小 import は **未確認** とする。import 最適化を行うなら分割元モジュールを復元した環境で `#check padicValNat_dvd_iff_le` と Lean build により検証すべきである。

## 既存 PDF との対応

本定理に直接対応する既存日本語・英語 PDF の具体的ページは、この博物館ブランチ上で今回確認できなかった。そのため PDF 固有の説明やページ番号は推測で補わない。数学的・形式的根拠は repository 内の Lean source を優先する。

## Comparator challenge 化の可否

**適している。** 入力とゴールが短く、数論的意味は明快だが、Lean では valuation API、素数 typeclass、非零条件、可除性と付値の equivalence を正しく接続する必要があるからである。

challenge とするなら定理文をそのまま提示し、`padicValNat_dvd_iff_le` の利用可否だけをヒントとして与えるのがよい。比較点は、

- 素数 instance の扱い
- $n\neq0$ の導出
- lower/upper bound の組み立て
- `25` と `5^2` の正規化
- `omega` への依存度

である。

## 次に読むべき定理

次は

```lean
theorem padicValNat_carrier_shape_of_mul_eq_fifth
    {carrier residual distinguished : ℕ}
    (hc0 : carrier ≠ 0) (hr0 : residual ≠ 0) (_hd0 : distinguished ≠ 0)
    (hEq : carrier * residual = distinguished ^ 5)
    (hrVal : padicValNat 5 residual = 1) :
    ∃ m : ℕ, padicValNat 5 carrier = 4 + 5 * m
```

を読むべきである。本号で得た residual の exact valuation $1$ を入力として、五乗積の付値加法性から carrier の付値を $4\pmod5$ の形へ変換する。ここで局所的な mod $25$ 解析が、五乗因子分解全体の valuation obstruction へ接続される。
