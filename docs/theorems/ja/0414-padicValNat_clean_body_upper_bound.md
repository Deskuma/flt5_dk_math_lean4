# 0414 `padicValNat_clean_body_upper_bound`

## 宣言種別

`theorem`

## Lean の型

```lean
theorem padicValNat_clean_body_upper_bound
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    padicValNat q (g * GN5 g y) ≤ 1 := by
  letI : Fact (Nat.Prime q) := ⟨h.prime⟩
  have hBodyNe : g * GN5 g y ≠ 0 := by
    intro hzero
    apply h.not_sq_dvd_body
    rw [hzero]
    exact dvd_zero _
  by_contra hnot
  have htwo : 2 ≤ padicValNat q (g * GN5 g y) := by
    omega
  have hsq : q ^ 2 ∣ g * GN5 g y :=
    (@padicValNat_dvd_iff_le q (Fact.mk h.prime) (g * GN5 g y) 2 hBodyNe).mpr htwo
  exact h.not_sq_dvd_body hsq
```

この theorem は、`CleanGN5Channel g y q` が与えられたとき、full fifth-power body

```lean
g * GN5 g y
```

における素数 `q` の `padicValNat` が高々 1 であることを示す。

## 数学的主張

`CleanGN5Channel g y q` は、正本の `CleanChannel.lean` で次の情報を持つ structure である。

```lean
structure CleanGN5Channel (g y q : ℕ) : Prop where
  prime : Nat.Prime q
  dvd_GN5 : q ∣ GN5 g y
  not_dvd_gap : ¬ q ∣ g
  noLift : ¬ q ^ 2 ∣ GN5 g y
```

そこから既に

```lean
h.dvd_body : q ∣ g * GN5 g y
h.not_sq_dvd_body : ¬ q ^ 2 ∣ g * GN5 g y
```

が証明されている。

0414 が使う本質は後者である。もし

$$
v_q(g\,GN_5(g,y))\ge 2
$$

なら、`padicValNat_dvd_iff_le` により

$$
q^2\mid g\,GN_5(g,y)
$$

となる。しかし clean channel は

$$
q^2\nmid g\,GN_5(g,y)
$$

を保証する。従って

$$
v_q(g\,GN_5(g,y))<2.
$$

`padicValNat` は自然数値なので、これは

$$
v_q(g\,GN_5(g,y))\le1
$$

と同値である。

Lean 上の結論は

```lean
padicValNat q (g * GN5 g y) ≤ 1
```

である。

## 証明全体での役割

0413 `padicValNat_lower_bound_d5` は、素数 `q` が正整数 `x` を割るなら

$$
v_q(x^5)\ge5
$$

と評価した。

0414 はその対になる clean-body 側の upper bound で、

$$
v_q(g\,GN_5(g,y))\le1
$$

を与える。

正本の `Valuation.lean` はこの局所矛盾を

```text
complete fifth power  -> local load at least 5
clean GN5 channel     -> local load at most 1
```

と説明している。

次の 0415 `padicValNat_clean_body_eq_one` では、`h.dvd_body` から lower bound

$$
1\le v_q(g\,GN_5(g,y))
$$

も得て、0414 と合わせて

$$
v_q(g\,GN_5(g,y))=1
$$

へ鋭化する。

その後 `counterexample_false_of_clean_GN5Channel_by_padicValNat` が FLT5 の body identity

$$
(z-y)GN_5(z-y,y)=x^5
$$

を使い、第五冪側の `≥ 5` と clean body 側の `= 1` を同じ自然数へ移して矛盾させる。

従って 0414 は valuation proof route の upper-bound lemma である。

## 直接依存する定義・補題

### `CleanGN5Channel`

`CleanGN5Channel g y q` は、`q` が `GN5 g y` に一度だけ現れ、gap `g` には現れない clean prime channel を表す。

直接利用する field / theorem は次の二つである。

```lean
h.prime : Nat.Prime q
h.not_sq_dvd_body : ¬ q ^ 2 ∣ g * GN5 g y
```

`h.not_sq_dvd_body` 自体は `not_dvd_gap` と `noLift` を使い、`q^2` と gap が互いに素であることから full body への square lift を GN5 側へ戻して排除する theorem である。

0414 はその内部証明を再実行せず、既に確立された interface を利用する。

### `GN5`

`GN5 g y` は gap 座標 `z=g+y` における第五差分の cyclotomic quotient で、

$$
(g+y)^5-y^5=g\,GN_5(g,y)
$$

を満たす。

0414 ではその多項式展開そのものは使わず、full body `g * GN5 g y` を valuation の対象として扱う。

### `padicValNat_dvd_iff_le`

この theorem の核心となる Mathlib bridge である。

非零な自然数 `n` について、概念的には

$$
q^k\mid n
\Longleftrightarrow
k\le v_q(n)
$$

を結ぶ。

0414 では逆向き `.mpr` を用いて

```lean
2 ≤ padicValNat q (g * GN5 g y)
```

から

```lean
q ^ 2 ∣ g * GN5 g y
```

を得る。

### `omega`

否定された目標

```lean
¬ padicValNat q (g * GN5 g y) ≤ 1
```

から

```lean
2 ≤ padicValNat q (g * GN5 g y)
```

を自然数算術として導く。

## 証明または構築の流れ

### 1. 素数性を typeclass instance にする

```lean
letI : Fact (Nat.Prime q) := ⟨h.prime⟩
```

`padicValNat` API が要求する `[Fact (Nat.Prime q)]` を局所的に供給する。

### 2. full body が非零であることを示す

```lean
have hBodyNe : g * GN5 g y ≠ 0 := by
  intro hzero
  apply h.not_sq_dvd_body
  rw [hzero]
  exact dvd_zero _
```

もし body が `0` なら、任意の自然数は `0` を割るため

```lean
q ^ 2 ∣ 0
```

となる。これは `h.not_sq_dvd_body` と矛盾する。

この非零性は数学的には clean-channel 条件から自動的に従うが、`padicValNat_dvd_iff_le` の side condition として Lean に明示する必要がある。

### 3. 上界を否定して付値 2 以上を得る

```lean
by_contra hnot
have htwo : 2 ≤ padicValNat q (g * GN5 g y) := by
  omega
```

自然数値に対する

$$
\neg(v\le1)\Longrightarrow2\le v
$$

を `omega` が処理する。

### 4. valuation lower bound を square divisibility に戻す

```lean
have hsq : q ^ 2 ∣ g * GN5 g y :=
  (@padicValNat_dvd_iff_le q (Fact.mk h.prime)
    (g * GN5 g y) 2 hBodyNe).mpr htwo
```

ここで

$$
2\le v_q(body)
$$

を

$$
q^2\mid body
$$

へ変換する。

### 5. clean-channel invariant と衝突させる

```lean
exact h.not_sq_dvd_body hsq
```

`h.not_sq_dvd_body` が square divisibility を禁止しているため矛盾し、元の upper bound が確立する。

## Lean 固有の処理

### 1. `Fact` instance

数学上は `h.prime : Nat.Prime q` をそのまま使えばよいが、Mathlib の valuation 補題では typeclass として素数性を要求する。

```lean
letI : Fact (Nat.Prime q) := ⟨h.prime⟩
```

は proposition の証明を instance search 用に再包装しているだけで、新しい仮定ではない。

### 2. 非零 side condition の人工的な抽出

`padicValNat_dvd_iff_le` を full body に適用するには `g * GN5 g y ≠ 0` が必要である。

正本は積の各因子の正性や非零性を個別に証明せず、より強い clean invariant

```lean
¬ q ^ 2 ∣ g * GN5 g y
```

から一行で非零性を導く。

これは Lean 証明として非常に効率的である。

### 3. `by_contra` と自然数の離散性

数学では `v_q(body)≤1` の否定から `v_q(body)≥2` は自明に見えるが、Lean 上では順序論の変換が必要になる。

ここを `omega` に任せることで、`Nat.lt_of_not_ge` などの補題連鎖を避けている。

### 4. `@` による implicit argument の露出

```lean
@padicValNat_dvd_iff_le q (Fact.mk h.prime)
  (g * GN5 g y) 2 hBodyNe
```

は implicit / instance 引数を明示して theorem の適用形を固定している。

一方で Mathlib API の引数順へ強く依存する書き方でもある。

### 5. `.mpr`

`padicValNat_dvd_iff_le` が返す同値の

```lean
(k ≤ padicValNat q n) → q ^ k ∣ n
```

方向を `.mpr` で選んでいる。

0413 では divisibility から valuation lower bound を得るため `.mp` を使っており、0413 と 0414 は同じ bridge theorem を逆方向に利用している点が美しい対称性になっている。

## 冗長・重複箇所

### `letI` と `Fact.mk h.prime` の重複

0413 と同様、

```lean
letI : Fact (Nat.Prime q) := ⟨h.prime⟩
```

で instance を登録した後に、

```lean
Fact.mk h.prime
```

を明示的に渡している。

これは Lean レベルでは軽い重複である。ただし補題適用を安定化させるために意図的に明示している可能性がある。

### `hBodyNe` は 0415 でも再登場する

直後の `padicValNat_clean_body_eq_one` でも同一の証明

```lean
have hBodyNe : g * GN5 g y ≠ 0 := by
  intro hzero
  apply h.not_sq_dvd_body
  rw [hzero]
  exact dvd_zero _
```

が繰り返される。

従って clean body の非零性を

```lean
CleanGN5Channel.body_ne
```

のような helper theorem として `CleanChannel.lean` 側へ置けば重複を除去できる。

## 最適化候補

### 1. clean body 非零補題を抽出する

0414 と 0415 で同一の非零証明を共有できるため、最も明確な局所最適化候補である。

概念的には

```lean
theorem CleanGN5Channel.body_ne
    (h : CleanGN5Channel g y q) :
    g * GN5 g y ≠ 0 := by
  ...
```

を用意すれば valuation theorem 群が短くなる。

### 2. `Fact.mk h.prime` の明示指定を減らす

`letI` 後に typeclass inference が十分に働くなら、`padicValNat_dvd_iff_le` の instance 引数を省略できる可能性がある。

ただしこのリポジトリの固定 Mathlib 版での推論結果は Lean build を行っていないため未確認である。

### 3. 一般的な valuation upper-bound lemma へ抽象化する

0414 の数学は GN5 固有ではなく、一般に

$$
\neg(q^{k+1}\mid n)
\Longrightarrow
v_q(n)\le k
$$

という valuation / divisibility の基本変換である。

ただし `CleanGN5Channel` 専用名は FLT5 の証明グラフを読みやすくするため、一般 helper を導入しても 0414 自体は薄い wrapper として残す価値がある。

### 4. `by_contra` を順序補題で直接書く

`omega` を減らしたい場合、`Nat` の順序補題から `2 ≤ v` を明示構成できる。

現行コードは短く意図も明快なので、これは必須の最適化ではない。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

0414 が Mathlib 側で直接利用する機能は少なくとも

- `padicValNat`
- `padicValNat_dvd_iff_le`
- `Fact`
- `Nat.Prime`
- 自然数の可除性
- `omega`

である。

DkMath 側では少なくとも

- `GN5`
- `CleanGN5Channel`
- `CleanGN5Channel.not_sq_dvd_body`

が必要である。

従って umbrella import `Mathlib` より狭い import へ縮小できる余地は大きい。p-adic valuation API を提供する Mathlib モジュールと `omega` tactic モジュールが主要候補になる。

ただし固定 Mathlib 版における正確な最小 module path と transitive import 集合は、今回 Lean build を行っていないため確認できない。具体的な最小 import 宣言は断定しない。

また standalone は generated artifact であり、実際の source module 順には `GN5.lean`、`CleanChannel.lean`、`Valuation.lean` が含まれている。0414 単独の最小 import と `Valuation.lean` 全体の最小 import は別問題として扱うべきである。

## Comparator challenge 化の可否

### 単独 challenge

適している。

0414 は短いが、Comparator に次の能力を同時に要求できる。

1. `CleanGN5Channel` の field / derived theorem を読む。
2. `not_sq_dvd_body` から body の非零性を導く。
3. upper bound の否定を `2 ≤ valuation` に変換する。
4. `padicValNat_dvd_iff_le` を正しい方向で適用する。
5. 得られた square divisibility を clean invariant と衝突させる。

0413 と対で出題すると、同じ valuation bridge を `.mp` と `.mpr` の逆方向に使い分けられるかも評価できる。

### challenge 設計上の注意

`h.not_sq_dvd_body` と `padicValNat_dvd_iff_le` を両方明示すると、証明探索はかなり短くなる。

より強い challenge にするなら、`CleanGN5Channel` と目標だけを与え、

- full body の square non-divisibility を既存 API から発見すること、
- valuation/divisibility bridge を Mathlib から選ぶこと

まで要求するとよい。

一方、proof synthesis の比較を主目的とする場合は利用可能補題を明示した方が theorem-name retrieval の差を減らせる。

## 次に読むべき宣言

次は 0415 `padicValNat_clean_body_eq_one`、種別は `theorem` である。

```lean
theorem padicValNat_clean_body_eq_one
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    padicValNat q (g * GN5 g y) = 1 := by
  letI : Fact (Nat.Prime q) := ⟨h.prime⟩
  have hBodyNe : g * GN5 g y ≠ 0 := by
    intro hzero
    apply h.not_sq_dvd_body
    rw [hzero]
    exact dvd_zero _
  apply Nat.le_antisymm (padicValNat_clean_body_upper_bound h)
  exact (@padicValNat_dvd_iff_le q (Fact.mk h.prime)
    (g * GN5 g y) 1 hBodyNe).mp (by simpa using h.dvd_body)
```

0414 の

$$
v_q(body)\le1
$$

に対し、clean channel の `q ∣ body` から

$$
1\le v_q(body)
$$

を追加し、反対称性で

$$
v_q(body)=1
$$

を得る。これにより valuation contradiction の clean-body 側が exact value として完成する。
