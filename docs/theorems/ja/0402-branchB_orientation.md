# 0402 `CounterexamplePack.branchB_orientation`

## 宣言種別

`theorem`

## Lean の型

```lean
theorem CounterexamplePack.branchB_orientation
    {x y z : ℕ} (p : CounterexamplePack x y z) :
    ¬ 5 ∣ z - y ∨ ¬ 5 ∣ z - x := by
  by_cases hyGap : 5 ∣ z - y
  · right
    intro hxGap
    have hyz : y ≤ z := (right_lt_of_fermat5Equation p.hx p.hEq).le
    have hxz : x ≤ z := by
      have hEqSwap : Fermat5Equation y x z := by
        simpa [Fermat5Equation, Nat.add_comm] using p.hEq
      exact (right_lt_of_fermat5Equation p.hy hEqSwap).le
    have hbody : Body5 (z - y) y = x ^ 5 :=
      body5_eq_fifth_power_of_fermat hyz p.hEq
    have h5xPow : 5 ∣ x ^ 5 := by
      rw [← hbody]
      exact dvd_mul_of_dvd_left hyGap _
    have h5x : 5 ∣ x :=
      (by norm_num : Nat.Prime 5).dvd_of_dvd_pow h5xPow
    have h5z : 5 ∣ z := by
      rw [← Nat.sub_add_cancel hxz]
      exact dvd_add hxGap h5x
    have h5y : 5 ∣ y := by
      rcases h5z with ⟨m, hm⟩
      rcases hyGap with ⟨n, hn⟩
      use m - n
      omega
    exact (Nat.not_coprime_of_dvd_of_dvd (by omega) h5x h5y) p.hxy
  · exact Or.inl hyGap
```

## 数学的主張

`CounterexamplePack x y z` は、正の自然数による原始的な FLT5 反例候補を表す。とくに

$$
x^5+y^5=z^5,
$$

かつ

$$
\gcd(x,y)=1
$$

を保持する。

この定理は、そのような packet では二つの gap

$$
z-y,\qquad z-x
$$

が同時に 5 の倍数になることはない、と述べる。したがって必ず

$$
5\nmid (z-y)
$$

または

$$
5\nmid (z-x)
$$

の少なくとも一方が成立する。

これは「どちらの向きから Branch B を読むか」を決める routing theorem である。左側の gap `z - y` が clean なら元の packet をそのまま使い、そうでなければ `x` と `y` を交換した packet に対して `z - x` を clean gap として使える。

## 証明全体での役割

直前の `signedGoldenZeroSectorExclusion_of_arithmetic` までで、zero unit sector の算術的排除条件を `SignedGoldenZeroSectorExclusion` へ持ち上げる準備が整った。しかし FLT5 の原始 packet 全体を閉じるには、Branch B の前提となる「5 で割れない gap」を、入力 packet ごとに確実に一つ選ばなければならない。

`branchB_orientation` はその選択を保証する。

後続の `counterexamplePackRefuter_of_unitFifthPowerExclusion` は

```lean
rcases p.branchB_orientation with hyGap | hxGap
· exact branchB_false_of_unitFifthPowerExclusion hExclude p hyGap
· exact branchB_false_of_unitFifthPowerExclusion hExclude p.swap hxGap
```

という形で、この二分岐をそのまま利用する。したがって本定理は

$$
\text{primitive packet}
\longrightarrow
\text{one admissible Branch-B orientation}
$$

という closure 層のルータである。

## 直接依存する定義・補題

### `CounterexamplePack`

`p.hx`, `p.hy`, `p.hxy`, `p.hEq` を通じて、少なくとも次の情報を使用する。

- `p.hx : 0 < x`
- `p.hy : 0 < y`
- `p.hxy : Nat.Coprime x y`
- `p.hEq : Fermat5Equation x y z`

### `Fermat5Equation`

指数 5 のフェルマー方程式

$$
x^5+y^5=z^5
$$

を表す。

証明中では `x` と `y` の交換に対して対称であることを

```lean
simpa [Fermat5Equation, Nat.add_comm] using p.hEq
```

で明示する。

### `right_lt_of_fermat5Equation`

正の左項と FLT5 方程式から、対応する入力が `z` より小さいことを与える。ここでは自然数減算を整数的に扱えるよう、

```lean
hyz : y ≤ z
hxz : x ≤ z
```

を得るために使う。

### `body5_eq_fifth_power_of_fermat`

```lean
Body5 (z - y) y = x ^ 5
```

を与える。`Body5` は第五冪差の因数分解に現れる body 側であり、ここでは `5 ∣ z-y` を `5 ∣ x^5` へ運ぶ橋になる。

### `Nat.Prime.dvd_of_dvd_pow`

5 が素数なので

$$
5\mid x^5 \Longrightarrow 5\mid x
$$

を回収する。

### `Nat.not_coprime_of_dvd_of_dvd`

最後に

$$
5\mid x,\qquad 5\mid y
$$

から `Nat.Coprime x y` に矛盾する。

## 証明の流れ

### 1. `z-y` が 5 で割れるかで場合分けする

```lean
by_cases hyGap : 5 ∣ z - y
```

`hyGap` が偽なら、結論の左側

```lean
Or.inl hyGap
```

で即座に終了する。

興味深いのは `5 ∣ z-y` の場合である。このとき右側、すなわち

$$
5\nmid(z-x)
$$

を証明する。

### 2. 反対に `5 ∣ z-x` も仮定する

```lean
intro hxGap
```

ここから両 gap が 5 の倍数なら primitive 条件と矛盾することを示す。

### 3. 自然数減算のための順序条件を確保する

`right_lt_of_fermat5Equation` から

$$
y\le z
$$

を得る。また `x` 側については方程式を交換して

$$
y^5+x^5=z^5
$$

と読み替え、同じ補題から

$$
x\le z
$$

を得る。

後者の交換は

```lean
have hEqSwap : Fermat5Equation y x z := by
  simpa [Fermat5Equation, Nat.add_comm] using p.hEq
```

で行われる。

### 4. `z-y` の 5 可除性を `x^5` へ移す

```lean
have hbody : Body5 (z - y) y = x ^ 5 :=
  body5_eq_fifth_power_of_fermat hyz p.hEq
```

`Body5` は先頭に gap 因子を含むため、`hyGap : 5 ∣ z-y` から

$$
5\mid Body5(z-y,y)
$$

が得られ、従って

$$
5\mid x^5
$$

となる。

Lean では

```lean
rw [← hbody]
exact dvd_mul_of_dvd_left hyGap _
```

と短く書かれている。

### 5. 素性により `5 ∣ x`

```lean
have h5x : 5 ∣ x :=
  (by norm_num : Nat.Prime 5).dvd_of_dvd_pow h5xPow
```

第五冪に対する可除性を底へ降ろす。

### 6. `5 ∣ z`

`hxz : x ≤ z` なので

$$
z=(z-x)+x.
$$

両項が 5 の倍数だから

$$
5\mid z.
$$

Lean では自然数の切り捨て減算を正しく戻すため、

```lean
rw [← Nat.sub_add_cancel hxz]
exact dvd_add hxGap h5x
```

とする。

### 7. `5 ∣ y`

今度は

$$
z-y
$$

と $z$ がともに 5 の倍数なので $y$ も 5 の倍数である。

Lean コードでは可除性 witness を明示的に分解し、

```lean
rcases h5z with ⟨m, hm⟩
rcases hyGap with ⟨n, hn⟩
use m - n
omega
```

としている。

これは自然数上の減算を含むため、単純な `dvd_sub` が使えないことへの対応である。

### 8. primitive 条件と矛盾

最後に

$$
5\mid x,\qquad 5\mid y,
$$

しかも $5>1$ なので $x,y$ は互いに素ではない。

```lean
exact (Nat.not_coprime_of_dvd_of_dvd (by omega) h5x h5y) p.hxy
```

で `False` を得て、`¬ 5 ∣ z-x` が確定する。

## Lean 固有の処理

### 自然数減算

本定理の Lean 的な中心は `Nat` の減算である。数学では

$$
z=(z-x)+x
$$

や

$$
y=z-(z-y)
$$

を無意識に使えるが、Lean の `Nat.sub` は切り捨て減算なので、`x ≤ z`, `y ≤ z` の証明が必要になる。

そのため `right_lt_of_fermat5Equation` が単なる大小関係以上に重要な依存となっている。

### `x` と `y` の交換

`CounterexamplePack` 自体をここで作り直すのではなく、方程式だけを

```lean
simpa [Fermat5Equation, Nat.add_comm]
```

で交換して `right_lt_of_fermat5Equation` を再利用している。

### 素数 5 の生成

```lean
(by norm_num : Nat.Prime 5)
```

で具体的素数性をその場で閉じる。専用 lemma を追加する必要がないため簡潔である。

### `omega`

最後の `5 ∣ y` の witness 計算、および `5 > 1` のような自然数線形算術を処理する。特に witness `m - n` の正当化は自然数減算を含むため、`omega` と相性がよい。

## 冗長・重複箇所

本証明は短く、目立つ重複は少ない。ただし次の二点は抽象化可能である。

1. `right_lt_of_fermat5Equation` を `x` と `y` の双方へ適用するための交換コード。
2. `5 ∣ z` と `5 ∣ z-y` から `5 ∣ y` を自然数減算経由で戻す部分。

後者は一般に

```lean
k ∣ z → k ∣ z - y → y ≤ z → k ∣ y
```

型の補題として切り出せる。ただし本 theorem 一箇所だけなら、現在の局所証明の方が追跡しやすい。

## 最適化候補

### gap 同時可除性の補題化

本定理の本質は

$$
5\mid(z-y)\land5\mid(z-x)\Longrightarrow 5\mid x\land5\mid y
$$

である。これを内部補題に分けると `branchB_orientation` 自体は「同時可除なら coprime contradiction」という高水準な構造だけになる。

ただし証明の局所性が高く、現在の形も十分明瞭である。

### 対称な `right_lt` API

`right_lt_of_fermat5Equation` が片側の正値性を前提にしているため、`x` 側では equation swap が必要になる。もし FLT5 API に

```lean
left_lt_right_of_fermat5Equation
both_lt_right_of_fermat5Equation
```

のような対称版が頻繁に必要なら、まとめて返す補題を置く余地がある。

### `h5y` の証明

`Nat` 上に適切な divisibility-subtraction lemma が既に Mathlib に存在するなら、witness 展開 + `omega` より宣言的に書ける可能性がある。ただしこの点は本ドキュメント作成時には未確認であり、置換可能性は推測である。

## 必要な Mathlib import

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は現在

```lean
import Mathlib
```

を使用している。

本定理が直接利用する Mathlib 機能は少なくとも次を含む。

- `Nat.Prime` と `dvd_of_dvd_pow`
- `Nat.Coprime` と `Nat.not_coprime_of_dvd_of_dvd`
- 自然数の divisibility
- `Nat.sub_add_cancel`
- `norm_num`
- `omega`
- `simpa`, `rw`, `rcases`

ローカル依存としては `CounterexamplePack`, `Fermat5Equation`, `right_lt_of_fermat5Equation`, `Body5`, `body5_eq_fifth_power_of_fermat` を定義・証明する先行 FLT5 モジュールが必要である。

### import 最適化候補

standalone 全体の `import Mathlib` をこの theorem 単体の最小 import に縮小することは可能と思われるが、今回は Lean build を行わない条件なので厳密な最小集合は確定していない。候補としては Nat の prime/gcd/divisibility と `Mathlib.Tactic` 系、および上記 FLT5 ローカルモジュール群が中心になる。

したがって「`import Mathlib` は過剰である可能性が高い」までは確認できるが、具体的な最小 import リストは未検証である。

## Comparator challenge 化

**可能。しかも良い候補である。**

理由は、証明が

- 具体的な素数 5
- 自然数減算
- 可除性
- coprimality
- 第五冪から底への prime divisibility
- equation symmetry

という Lean の基礎的だが事故の起こりやすい要素を一つに集約しているからである。

challenge 化するなら、`CounterexamplePack` 全体を持ち込まず、次の入力だけに縮約するとよい。

- `hx, hy : 0 < x, 0 < y`
- `hxy : Nat.Coprime x y`
- `hEq : x^5 + y^5 = z^5`
- `body5_eq_fifth_power_of_fermat`
- 必要な大小補題

目標を

```lean
¬ 5 ∣ z - y ∨ ¬ 5 ∣ z - x
```

とすれば、Comparator が proof engineering と自然数減算をどこまで安定して処理できるかを見る良い小課題になる。

## 次に読むべき宣言

次は **0403 `CounterexamplePackRefuter`** である。

宣言種別は theorem ではなく **`abbrev`**。

```lean
abbrev CounterexamplePackRefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

0402 で「各 primitive packet を Branch B のどちらかの向きへ必ず送れる」ことが確立した。0403 はその直後で、primitive packet を一律に排除する receiver interface を `Prop` として定義する。

その次の `counterexamplePackRefuter_of_unitFifthPowerExclusion` が 0402 の orientation 二分岐を実際に消費し、

$$
\text{SignedGoldenUnitFifthPowerExclusion}
\Longrightarrow
\text{CounterexamplePackRefuter}
$$

を閉じる。したがって依存順としては 0403 を先に読むのが正しい。