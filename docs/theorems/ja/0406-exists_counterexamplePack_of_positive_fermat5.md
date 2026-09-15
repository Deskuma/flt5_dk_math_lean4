# 0406 `exists_counterexamplePack_of_positive_fermat5`

## 宣言種別

`theorem`

## Lean の型

```lean
/-- Arbitrary positive solutions can be reduced to a primitive counterexample packet. -/
theorem exists_counterexamplePack_of_positive_fermat5
    {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hEq : Fermat5Equation x y z) :
    ∃ x' y' z' : ℕ, CounterexamplePack x' y' z' := by
  let d := Nat.gcd x y
  let x' := x / d
  let y' := y / d
  have hdPos : 0 < d := Nat.gcd_pos_of_pos_left y hx
  have hdx : d ∣ x := Nat.gcd_dvd_left x y
  have hdy : d ∣ y := Nat.gcd_dvd_right x y
  have hd5z5 : d ^ 5 ∣ z ^ 5 := by
    have hd5x5 : d ^ 5 ∣ x ^ 5 := pow_dvd_pow_of_dvd hdx 5
    have hd5y5 : d ^ 5 ∣ y ^ 5 := pow_dvd_pow_of_dvd hdy 5
    rw [← hEq]
    exact dvd_add hd5x5 hd5y5
  have hdz : d ∣ z := by
    have hroot := (Nat.dvd_pow_iff_ceilRoot_dvd (a := d ^ 5) (b := z)
      (by decide : 5 ≠ 0)).mp hd5z5
    simpa using hroot
  let z' := z / d
  have hxEq : d * x' = x := Nat.mul_div_cancel' hdx
  have hyEq : d * y' = y := Nat.mul_div_cancel' hdy
  have hzEq : d * z' = z := Nat.mul_div_cancel' hdz
  have hxPos : 0 < x' := Nat.div_pos (Nat.le_of_dvd hx hdx) hdPos
  have hyPos : 0 < y' := Nat.div_pos (Nat.le_of_dvd hy hdy) hdPos
  have hzPos : 0 < z' := Nat.div_pos (Nat.le_of_dvd hz hdz) hdPos
  have hcop : Nat.Coprime x' y' := by
    exact Nat.coprime_div_gcd_div_gcd hdPos
  have hEq' : Fermat5Equation x' y' z' := by
    have hscaled : d ^ 5 * (x' ^ 5 + y' ^ 5) = d ^ 5 * z' ^ 5 := by
      calc
        d ^ 5 * (x' ^ 5 + y' ^ 5) = (d * x') ^ 5 + (d * y') ^ 5 := by ring
        _ = x ^ 5 + y ^ 5 := by rw [hxEq, hyEq]
        _ = z ^ 5 := hEq
        _ = (d * z') ^ 5 := by rw [hzEq]
        _ = d ^ 5 * z' ^ 5 := by ring
    unfold Fermat5Equation
    exact Nat.mul_left_cancel (pow_pos hdPos 5) hscaled
  exact ⟨x', y', z', hxPos, hyPos, hzPos, hcop, hEq'⟩
```

## 数学的主張・宣言の意味

この theorem は、正整数の FLT5 解

$$
x^5+y^5=z^5,
\qquad x>0,\ y>0,\ z>0
$$

が存在すると仮定したなら、そこから互いに素な正整数解、すなわち `CounterexamplePack` を必ず抽出できることを示す正規化定理である。

まず

$$
d=\gcd(x,y),
\qquad x'=\frac{x}{d},
\qquad y'=\frac{y}{d}
$$

と置く。すると定義から

$$
\gcd(x',y')=1
$$

となる。

重要なのは、$d\mid x$ と $d\mid y$ だけでなく、元の第五冪方程式から $d\mid z$ も導く点である。実際、

$$
d^5\mid x^5,
\qquad d^5\mid y^5
$$

なので

$$
d^5\mid x^5+y^5=z^5.
$$

ここから Lean では `Nat.dvd_pow_iff_ceilRoot_dvd` を用いて第五根を戻し、

$$
d\mid z
$$

を得る。そこで

$$
z'=\frac{z}{d}
$$

と定めることができる。

元の式へ

$$
x=dx',\qquad y=dy',\qquad z=dz'
$$

を代入すると、

$$
d^5(x'^5+y'^5)=d^5z'^5.
$$

$d>0$ なので $d^5>0$ であり、自然数の左消去によって

$$
x'^5+y'^5=z'^5
$$

を得る。

従って、任意の正整数解は

$$
(x,y,z)
\longmapsto
\left(\frac{x}{d},\frac{y}{d},\frac{z}{d}\right)
$$

により primitive solution へ縮約される。

## 証明全体での役割

0405 までで証明は

```lean
CounterexamplePack x y z → False
```

という primitive packet の排除まで到達した。しかし最終目標は、互いに素性を仮定していない任意の正整数 $x,y,z$ に対する FLT5 である。

0406 はその間を埋める normalization bridge である。

論理の流れは

$$
\begin{aligned}
&x^5+y^5=z^5,
\quad x,y,z>0\\
&\qquad\Downarrow\quad d=\gcd(x,y)\\
&x=dx',\quad y=dy',\quad z=dz'\\
&\qquad\Downarrow\\
&x'^5+y'^5=z'^5,
\quad x',y',z'>0,
\quad \gcd(x',y')=1\\
&\qquad\Downarrow\\
&\mathrm{CounterexamplePack}(x',y',z').
\end{aligned}
$$

したがって、0406 以降は primitive case の contradiction を一般の positive solution に持ち上げられる。

この定理は golden integer、unit class、zero-sector descent には依存しない。証明の入口側に属する純粋な自然数 gcd normalization であり、証明全体の代数的な前処理と後段の primitive obstruction を接続する役割を持つ。

## 直接依存する定義・補題

### `Fermat5Equation`

元の方程式を表す定義である。

概念的には

```lean
x ^ 5 + y ^ 5 = z ^ 5
```

を表す。

0406 はこの等式を divisibility と cancellation の二箇所で使用する。

### `CounterexamplePack`

結論で構築される structure。

ここで必要な field は、コード末尾の constructor から読み取れる通り、少なくとも

- `0 < x'`
- `0 < y'`
- `0 < z'`
- `Nat.Coprime x' y'`
- `Fermat5Equation x' y' z'`

である。

0406 はこれらを順に構築し、最後に

```lean
⟨x', y', z', hxPos, hyPos, hzPos, hcop, hEq'⟩
```

として packet を完成させる。

### `Nat.gcd_pos_of_pos_left`

$x>0$ から

$$
0<\gcd(x,y)
$$

を得る。

この正値性は quotient の正値性と、最後の $d^5$ の cancellation の両方に必要である。

### `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right`

$$
d\mid x,
\qquad d\mid y
$$

を供給する gcd の基本補題。

### `pow_dvd_pow_of_dvd`

$d\mid x$ から

$$
d^5\mid x^5
$$

へ持ち上げる。同様に $y$ にも使われる。

### `Nat.dvd_pow_iff_ceilRoot_dvd`

この証明で最も特徴的な Mathlib 補題である。

`hd5z5 : d ^ 5 ∣ z ^ 5` から、指数 $5\neq0$ を使って根を戻し、最終的に

```lean
hdz : d ∣ z
```

を得る。

数学上は「$d^5\mid z^5$ なら $d\mid z$」という素因数指数の比較に相当するが、Lean コードでは `ceilRoot` を通した一般補題を再利用している。

### `Nat.mul_div_cancel'`

可除性から

$$
d\left(\frac{x}{d}\right)=x
$$

という exact reconstruction を得る。`x`, `y`, `z` の三つに使用される。

### `Nat.div_pos`

$x'>0$, $y'>0$, $z'>0$ を示すために使われる。

ここでは `Nat.le_of_dvd` によって $d\le x,y,z$ を作り、`hdPos` と組み合わせて quotient positivity を得る。

### `Nat.coprime_div_gcd_div_gcd`

$$
\gcd\left(\frac{x}{d},\frac{y}{d}\right)=1
$$

を直接供給する normalization 補題。

### `Nat.mul_left_cancel`

最後に

$$
d^5 A=d^5B
$$

から $A=B$ を得る。コードでは `pow_pos hdPos 5` を渡して非零性を保証している。

## 証明・構築の流れ

### 1. gcd と normalized coordinates を定める

```lean
let d := Nat.gcd x y
let x' := x / d
let y' := y / d
```

まず左二変数だけで primitive normalization の尺度を固定する。

### 2. gcd の正値性と可除性を得る

```lean
have hdPos : 0 < d := Nat.gcd_pos_of_pos_left y hx
have hdx : d ∣ x := Nat.gcd_dvd_left x y
have hdy : d ∣ y := Nat.gcd_dvd_right x y
```

### 3. $d^5\mid z^5$ を導く

```lean
have hd5x5 : d ^ 5 ∣ x ^ 5 := pow_dvd_pow_of_dvd hdx 5
have hd5y5 : d ^ 5 ∣ y ^ 5 := pow_dvd_pow_of_dvd hdy 5
rw [← hEq]
exact dvd_add hd5x5 hd5y5
```

元の Fermat equation を逆向きに rewrite して、右辺 $z^5$ を左辺 $x^5+y^5$ に置き換える。

### 4. 第五冪の可除性から $d\mid z$ を回収する

```lean
have hroot := (Nat.dvd_pow_iff_ceilRoot_dvd ...).mp hd5z5
simpa using hroot
```

ここが normalization の技術的中心である。

### 5. $z'$ を定義し、元の三変数を復元する

```lean
let z' := z / d
have hxEq : d * x' = x := Nat.mul_div_cancel' hdx
have hyEq : d * y' = y := Nat.mul_div_cancel' hdy
have hzEq : d * z' = z := Nat.mul_div_cancel' hdz
```

### 6. normalized coordinates の正値性と互いに素性を証明する

```lean
have hxPos : 0 < x' := ...
have hyPos : 0 < y' := ...
have hzPos : 0 < z' := ...
have hcop : Nat.Coprime x' y' := ...
```

### 7. normalized Fermat equation を証明する

まず $d^5$ を付けた式

```lean
d ^ 5 * (x' ^ 5 + y' ^ 5) = d ^ 5 * z' ^ 5
```

を `calc` と `ring` で作る。

その後

```lean
unfold Fermat5Equation
exact Nat.mul_left_cancel (pow_pos hdPos 5) hscaled
```

として共通因子 $d^5$ を消去する。

### 8. `CounterexamplePack` を構築する

最後にすべての field を一度に渡す。

```lean
exact ⟨x', y', z', hxPos, hyPos, hzPos, hcop, hEq'⟩
```

## Lean 固有の処理

### `let` による局所略記

`d`, `x'`, `y'`, `z'` を `let` で定義しているため、数学的な quotient notation を保ったまま証明を進められる。後続の `Nat.mul_div_cancel'` や `ring` でも Lean がこれらの局所定義を適切に展開する。

### `rw [← hEq]`

可除性 goal の右辺 `z ^ 5` を `x ^ 5 + y ^ 5` へ変形するため、方程式を逆向きに rewrite している。

### `by decide : 5 ≠ 0`

`Nat.dvd_pow_iff_ceilRoot_dvd` が指数の非零性を要求するため、具体的な数値事実 $5\neq0$ を decision procedure で埋めている。

### `simpa using hroot`

`ceilRoot` を含む一般補題の結論と目的の `d ∣ z` との間にある計算可能な正規化を `simp` に任せている。この箇所は theorem の数学的内容より Mathlib API の表現差を吸収する Lean 固有処理である。

### `ring`

`hscaled` の最初と最後で

$$
d^5x'^5=(dx')^5
$$

などの半環恒等式を自動正規化している。ここでは自然数半環上の純代数計算であり、数論的推論ではない。

### `Nat.mul_left_cancel (pow_pos hdPos 5)`

自然数では cancellation theorem が左因子の正値性を明示的に受け取る形になっている。数学では「$d^5\neq0$ なので消去」と一行で済む部分を、Lean では `pow_pos hdPos 5` で証明項として供給する。

## 冗長・重複箇所

大きな論理的重複はない。正規化の各段階が明瞭に分離されている。

ただし、次の三組は同じパターンを繰り返している。

```lean
hxEq / hyEq / hzEq
hxPos / hyPos / hzPos
```

三変数すべてを同じ gcd で割るため、局所 helper を使えば記述量を減らせる可能性はある。しかし現在の形は各座標について何を証明しているかが明瞭で、museum 用の可読性という点ではむしろ有利である。

また `hscaled` は一度 $d^5$ を両辺へ付けてから cancellation するため、抽象的な「Fermat5Equation は共通因子除去で保存される」という lemma が存在すれば短縮できる。

## 最適化候補

### gcd normalization を独立 lemma にする

例えば概念的に

```lean
Fermat5Equation x y z →
d = Nat.gcd x y →
∃ x' y' z',
  x = d * x' ∧ y = d * y' ∧ z = d * z' ∧
  Nat.Coprime x' y' ∧ Fermat5Equation x' y' z'
```

という normalization lemma を用意すれば、0406 は `CounterexamplePack` への包装だけになる。

### `d ^ 5 ∣ z ^ 5 → d ∣ z` を専用 helper にする

現在は強力な一般補題 `Nat.dvd_pow_iff_ceilRoot_dvd` を直接使っている。指数5専用の薄い補題

```lean
lemma dvd_of_pow_five_dvd_pow_five {d z : ℕ} :
    d ^ 5 ∣ z ^ 5 → d ∣ z := ...
```

を用意すれば、FLT5 本体から `ceilRoot` API の細部を隠せる。

### scaling/cancellation を定理化する

```lean
Fermat5Equation (d * x) (d * y) (d * z) ↔ Fermat5Equation x y z
```

の適切な正値・非零条件付き版を作れば、`hscaled` の `ring` chain を再利用可能な構造にできる。

ただし、この theorem は一度しか現れない normalization boundary なので、抽象化しすぎると依存関係を増やす可能性もある。現行コードは十分局所的で監査しやすい。

## 必要 Mathlib import と import 最適化候補

リポジトリの standalone 正本は `import Mathlib` を使用しているため、この宣言についても確実に確認できる import は `Mathlib` である。

0406 が直接利用する Mathlib 機能は主に

- `Nat.gcd`, `Nat.Coprime` と gcd/division 補題
- `Nat.dvd_pow_iff_ceilRoot_dvd`
- 自然数の divisibility と division
- `ring`
- `decide`

である。

従って import 最適化では、gcd/divisibility/roots と `ring` tactic を提供する個別 Mathlib module へ縮小できる可能性が高い。ただし、このリポジトリ正本では 0406 単独の最小 import build は実施されておらず、今回も Lean build は行っていないため、具体的な最小 module 集合は **未確認** である。

特に `Nat.dvd_pow_iff_ceilRoot_dvd` の定義元 module を正確に切り出す場合は、別途 Mathlib source 依存を確認する必要がある。

## Comparator challenge 化の可否

**適している。**

0406 は challenge として独立性が高い。

入力として

- `Fermat5Equation`
- `CounterexamplePack`
- Mathlib の自然数 gcd/divisibility API

だけを残し、証明本体を穴にすれば、AI が

1. gcd normalization を設計できるか
2. $d^5\mid z^5$ から $d\mid z$ を Lean で回収できるか
3. quotient positivity と coprimality を構築できるか
4. scaling を `ring` と cancellation で閉じられるか

を同時に評価できる。

特に `Nat.dvd_pow_iff_ceilRoot_dvd` を自力で発見・適用できるかは Mathlib API 探索能力を測るよい難所になる。

一方、challenge を純粋な数学推論寄りにしたい場合は

```lean
d ^ 5 ∣ z ^ 5 → d ∣ z
```

だけを補助 lemma として与え、残りの gcd normalization を解かせる形もよい。

0404・0405 のような receiver composition よりは、実際の自然数算術と structure construction が含まれるため、Comparator challenge として一段価値が高い。

## 次に読むべき宣言

次は **0407 `PositiveFermat5Refuter`** である。

宣言種別は `abbrev`。

```lean
abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

0406 が

$$
\text{positive solution}
\Longrightarrow
\text{primitive CounterexamplePack}
$$

を構築したので、0407 は「任意の positive solution を否定する証明」の receiver 型を名前付きで固定する。

その直後の `positiveFermat5Refuter_of_counterexamplePackRefuter` で 0406 が直接使用され、

$$
\mathrm{CounterexamplePackRefuter}
\Longrightarrow
\mathrm{PositiveFermat5Refuter}
$$

が閉じる。
