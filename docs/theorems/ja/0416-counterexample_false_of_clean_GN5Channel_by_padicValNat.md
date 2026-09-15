# 0416 `counterexample_false_of_clean_GN5Channel_by_padicValNat`

## 宣言種別

`theorem`

## Lean の型

```lean
theorem counterexample_false_of_clean_GN5Channel_by_padicValNat
    {x y z q : ℕ}
    (hPack : CounterexamplePack x y z)
    (hClean : CleanGN5Channel (z - y) y q) :
    False := by
  have hyz : y ≤ z := Nat.le_of_lt (right_lt_of_fermat5Equation hPack.hx hPack.hEq)
  have hBodyEq : Body5 (z - y) y = x ^ 5 :=
    body5_eq_fifth_power_of_fermat hyz hPack.hEq
  have hqDivPow : q ∣ x ^ 5 := by
    rw [← hBodyEq]
    exact hClean.dvd_body
  have hqDivX : q ∣ x := hClean.prime.dvd_of_dvd_pow hqDivPow
  have hlower : 5 ≤ padicValNat q (x ^ 5) :=
    padicValNat_lower_bound_d5 hPack.hx hClean.prime hqDivX
  have hexact : padicValNat q (Body5 (z - y) y) = 1 := by
    simpa [Body5] using padicValNat_clean_body_eq_one hClean
  rw [hBodyEq] at hexact
  omega
```

この theorem は、primitive な FLT5 候補 `CounterexamplePack x y z` と、その自然数 gap `z - y` に対する clean prime channel が同時には存在できないことを、`padicValNat` による局所付値だけで証明する。

## 数学的主張

Fermat-five の式

$$
x^5+y^5=z^5
$$

と $y\le z$ から、gap を

$$
g=z-y
$$

と置けば fifth-power body は

$$
\operatorname{Body5}(g,y)=g\,GN_5(g,y)=x^5
$$

となる。

一方、`CleanGN5Channel g y q` は、素数 $q$ が body に一度だけ現れる clean channel を与える。0415 により

$$
v_q(g\,GN_5(g,y))=1
$$

である。

しかし body は $x^5$ そのものであり、clean channel から $q\mid x^5$、素数性から $q\mid x$ が従う。0413 により

$$
5\le v_q(x^5)
$$

である。

body identity により両者は同じ自然数の付値なので、

$$
5\le v_q(x^5)=1
$$

となり矛盾する。

したがって

$$
\operatorname{CounterexamplePack}(x,y,z)
\land
\operatorname{CleanGN5Channel}(z-y,y,q)
\Longrightarrow \bot.
$$

## 証明全体での役割

この theorem は `Valuation.lean` の独立 proof route の終端である。

`CleanChannel.lean` には既に、clean channel が full body を第五冪にすることを直接の可除性議論で否定する route がある。一方 `Valuation.lean` は同じ obstruction を

```text
fifth power   -> q-adic valuation ≥ 5
clean channel -> q-adic valuation = 1
```

として再構成する。

0413 `padicValNat_lower_bound_d5` が第五冪側の下界、0414 が clean body の上界、0415 が exact valuation $=1$ を与え、0416 が Fermat body identity を介して二つを同一量へ移し、最終矛盾を閉じる。

従ってこの theorem は FLT5 全体の main closure に必須な唯一の route ではなく、clean-channel obstruction の独立な valuation 証明である。正本の module comment も、この route が `CleanChannel.lean` の直接証明と独立であることを明記している。

## 直接依存する定義・補題

### `CounterexamplePack`

`hPack : CounterexamplePack x y z` から少なくとも

```lean
hPack.hx : 0 < x
hPack.hEq : Fermat5Equation x y z
```

を使用する。

`hPack.hx` は 0413 の正値条件に、`hPack.hEq` は gap/body identity に使われる。

### `CleanGN5Channel`

```lean
hClean : CleanGN5Channel (z - y) y q
```

から本 theorem が直接使うのは

```lean
hClean.prime
hClean.dvd_body
```

であり、0415 を介して `not_sq_dvd_body` に由来する exact valuation も利用する。

### `right_lt_of_fermat5Equation`

```lean
right_lt_of_fermat5Equation hPack.hx hPack.hEq : y < z
```

を与える。これを `Nat.le_of_lt` で $y\le z$ に弱め、自然数減算 `z - y` を通常の gap として安全に扱う。

### `body5_eq_fifth_power_of_fermat`

```lean
body5_eq_fifth_power_of_fermat hyz hPack.hEq :
  Body5 (z - y) y = x ^ 5
```

が valuation route と Fermat equation を接続する中心 bridge である。

### `Nat.Prime.dvd_of_dvd_pow`

```lean
hClean.prime.dvd_of_dvd_pow hqDivPow
```

によって

$$
q\mid x^5 \Longrightarrow q\mid x
$$

を得る。

### `padicValNat_lower_bound_d5`

0413。

```lean
padicValNat_lower_bound_d5 hPack.hx hClean.prime hqDivX
```

により

```lean
5 ≤ padicValNat q (x ^ 5)
```

を得る。

### `padicValNat_clean_body_eq_one`

0415。

```lean
padicValNat_clean_body_eq_one hClean
```

は

```lean
padicValNat q ((z - y) * GN5 (z - y) y) = 1
```

を与える。`Body5` を展開して `Body5 (z-y) y` の形へ合わせる。

## 証明の流れ

### 1. gap の順序条件を得る

```lean
have hyz : y ≤ z :=
  Nat.le_of_lt (right_lt_of_fermat5Equation hPack.hx hPack.hEq)
```

正の $x$ を含む Fermat-five equation では $y<z$ なので、自然数 gap `z - y` は本来の差として扱える。

### 2. body を第五冪へ同定する

```lean
have hBodyEq : Body5 (z - y) y = x ^ 5 :=
  body5_eq_fifth_power_of_fermat hyz hPack.hEq
```

これが proof の輸送路である。以後、同じ数を clean body としても第五冪としても読む。

### 3. clean prime が $x^5$ を割ることを得る

```lean
have hqDivPow : q ∣ x ^ 5 := by
  rw [← hBodyEq]
  exact hClean.dvd_body
```

`hClean.dvd_body` は clean prime が full body を割るという既存 API である。

### 4. 素数性により root へ降ろす

```lean
have hqDivX : q ∣ x :=
  hClean.prime.dvd_of_dvd_pow hqDivPow
```

素数 $q$ が第五冪を割るなら底 $x$ を割る。

### 5. 第五冪側の valuation lower bound を得る

```lean
have hlower : 5 ≤ padicValNat q (x ^ 5) :=
  padicValNat_lower_bound_d5 hPack.hx hClean.prime hqDivX
```

ここで 0413 がそのまま再利用される。

### 6. clean body 側の exact valuation を得る

```lean
have hexact : padicValNat q (Body5 (z - y) y) = 1 := by
  simpa [Body5] using padicValNat_clean_body_eq_one hClean
```

0415 の対象は `(z-y) * GN5 (z-y) y` であり、`Body5` の定義展開だけで同じ式になる。

### 7. body identity で valuation を第五冪側へ輸送する

```lean
rw [hBodyEq] at hexact
```

これにより

```lean
hexact : padicValNat q (x ^ 5) = 1
```

となる。

### 8. 算術矛盾を閉じる

```lean
omega
```

`hlower : 5 ≤ ...` と `hexact : ... = 1` から不可能性を判定し、`False` を得る。

## Lean 固有の処理

### `Nat.le_of_lt`

body identity の API が `y ≤ z` を要求する一方、既存補題は強い `y < z` を返す。そのため単なる order weakening を行っている。

### `rw [← hBodyEq]`

divisibility の目標 `q ∣ x ^ 5` を clean-channel API が理解できる body 側へ戻す。数学的には等しい対象の置換だけである。

### `dvd_of_dvd_pow`

一般の合成数では成り立たない prime-specific step を `hClean.prime` が保証する。ここで `CleanGN5Channel` の素数性 field が実質的に使われる。

### `simpa [Body5]`

0415 の theorem statement と本 theorem の preferred abstraction `Body5` の間の definitional difference を吸収する。新しい数学はない。

### `rw [hBodyEq] at hexact`

等式を目標ではなく局所仮定の中へ rewrite する。これにより `hlower` と `hexact` の `padicValNat` 対象が syntactically 同一になる。

### `omega`

最後は自然数の線形算術だけである。付値論そのものはすでに 0413 と 0415 に封じ込められている。

## 冗長・重複箇所

### direct clean-channel contradiction と数学的 obstruction が重複する

`CleanChannel.lean` の `not_fifth_power_body_of_clean` は、clean body が第五冪であることを二乗可除性から直接否定する。0416 は同じ obstruction を valuation の言葉で再証明する。

これは accidental duplication ではなく、正本自身が「independent `padicValNat` proof」と位置づけた意図的な二重化である。

### `hqDivPow` → `hqDivX` は第五冪 lower bound の前処理

0413 は入力として `q ∣ x` を要求するため、本 theorem 側で `q ∣ x^5` から root divisibility を復元している。0413 を「`q ∣ x^5` から直接 $v_q(x^5)\ge5$」という variant にすれば一段短縮できるが、現在の 0413 の方が一般的で意味が明瞭である。

### `Body5` と積表示の往復

0415 は積表示、0416 は `Body5` abstraction を使うため `simpa [Body5]` が必要になる。小さな表現上の重複である。

## 最適化候補

### 1. valuation contradiction を抽象 helper にする

一般形として

```text
body = x^5
q ∣ body
v_q(body) = 1
```

から `False` を出す helper は抽出可能である。ただし FLT5 固有の `Body5` identity が証明の可読性を高めているため、現状の具体形にも価値がある。

### 2. `Body5` 版 exact-valuation wrapper を用意する

例えば `padicValNat_clean_Body5_eq_one` のような wrapper があれば

```lean
simpa [Body5]
```

を本 theorem から除ける。ただし一箇所だけなら API を増やすほどではない。

### 3. direct route と valuation route の共通 transport を分離する

`hBodyEq` と `hClean.dvd_body` から `q ∣ x^5` を得る部分は、direct clean-channel proof と類似する transport layer として再利用できる可能性がある。

### 4. `omega` を明示的 contradiction に置換する必要は薄い

`hlower` と `hexact` から `5 ≤ 1` を作って `omega` で閉じる現行形は短く明快である。proof object をより説明的にしたければ `omega` 前に `have : 5 ≤ 1 := by omega` のように分離できるが、Lean コードとしては冗長になる。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

0416 が直接または依存補題を通して必要とする Mathlib 機能は少なくとも次を含む。

- `padicValNat`
- `Nat.Prime.dvd_of_dvd_pow`
- 自然数の順序 API (`Nat.le_of_lt`)
- divisibility
- `omega`

ただし production source の個別 module import は standalone 生成物からは確認できず、この実行では Lean build も行っていないため、最小 import 集合は未確認である。`import Mathlib` から valuation・prime・omega に関する個別 import へ縮小できる可能性は高いが、実際の最小化には build 検証が必要である。

## Comparator challenge 化の可否

**可能であり、0413〜0416 をまとめると良い challenge になる。**

0416 単独では多くの domain lemma が既に与えられているため短いが、challenge としては次の構造を評価できる。

1. Fermat equation から body identity を得る。
2. clean channel の divisibility を第五冪へ transport する。
3. prime divisibility を base へ降ろす。
4. 第五冪側 valuation $\ge5$ を得る。
5. clean body 側 exact valuation $=1$ を得る。
6. equality transport 後に矛盾を閉じる。

特に `padicValNat` API、rewrite orientation、`Body5` の unfolding、prime power divisibility を同時に扱うため、単純な `ring` challenge より Lean 固有の判断点が多い。

一方、FLT5 の研究的核心である黄金整数・unit class・無限降下を問う challenge ではない。これは局所付値 obstruction の機械検証能力を測る challenge である。

## 次に読むべき宣言

次は `Main.lean` に入り、**0417 `FLT5Target`** を読むべきである。

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

宣言種別は `abbrev`。

0416 で独立 valuation route が完結し、その次からは FLT5 development 全体の公開 endpoint 層に入る。`FLT5Target` は正の自然数における指数 5 の最終否定命題を型として固定し、後続の conditional receiver と unconditional theorem `flt5Target` の codomain になる。