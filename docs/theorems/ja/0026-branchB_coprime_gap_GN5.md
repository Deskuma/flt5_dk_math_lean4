# 0026 — `branchB_coprime_gap_GN5`

## 宣言

```lean
theorem branchB_coprime_gap_GN5
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    Nat.Coprime (z - y) (GN5 (z - y) y) :=
  coprime_gap_GN5_of_coprime_of_five_not_dvd
    (coprime_gap_y_of_counterexamplePack hPack) hBranch
```

## Lean の型

この定理は、正の原始的 FLT5 反例候補を表す `CounterexamplePack x y z` と、Branch B 条件 `¬ 5 ∣ z - y` を受け取り、自然数 gap `z - y` と第五巡回残余核 `GN5 (z - y) y` が互いに素であることを返す。

```lean
CounterexamplePack x y z →
  (¬ 5 ∣ z - y) →
  Nat.Coprime (z - y) (GN5 (z - y) y)
```

## 数学的主張

$g=z-y$ と置く。反例候補の原始性と方程式から、すでに

$$
\gcd(g,y)=1
$$

が得られている。また Branch B では

$$
5\nmid g
$$

を仮定する。前号の一般定理により、この二条件から

$$
\gcd\bigl(g,GN5(g,y)\bigr)=1
$$

が従う。したがって具体的には、

$$
\gcd\bigl(z-y,GN5(z-y,y)\bigr)=1
$$

である。

## 証明全体での役割

第五冪差の因数分解

$$
z^5-y^5=(z-y)GN5(z-y,y)
$$

に現れる二因子を完全に分離する Branch B 専用の接続 API である。後続の `fifth_power_factor_split` と `branchB_fifth_power_factor_split` は、この互いに素性を用いて、積が第五冪なら両因子がそれぞれ第五冪であることを導く。

本定理自身は新しい素因数解析を行わない。前号の一般定理を、`CounterexamplePack` から導かれた具体的な gap 座標へ適用する境界層である。

## 直接依存する定義・補題

1. `CounterexamplePack`
   - `x,y,z` の正値性、`Nat.Coprime x y`、および `x^5+y^5=z^5` を束ねる。
2. `GN5`
   - 第五冪差から gap を除いた次数4の斉次残余核。
3. `coprime_gap_y_of_counterexamplePack`
   - `hPack` から `Nat.Coprime (z-y) y` を供給する。
4. `coprime_gap_GN5_of_coprime_of_five_not_dvd`
   - `Nat.Coprime g y` と `¬ 5 ∣ g` から `Nat.Coprime g (GN5 g y)` を導く一般定理。

## 証明の流れ

証明は一つの関数適用だけで完了する。

1. `coprime_gap_y_of_counterexamplePack hPack` により、

$$
\gcd(z-y,y)=1
$$

を得る。
2. `hBranch` はそのまま

$$
5\nmid z-y
$$

を与える。
3. この二つを一般定理 `coprime_gap_GN5_of_coprime_of_five_not_dvd` に渡す。
4. Lean が `g := z-y` と `y := y` を型から推論し、目的を直接返す。

## Lean 固有の処理

### 暗黙引数の推論

一般定理の変数 `g` と `y` は、第一引数

```lean
coprime_gap_y_of_counterexamplePack hPack
```

の型 `Nat.Coprime (z-y) y` から推論される。明示的な `g := z-y` 指定や `simpa` は不要である。

### term proof

証明は `by` ブロックを使わない term-style で書かれている。結論の型が一般定理の返り値と定義的に一致するため、書き換えも tactic も必要ない。

### 自然数減算の安全性

この宣言では `z-y` を用いるが、減算の正値性や `y≤z` を直接扱わない。それらは前段の `coprime_gap_y_of_counterexamplePack` 内で処理済みである。この抽象化により、本定理は切り捨て減算の技術的処理から隔離されている。

## 冗長・重複箇所

証明本体に計算上の重複はない。一般定理と provider を一行で接続する最小のラッパーである。

ただし API の観点では、同じ結論を呼び出し側で二補題を直接合成して得ることもできる。その意味では論理的には省略可能だが、Branch B の主要不変量に名前を与え、後続証明の意図を明確にする役割があるため、宣言として保持する価値が高い。

## 最適化候補

1. 現在の term proof はほぼ最小であり、証明速度上の最適化余地はない。
2. 引数名 `hBranch` は Branch B 条件を明確にしており、そのままがよい。
3. 将来 Branch B 条件を構造体へ束ねる場合、本補題をその構造体のメソッドまたは namespace API に移す設計は検討できる。これは未検証の設計提案である。
4. 一般定理側の名称が長いため、局所的な可読性を目的に別名を設ける案もあるが、本証明では一度しか現れず利益は小さい。

## 必要 Mathlib import と import 最適化候補

リポジトリの standalone 版は `import Mathlib` を用いているため、この宣言単独の最小 import はソースから確定していない。

本定理自身が直接必要とするのは、自然数、整除性、`Nat.Coprime`、および先行する DkMath 宣言だけである。実際の個別モジュールでは `Reduction.lean` の import を根拠に監査すべきであり、`Mathlib` 全体からの縮小候補として自然数の gcd・coprime・divisibility 関連モジュールが考えられる。ただし、これは Lean ビルドを行っていない未検証の import 最適化案である。

## Comparator challenge 化の可否

適している。ただし数学的難度ではなく、API 合成と暗黙引数推論を比較する小規模 challenge になる。

### 課題案

次の仮定から一行または短い term proof で結論を示す。

```lean
(hPack : CounterexamplePack x y z)
(hBranch : ¬ 5 ∣ z - y)
⊢ Nat.Coprime (z - y) (GN5 (z - y) y)
```

比較対象は次のようにできる。

1. 現行の term-style 合成。
2. `by exact ...` を使う版。
3. 暗黙引数を明示する版。
4. 一般定理を使わず共通素因子反証を再展開する版。

評価軸は、短さだけでなく、依存の明示性、保守性、一般定理の再利用、不要な算術再証明の有無である。

## 根拠と推測の区別

宣言の型、証明本体、直接依存、後続で `fifth_power_factor_split` に渡されることはリポジトリ内 Lean コードで確認した。最小 import の候補と Branch B 構造体化は未検証の設計提案である。

## 次に読むべき定理

```lean
DkMath.FLT.Five.fifth_power_factor_split
```

互いに素な二自然数の積が第五冪なら、それぞれが第五冪であることを示す一般分離定理である。本号で確立した Branch B の互いに素性を、実際の第五冪 normal form へ変換する核心 API となる。