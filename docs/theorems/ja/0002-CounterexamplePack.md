# 0002 — `CounterexamplePack`

## 1. 展示対象

```lean
namespace DkMath.FLT.Five

/-- A positive primitive candidate for the exponent-five equation.  The condition
`Coprime x y` is the normalization needed by every subsequent local factorization. -/
structure CounterexamplePack (x y z : ℕ) : Prop where
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
  hxy : Nat.Coprime x y
  hEq : Fermat5Equation x y z

end DkMath.FLT.Five
```

完全修飾名は次です。

```lean
DkMath.FLT.Five.CounterexamplePack
```

Lean 上では、固定された `x y z : ℕ` に対して命題を返す構造体です。

```lean
CounterexamplePack (x y z : ℕ) : Prop
```

## 2. 数学的主張

`CounterexamplePack x y z` は、三つの自然数が次を同時に満たすことを表します。

1. `x`, `y`, `z` はすべて正である。
2. `x` と `y` は互いに素である。
3. 指数5のフェルマー方程式を満たす。

$$
x^5+y^5=z^5
$$

つまり、単なる解候補ではなく、後続の局所因数分解に使える **正の原始反例候補** を一つの型へ束ねたものです。

ここで「原始」は `Nat.Coprime x y` のみによって記録されます。`x` と `z`、`y` と `z` の互いに素性は構造体のフィールドに含まれず、方程式から後で導く設計です。

## 3. 証明全体での役割

`Fermat5Equation` が方程式だけを表す最小述語であったのに対し、`CounterexamplePack` は証明の実働部分が受け取る最初の正規化済み入力です。

後続の gap、5進評価、黄金整数環での因数分解は、零や共通因子を含む任意の三つ組ではなく、正で原始的な候補を前提とします。この構造体は、その前提を一度だけ宣言し、以後は `p.hx`、`p.hxy`、`p.hEq` のような射影として再利用できるようにします。

概念的な流れは次です。

```text
Fermat5Equation x y z
  + positivity of x, y, z
  + Nat.Coprime x y
  └─ CounterexamplePack x y z
       └─ gap / GN5 / five-adic / golden-order reductions
```

## 4. 直接依存する定義・補題

プロジェクト固有の直接依存は一つです。

- `DkMath.FLT.Five.Fermat5Equation`

Lean/Mathlib 側では次を使います。

- `ℕ`
- 自然数の順序 `0 < x`
- `Nat.Coprime`
- `structure ... : Prop`

証明済み補題には依存しません。これはデータと仮定を束ねる宣言です。

## 5. 構成の流れ

この構造体を構成するには、次の五つの証明を順に与えます。

```lean
{
  hx  : 0 < x
  hy  : 0 < y
  hz  : 0 < z
  hxy : Nat.Coprime x y
  hEq : Fermat5Equation x y z
}
```

構成後は、それぞれが射影として取り出せます。

```lean
p.hx
p.hy
p.hz
p.hxy
p.hEq
```

構造体自体は `Prop` に属するため、計算用レコードではなく「これらの仮定が同時に成立する」という証明パッケージです。

## 6. Lean 固有の処理

### 6.1 `structure ... : Prop`

`CounterexamplePack` は `Type` ではなく `Prop` に置かれています。したがって、その主目的は実行時データの保存ではなく、証明仮定の整理です。

Lean の proof irrelevance により、この構造体の異なる証明値を計算上区別する必要はありません。後続は「どの証明を使ったか」ではなく、フィールドが提供する命題だけを利用します。

### 6.2 パラメータ固定型

`x y z` は構造体のフィールドではなくパラメータです。

```lean
structure CounterexamplePack (x y z : ℕ) : Prop where
```

そのため `p : CounterexamplePack x y z` の型を見れば対象の三つ組が確定します。別案として `x y z` 自体をフィールドに持つ閉じたレコードも作れますが、現在の形は定理の暗黙引数とよく噛み合います。

### 6.3 射影による仮定の再利用

多数の仮定を定理ごとに列挙せず、構造体一つを受け取って必要なフィールドだけを使えます。これは証明項の整理と API の安定化に有効です。

## 7. 冗長・重複箇所

フィールドのうち `hz : 0 < z` は、`hx : 0 < x` と方程式から導出できる可能性があります。実際、正の `x` があれば `z^5` は正となるため、`z = 0` は排除できます。

ただし、これは本記事の数学的観察であり、リポジトリ内で `hz` を不要とする補題がこの宣言以前に提供されているわけではありません。明示フィールドとして保持すれば、後続定理は毎回導出せず直接使えます。

同様に、`hy` からも `hz` の正値性を導ける可能性があります。したがって `hz` は論理的には冗長候補ですが、API と証明コストの観点では意図的なキャッシュと見なせます。

`hxy` だけを記録し、`Coprime x z` と `Coprime y z` を記録しない点は冗長削減です。ソースコメントは、他の互いに素性を方程式から導く方針を明示しています。

## 8. 最適化候補

### 8.1 `hz` の導出化

構造体を最小化するなら `hz` を削除し、必要時に補題で導く設計が候補です。ただし、後続での使用頻度、証明項の長さ、simp/omega の安定性を確認せずに削るべきではありません。

### 8.2 名前の意味範囲

`CounterexamplePack` は「反例が存在する」と主張する名前ではなく、仮定された候補を包装する型です。より中立的な `PrimitiveFermat5Data` のような名前も考えられますが、無限降下の背理法入力であることを強調する現名称には十分な意味があります。

### 8.3 一般構造体との共有

指数に依存しない正値性と原始性を一般化した構造体を別層へ置く案もあります。しかし `hEq` の型と後続の局所理論は指数5固有です。他指数との実際の共有箇所が増えるまでは、局所構造体の方が読みやすいでしょう。

## 9. Mathlib import 監査

standalone 全体は `import Mathlib` を使います。

この構造体自身が必要とする機能は小さく、概念的には次だけです。

- 自然数と順序
- `Nat.Coprime`
- 前号の `Fermat5Equation`

`Nat.Coprime` を提供する Mathlib の gcd 系モジュールが、定義単体の主要 import 候補です。ただし正確なモジュール名と推移依存は本回ではビルド検証していません。

standalone は生成済み結合成果物であり、後段の tactic・代数・数論をすべて含むため、この宣言だけを根拠に `import Mathlib` を変更するべきではありません。元の分割モジュール `DkMath/FLT/Five/Basic.lean` で `#min_imports` または独立ビルドを行うのが適切です。

## 10. Comparator challenge 化

Comparator challenge 化は **可** です。定理証明よりも、構造体の構成・分解・最小仮定設計の比較に向きます。

### Challenge A — 構成

```lean
theorem mkCounterexamplePack
    {x y z : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : Nat.Coprime x y)
    (hEq : Fermat5Equation x y z) :
    CounterexamplePack x y z := by
  exact ⟨hx, hy, hz, hxy, hEq⟩
```

`exact ⟨...⟩`、`constructor` の反復、名前付きフィールド構文を比較できます。

### Challenge B — 分解

```lean
theorem unpackCounterexamplePack
    {x y z : ℕ}
    (p : CounterexamplePack x y z) :
    0 < x ∧ 0 < y ∧ 0 < z ∧ Nat.Coprime x y ∧
      Fermat5Equation x y z := by
  exact ⟨p.hx, p.hy, p.hz, p.hxy, p.hEq⟩
```

射影、`rcases p with ⟨...⟩`、`simpa` の可読性を比較できます。

## 11. 根拠と推測の区別

Lean ソースから直接確認できる事実は次です。

- 五つのフィールドとその型
- `CounterexamplePack ... : Prop` であること
- `Nat.Coprime x y` のみを明示的に記録すること
- 後続の gap、5進、二次整数環還元の原始入力であるというモジュールコメント

一方、`hz` が論理的に冗長である可能性、名称変更、一般化、import 最小化は監査上の提案です。今回は Lean ビルドを実行していません。

## 12. 次に読むべき宣言

次は次の補題です。

```lean
DkMath.FLT.Five.fifth_sub_eq_of_add_eq
```

`CounterexamplePack` が反例候補の仮定を束ねた後、証明経路で最初に必要になる代数変換は、加法形

$$
x^5+y^5=z^5
$$

を差分形

$$
z^5-y^5=x^5
$$

へ移すことだからです。これが自然数の gap と `GN5` 因数分解への入口になります。
