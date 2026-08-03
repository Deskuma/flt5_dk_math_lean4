# 0001 — `Fermat5Equation`

## 1. 展示対象

```lean
namespace DkMath.FLT.Five

/-- The equation `x^5 + y^5 = z^5` over natural numbers. Positivity is deliberately
kept outside this definition and supplied by `CounterexamplePack` or `FLT5Target`. -/
def Fermat5Equation (x y z : ℕ) : Prop :=
  x ^ 5 + y ^ 5 = z ^ 5

end DkMath.FLT.Five
```

完全修飾名は次です。

```lean
DkMath.FLT.Five.Fermat5Equation
```

Lean 上の型は次の関数型です。

```lean
ℕ → ℕ → ℕ → Prop
```

すなわち、三つの自然数を受け取り、それらが指数 5 のフェルマー方程式を満たすという命題を返します。

## 2. 数学的主張

`Fermat5Equation x y z` は、単に次の等式の別名です。

$$
x^5+y^5=z^5
$$

この定義自身は、解が存在するとも存在しないとも主張しません。また、`x`、`y`、`z` の正値性、互いに素であること、順序関係も含みません。

これはソースコメントにも明記されており、正値性は後続の `CounterexamplePack` または最終入口側の `FLT5Target` が供給します。

## 3. 証明全体での役割

この宣言は FLT5 形式化の最小入口です。

証明全体では、次の二種類の情報を分離するために使われます。

1. 方程式そのもの
2. 正値性・原始性など、反例候補を正規化する追加条件

方程式を独立した述語にしておくことで、後続補題は必要な仮定だけを受け取れます。実際、直後の基礎層では次のように使い分けられます。

- `fifth_sub_eq_of_add_eq` は方程式だけを受け取る。
- `right_lt_of_fermat5Equation` は方程式と `0 < x` を受け取る。
- `gap_pos_of_fermat5Equation` も方程式と `0 < x` を受け取る。
- `CounterexamplePack` は方程式に正値性と `Nat.Coprime x y` を束ねる。

したがって本定義は、後続の gap 座標、`GN5` 分解、5 進分岐、黄金整数環、無限降下へ進む前の共通インターフェースです。

## 4. 直接依存する定義・演算

リポジトリ内の独自宣言には依存しません。直接使っているのは Lean/Mathlib 側の基本要素だけです。

- `ℕ`：自然数型
- `Nat.pow` と冪記法 `^`
- 自然数加法 `+`
- 等式 `=`
- 命題型 `Prop`

依存関係を概念的に書けば次の通りです。

```text
Nat, Nat.pow, Nat.add, Eq, Prop
  └─ Fermat5Equation
       ├─ CounterexamplePack
       ├─ fifth_sub_eq_of_add_eq
       ├─ right_lt_of_fermat5Equation
       └─ gap_pos_of_fermat5Equation
```

## 5. 定義の流れ

この宣言には tactic 証明はありません。右辺の命題を名前付き述語として包装しているだけです。

1. `x y z : ℕ` を受け取る。
2. 各変数の 5 乗を作る。
3. 左辺二項を加算する。
4. その値が `z ^ 5` と等しいという `Prop` を返す。

`def` なので、必要な場所では `unfold Fermat5Equation` によって元の等式へ展開できます。

## 6. Lean 固有の処理

### 6.1 命題を `def` で包装する

数学的には単なる等式ですが、Lean では名前を付けることで API 境界になります。後続コードは、生の等式を毎回書く代わりに `Fermat5Equation x y z` を仮定として受け取れます。

### 6.2 正値性を定義へ混ぜない

`ℕ` には `0` が含まれるため、本定義だけでは自明解を排除しません。これは欠落ではなく意図的な責務分離です。正値性は `CounterexamplePack` などで追加されます。

### 6.3 展開は定義的等価性で行える

後続の `fifth_sub_eq_of_add_eq` と `right_lt_of_fermat5Equation` は、冒頭で次を実行します。

```lean
unfold Fermat5Equation at hEq
```

これにより、名前付き述語から生の自然数等式へ戻し、`omega` や冪に関する補題へ渡せます。

## 7. 冗長・重複箇所

本定義そのものには実質的な冗長性はありません。

ただし、リポジトリの公開入口 `PNat.pow_add_pow_ne_pow_five` では `ℕ+` 上の等式を `Subtype.ext_iff.mp` で自然数の等式へ戻した後、最終定理へ渡しています。これは本定義と競合する重複ではなく、正自然数 API と内部の自然数 API の境界処理です。

推測を含む監査候補としては、後続コード中に生の

```lean
x ^ 5 + y ^ 5 = z ^ 5
```

が繰り返し現れる場合、それらを `Fermat5Equation` に統一できる可能性があります。ただし、書き換えや自動化の都合で生の等式が有利な箇所もあるため、機械的な一括置換は勧められません。

## 8. 最適化候補

### 8.1 `[simp]` 属性は付けない方がよい

この定義を常時展開する `[simp]` 定義にすると、API 名を保つ利点が薄れ、ゴール表示が不必要に大きくなる可能性があります。現在のように必要な箇所だけ `unfold` する設計が明瞭です。

### 8.2 一般指数化は別層に置く

次のような一般述語へ抽象化する案は考えられます。

```lean
def FermatEquation (n x y z : ℕ) : Prop :=
  x ^ n + y ^ n = z ^ n
```

しかし、このリポジトリは指数 5 に特化しており、後続の `GN5`、5 進評価、黄金整数環が指数 5 固有です。したがって、現時点での一般化はコード量だけを増やす可能性があります。共通 FLT 基盤を別モジュールに作る場合のみ検討価値があります。

### 8.3 `abbrev` 化は不要

単なる別名なので `abbrev` も候補に見えますが、証明 API の明示的な境界として保持し、展開を制御できる `def` の方が適切です。

## 9. Mathlib import 監査

standalone ファイル全体は次を import しています。

```lean
import Mathlib
```

本定義単体に必要なのは自然数、冪、加法、等式、`Prop` だけです。したがって `import Mathlib` は本宣言だけを見る限り大幅に広い import です。

未検証の最小化候補は次です。

- Lean の標準前置環境だけで成立する可能性
- 明示 import が必要なら、自然数の基本演算を提供する小さな Mathlib モジュール

ただし、このファイルは多数の生成済みモジュールを一つへ結合した standalone 成果物です。ファイル全体の import は後続の代数・数論・tactic 群により決まるため、この一宣言を理由に standalone の `import Mathlib` を削るべきではありません。

正確な最小 import は、宣言を独立ファイルへ切り出して Lean ビルドで検証する必要があります。本回はビルドを行っていないため、候補に留めます。

## 10. Comparator challenge 化

単独では証明を含まないため、通常の「二つの証明を比較する」Comparator challenge には不向きです。

ただし、次の小課題にはできます。

### Challenge A — 包装と展開

```lean
theorem fermat5Equation_iff (x y z : ℕ) :
    Fermat5Equation x y z ↔ x ^ 5 + y ^ 5 = z ^ 5 := by
  rfl
```

比較対象は `rfl`、`simp [Fermat5Equation]`、`constructor` を使う冗長な証明です。

### Challenge B — API 設計比較

`def`、`abbrev`、生の等式を直接使う三設計を比較し、ゴール表示、展開制御、後続補題の可読性を評価できます。

したがって Comparator 化の判定は **限定的に可** です。数学的難度ではなく Lean API 設計の比較課題になります。

## 11. 根拠と推測の区別

Lean ソースから直接確認できる事実は次です。

- 本定義の完全な型と右辺
- 正値性を定義外に置く設計意図
- `CounterexamplePack` が正値性・互いに素・方程式を束ねること
- 直後の三補題が本定義を展開して使うこと
- standalone が `import Mathlib` を使用すること

一方、import の最小候補、一般指数化の是非、Comparator 課題としての価値判断は、本記事の監査・設計上の提案であり、Lean ビルドによる検証済み事実ではありません。

既存の日本語・英語 PDF は、指数 5 の証明経路を 5 進評価、黄金整数環、無限降下へ進める説明資料です。本記事では、PDF の叙述よりもリポジトリ内の Lean 宣言を第一の根拠とし、PDF から本定義以上の主張を追加していません。

## 12. 次に読むべき宣言

次は次の構造体です。

```lean
DkMath.FLT.Five.CounterexamplePack
```

理由は、`Fermat5Equation` だけでは含まれない正値性と原始性を束ね、後続の局所因数分解が受け取る「正の原始反例候補」を初めて形成するからです。

---

[prev](./README.md) < 0001 > [next](./0002-CounterexamplePack.md)
