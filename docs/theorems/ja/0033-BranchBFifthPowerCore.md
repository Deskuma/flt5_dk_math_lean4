# 0033 — `BranchBFifthPowerCore`

## 宣言

```lean
abbrev BranchBFifthPowerCore : Prop :=
  ∀ {a b y : ℕ},
    0 < a →
    0 < y →
    Nat.Coprime a y →
    ¬ 5 ∣ a →
    GN5 (a ^ 5) y = b ^ 5 →
    False
```

## 数学的主張

任意の自然数 $a,b,y$ に対し、

$$
a>0,\qquad y>0,
$$

$$
\gcd(a,y)=1,\qquad 5\nmid a,
$$

$$
GN5(a^5,y)=b^5
$$

が同時に成立することはない、という命題を一つの略称として定める。

同値に、この条件を満たす `GN5` の完全第五冪表示をすべて排除できれば、Branch B の elementary reduction 後に残る算術核を閉じたことになる。

## 証明全体での役割

`BranchBFifthPowerCore` は定理の証明ではなく、後続の数論が供給すべき **consumer interface** である。前号の `exists_branchB_fifthPowerNormalForm` は反例候補から $a,b$ と完全標準形を構成する。本宣言は、その標準形から最終矛盾を得るために本当に必要な入力だけを抽出する。

重要なのは、完全標準形が保持する十二個のフィールドすべてを要求していない点である。ここでは `a_pos`、`pack.hy`、`coprime_a_y`、`five_not_dvd_a`、`GN_eq` のみを残し、$x,z$、Branch B 仮定そのもの、$x=ab$、$z=y+a^5$、$b$ の正値性、ほかの互いに素性をインターフェースから落としている。

したがってこれは、Reduction/NormalForm 層と、square/golden・黄金整数・降下法の実装との間に置かれた最小境界である。

## 直接依存する定義・補題

リポジトリ内の直接依存は次の二つである。

- `GN5`
- 自然数上の命題・整除性・互いに素性

構文上は既存定理を呼び出さない。`abbrev` の右辺で使う主要な型・記号は次のとおりである。

- `ℕ`
- `Nat.Coprime`
- `Dvd.dvd` の記法 `∣`
- 関数型 `→`
- 全称量化 `∀`
- `False`

## 証明の流れ

本宣言自身には証明項がない。論理構造は次の五段の入力列である。

1. $a$ が正である。
2. $y$ が正である。
3. $a$ と $y$ が互いに素である。
4. 例外素数 $5$ は $a$ を割らない。
5. `GN5 (a^5) y` が $b^5$ に等しい。

これらを受け取った consumer は `False` を返さなければならない。

Lean の関数型として読むと、最後の等式までを順に適用して初めて矛盾が得られる curried interface である。

## Lean 固有の処理

### `abbrev` と定義展開

`abbrev` は透過的な略称であり、通常の elaboration や reduction では右辺の命題へ容易に展開される。独立したデータ構造を作るのではなく、長い高階命題へ短い名前を与えている。

### 暗黙量化された変数

```lean
∀ {a b y : ℕ}, ...
```

の波括弧により、`a`、`b`、`y` は暗黙引数になる。consumer を適用する側では、後続の仮定、とくに `GN5 (a ^ 5) y = b ^ 5` の型から Lean が三変数を推論できる。

### `¬ 5 ∣ a` の結合

Lean では `¬ 5 ∣ a` は `¬ (5 ∣ a)`、すなわち `(5 ∣ a) → False` である。関数矢印の列の一要素として扱われる。

### `False` を返す API

結論を否定存在形ではなく `False` としたため、完全標準形を構成した後の consumer は仮定を直接順番に渡せる。直後の `branchB_false_of_fifthPowerCore` はまさにこの形を利用する。

## 冗長・重複箇所

宣言そのものに証明の重複はない。ただし `BranchBFifthPowerNormalForm` が保持する情報に比べ、本 core は非常に狭い。これは欠落ではなく意図的な依存縮約である。

一方で、`b` の正値性を要求しない点は注目に値する。`GN5(a^5,y)=b^5` と $a,y>0$ から必要なら導出できる可能性があり、現在の後続証明には入力として不要と判断されたと読める。ただし、これが設計上の明示的意図であるかはコメント以上には確認できないため、解釈を含む。

## 最適化候補

以下は未検証の提案である。

1. consumer が標準形構造体を直接受け取る設計、

```lean
∀ {x y z a b}, BranchBFifthPowerNormalForm x y z a b → False
```

も可能だが、不要な依存が増える。現在の core の方が後続算術の再利用性は高い。

2. 命題を否定存在形、

```lean
¬ ∃ a b y : ℕ,
  0 < a ∧ 0 < y ∧ Nat.Coprime a y ∧
  ¬ 5 ∣ a ∧ GN5 (a ^ 5) y = b ^ 5
```

として表す案もある。現形式は provider から得た証拠を順に適用しやすく、否定存在形は数学的な表示が読みやすい。Comparator で両者の証明接続を比較できる。

3. `a^5` を新しい変数 $A$ として抽象化すると一般化できるが、第五冪根 $a$ と $5\nmid a$ の情報が後続の黄金整数処理に重要なら、現在の形を保つべきである。

## 必要 Mathlib import と import 最適化候補

確認済みの standalone 生成物は `import Mathlib` を使う。本宣言単体が必要とする Mathlib 機能は自然数、冪、整除性、`Nat.Coprime`、基本論理に限られる。

元の分割ソース `NormalForm.lean` の個別 import 行は、この回に取得できたブランチ資料では確認できなかった。細分化候補としては次が考えられるが未検証である。

- `Mathlib.Data.Nat.GCD.Basic`
- 自然数の冪と整除性を提供する基礎モジュール
- 前段の DkMath `GN5` モジュール

本宣言だけなら `omega` や `ring` は不要である。ただし同一ファイル内の周辺定理がそれらを要求する可能性があるため、ファイル単位の import 最小化には Lean ビルドによる検証が必要である。本作業ではビルドしていない。

## Comparator challenge 化

適している。宣言が短く、論理インターフェース設計を比較しやすい。

1. **初級** — curried 形式と否定存在形式の同値を証明する。
2. **中級** — `BranchBFifthPowerNormalForm` から core が要求する五つの証拠を射影し、`False` を得る adapter を書く。
3. **設計比較** — core に `0<b` や `Nat.Coprime b y` を加えた版と現在版を比較し、後続証明に本当に必要な最小入力を調べる。

## 根拠と推測の区別

宣言型、`abbrev` であること、直後に `branchB_false_of_fifthPowerCore` が続くことは、リポジトリ内の生成済み `Flt5DkMath/FLT5StandAlone.lean` で確認した。

`b_pos` を省いた設計意図、import 細分化、否定存在形への変更案は未検証の解釈・提案である。

## 次に読むべき定理

```text
DkMath.FLT.Five.branchB_false_of_fifthPowerCore
```

これは `exists_branchB_fifthPowerNormalForm` が供給する完全標準形から、本 core が要求する五つのフィールドだけを取り出して適用し、任意の Branch B `CounterexamplePack` を反証する adapter 定理である。
