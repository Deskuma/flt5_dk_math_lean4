# 0034 — `branchB_false_of_fifthPowerCore`

## 宣言

```lean
theorem branchB_false_of_fifthPowerCore
    (hCore : BranchBFifthPowerCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  rcases exists_branchB_fifthPowerNormalForm hPack hBranch with ⟨a, b, hNF⟩
  exact hCore hNF.a_pos hNF.pack.hy hNF.coprime_a_y
    hNF.five_not_dvd_a hNF.GN_eq
```

## Lean の型

本定理は、Branch B の残存算術核を排除する仮定

```lean
hCore : BranchBFifthPowerCore
```

を受け取り、任意の `CounterexamplePack x y z` と Branch B 条件

```lean
hBranch : ¬ 5 ∣ z - y
```

から `False` を返します。

`BranchBFifthPowerCore` は前号で導入された略称であり、展開すると次の universal refuter です。

```lean
∀ {a b y : ℕ},
  0 < a →
  0 < y →
  Nat.Coprime a y →
  ¬ 5 ∣ a →
  GN5 (a ^ 5) y = b ^ 5 →
  False
```

## 数学的主張

Branch B の反例候補から完全標準形を構成すると、ある自然数 $a,b$ が存在して、

$$
a>0,\qquad y>0,\qquad \gcd(a,y)=1,\qquad 5\nmid a,
$$

かつ、

$$
GN5(a^5,y)=b^5
$$

を満たします。

一方 `hCore` は、そのような $a,b,y$ の存在を一律に排除します。したがって Branch B の `CounterexamplePack` は存在できません。

## 証明全体での役割

本定理は、elementary reduction と後続の深い数論を接続する adapter です。

- provider 側の `exists_branchB_fifthPowerNormalForm` は、反例候補から完全な正規形パケットを構成する。
- consumer 側の `BranchBFifthPowerCore` は、そのパケットのうち反証に必要な五つの成分だけを要求する。
- 本定理は、パケットから必要成分を射影して core に渡す。

この分離により、後続の黄金整数・降下法は元の $x,y,z$ や第五冪方程式を直接扱わず、縮約済みの `GN5` 方程式だけを反証すればよくなります。

## 直接依存する定義・補題

### `BranchBFifthPowerCore`

反証器の最小インターフェースです。必要な仮定を curried implication として並べます。

### `CounterexamplePack`

正値性、原始性、第五冪方程式を束ねた元の反例候補です。本定理では `hPack` 自体を直接分解せず、provider に渡します。

### `exists_branchB_fifthPowerNormalForm`

`hPack` と `hBranch` から、

```lean
∃ a b, BranchBFifthPowerNormalForm x y z a b
```

を構成する provider です。

### `BranchBFifthPowerNormalForm` の射影

本定理が使用するのは次の五項だけです。

```lean
hNF.a_pos
hNF.pack.hy
hNF.coprime_a_y
hNF.five_not_dvd_a
hNF.GN_eq
```

## 証明の流れ

1. `exists_branchB_fifthPowerNormalForm hPack hBranch` を適用する。
2. `rcases` により witness `a`, `b` と標準形 `hNF` を取り出す。
3. `hCore` に、`a>0`、`y>0`、`Coprime a y`、`5∤a`、`GN5(a^5,y)=b^5` を順に渡す。
4. core が返す `False` で証明を閉じる。

新しい整数論的推論はありません。先行 provider と抽象 consumer の型を正確に接続することが本定理の全内容です。

## Lean 固有の処理

### `rcases` による二重存在の除去

```lean
rcases exists_branchB_fifthPowerNormalForm hPack hBranch with ⟨a, b, hNF⟩
```

は、二つの存在量化を一度に除去し、最後の構造体証拠を `hNF` として保持します。

### 構造体フィールドの射影

`hNF.pack.hy` は、標準形が内部に保持する元の `CounterexamplePack` から $y>0$ を取り出します。他の四項は標準形自身のフィールドです。

### curried proposition の適用

`BranchBFifthPowerCore` は関数型の連鎖なので、五つの証拠を空白区切りで順に適用できます。暗黙変数 `{a b y}` は渡された証拠と `hNF.GN_eq` の型から推論されます。

### `abbrev` の透過性

`BranchBFifthPowerCore` は `abbrev` であり、Lean は必要に応じて定義を透過的に展開します。そのため明示的な `unfold BranchBFifthPowerCore at hCore` は不要です。

## 冗長・重複箇所

証明本体は既に最小に近く、数学的重複はありません。

ただし設計上、`hNF.pack.hy` だけが入れ子の射影で、残りは `hNF` の直下にあります。後続 adapter が同じ五項を繰り返し抽出するなら、標準形から core の入力を束ねる補助定理または小さな packet を導入する余地があります。

一方、この一回だけの利用なら現在の直接射影の方が読みやすく、補助 API の追加は過剰抽象化になり得ます。

## 最適化候補

### 1. term proof 化

現在の証明は十分短いですが、`obtain` を含むため完全な一行 term proof には向きません。`Exists.elim` を使えば式として書けるものの、可読性は低下します。現状維持が妥当です。

### 2. core 適用用 adapter の抽出

未検証案として、次のような定理を置けます。

```lean
theorem BranchBFifthPowerNormalForm.false_of_core
    (hNF : BranchBFifthPowerNormalForm x y z a b)
    (hCore : BranchBFifthPowerCore) : False :=
  hCore hNF.a_pos hNF.pack.hy hNF.coprime_a_y
    hNF.five_not_dvd_a hNF.GN_eq
```

すると本定理は provider の存在除去と `hNF.false_of_core hCore` だけになります。ただし現時点では一箇所の短縮に留まるため、API 増加との釣り合いを要します。

### 3. core を packet consumer にする案

`BranchBFifthPowerCore` を

```lean
∀ {x y z a b}, BranchBFifthPowerNormalForm x y z a b → False
```

と定めれば本定理はさらに短くなります。しかし、それでは不要な $x,z$、`x_eq`、`z_eq`、他の互いに素性まで core 境界へ持ち込み、前号で達成した最小化を失います。現在の設計の方が依存境界として優れています。

## 必要 Mathlib import と import 最適化候補

確認できる standalone artifact は `import Mathlib` を使用しています。本定理自身が直接使う Lean 機能は、存在除去、構造体射影、関数適用だけです。数学補題を直接呼びません。

実モジュール単位では、ローカル宣言の依存として `NormalForm` より前の Reduction/NormalForm 構築部が必要です。最小 import はプロジェクト内モジュール依存に従うべきであり、本記事だけから個別 Mathlib import を断定できません。

未検証の import 最適化候補は次の通りです。

- 本定理だけなら Mathlib の算術・tactic import は新たに不要。
- `rcases` が利用可能な基礎 tactic/import と、`BranchBFifthPowerCore` および provider を供給するローカルモジュールで足りる可能性が高い。
- 実際の最小 import は別ブランチまたは一時ファイルでビルド検証すべきであり、本作業では Lean ビルドを行っていません。

## Comparator challenge 化の可否

適しています。難度は初級です。

### Challenge

次の宣言を完成させます。

```lean
theorem challenge
    (hCore : BranchBFifthPowerCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False := by
  sorry
```

### 評価観点

- `exists_branchB_fifthPowerNormalForm` を発見できるか。
- 二重存在を `rcases` で取り出せるか。
- core が必要とする五つのフィールドを正しい順序で選べるか。
- 不要な標準形フィールドを使わずに閉じられるか。

Comparator 用には、単なる文字列一致ではなく、provider/consumer 境界を維持した短い証明であることを評価できます。

## 根拠と推測の区別

Lean 宣言型、証明本体、使用フィールド、`NormalForm.lean` の末尾に置かれていることは repository 内の生成済み standalone Lean ソースで確認しました。

import の最小化、補助 adapter の追加、core の別表現に関する記述は未検証の設計提案です。

## 次に読むべき定理

次は `DkMath.FLT.Five.FifthPowerCore` を読むのが依存順として自然です。

`branchB_false_of_fifthPowerCore` は Branch B 専用の core adapter を完成させました。次の `BranchB.lean` 層では、Branch A/B の routing や、より上位の共通反証インターフェースへ進むための宣言が始まります。実際の次宣言名は Lean ソースの直後を基準に確定し、目録へ反映します。
