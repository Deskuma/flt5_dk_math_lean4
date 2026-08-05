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

本定理は Branch B の残存算術核を排除する仮定

```lean
hCore : BranchBFifthPowerCore
```

と、任意の `CounterexamplePack x y z`、Branch B 条件

```lean
hBranch : ¬ 5 ∣ z - y
```

を受け取り `False` を返します。

`BranchBFifthPowerCore` を展開すると、

```lean
∀ {a b y : ℕ},
  0 < a → 0 < y → Nat.Coprime a y → ¬ 5 ∣ a →
  GN5 (a ^ 5) y = b ^ 5 → False
```

です。

## 数学的主張

Branch B の反例候補から完全標準形を構成すると、ある自然数 $a,b$ が存在して、

$$
a>0,\qquad y>0,\qquad \gcd(a,y)=1,\qquad 5\nmid a,
$$

かつ、

$$
GN5(a^5,y)=b^5
$$

を満たします。`hCore` はこの組を一律に排除するので、Branch B の反例候補は存在できません。

## 証明全体での役割

本定理は elementary reduction と後続の深い数論を接続する adapter です。

- `exists_branchB_fifthPowerNormalForm` が完全標準形を構成する provider。
- `BranchBFifthPowerCore` が反証に必要な五項だけを要求する consumer。
- 本定理が標準形から五項を射影して consumer へ渡す。

これにより、後続の黄金整数・降下法は元の $x,y,z$ を直接扱わず、縮約済み `GN5` 方程式の排除に集中できます。

## 直接依存する定義・補題

### `BranchBFifthPowerCore`

反証器の最小 curried interface です。

### `CounterexamplePack`

正値性、原始性、第五冪方程式を束ねた元の反例候補です。

### `exists_branchB_fifthPowerNormalForm`

`hPack` と `hBranch` から、

```lean
∃ a b, BranchBFifthPowerNormalForm x y z a b
```

を構成します。

### 使用する標準形フィールド

```lean
hNF.a_pos
hNF.pack.hy
hNF.coprime_a_y
hNF.five_not_dvd_a
hNF.GN_eq
```

## 証明の流れ

1. provider を `hPack` と `hBranch` に適用する。
2. `rcases` で witness `a`, `b` と標準形 `hNF` を取り出す。
3. core に $a>0$、$y>0$、`Coprime a y`、$5∤a$、`GN5(a^5,y)=b^5` を順に渡す。
4. core が返す `False` で閉じる。

新しい数論的推論はなく、provider と consumer の型を接続することが全内容です。

## Lean 固有の処理

`rcases ... with ⟨a, b, hNF⟩` が二重存在を一度に除去します。`hNF.pack.hy` は標準形内部の `CounterexamplePack` から $y>0$ を取り出す入れ子の射影です。

`BranchBFifthPowerCore` は関数型の連鎖なので、五つの証拠を通常の関数適用で渡せます。暗黙変数 `{a b y}` は引数型から推論されます。また `abbrev` は透過的なので、明示的な `unfold` は不要です。

## 冗長・重複箇所

証明本体は既に最小に近く、数学的重複はありません。`hNF.pack.hy` だけが入れ子の射影ですが、一回の利用のために専用 API を増やすより現在の直接射影が明瞭です。

## 最適化候補

未検証案として、標準形に次の adapter を追加できます。

```lean
theorem BranchBFifthPowerNormalForm.false_of_core
    (hNF : BranchBFifthPowerNormalForm x y z a b)
    (hCore : BranchBFifthPowerCore) : False :=
  hCore hNF.a_pos hNF.pack.hy hNF.coprime_a_y
    hNF.five_not_dvd_a hNF.GN_eq
```

ただし現状では一箇所しか短縮しないため、API 増加との釣り合いが必要です。

core 自体を標準形全体の consumer にすると証明は短くなりますが、不要な $x,z$ や追加の互いに素性まで境界へ持ち込むため、現在の必要最小限設計の方が優れています。

## 必要 Mathlib import と import 最適化候補

確認済みの standalone artifact は `import Mathlib` を使用しています。本定理自身が直接使うのは存在除去、構造体射影、関数適用だけで、Mathlib の算術補題を直接呼びません。

最小 import はプロジェクト内の `NormalForm` 依存に従います。`rcases` を提供する基礎環境と、core・provider を供給するローカルモジュールだけで足りる可能性がありますが、未検証です。本作業では Lean ビルドを行っていません。

## Comparator challenge 化の可否

初級 challenge に適しています。

```lean
theorem challenge
    (hCore : BranchBFifthPowerCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False := by
  sorry
```

評価点は、provider の発見、二重存在の除去、必要な五フィールドの正しい選択、不要フィールドを使わない provider/consumer 境界の保持です。

## 根拠と推測の区別

宣言型、証明本体、使用フィールド、`NormalForm.lean` の末尾に置かれていることは repository 内の生成済み standalone Lean ソースで確認しました。

import 最小化と補助 adapter の追加は未検証の設計提案です。

## 次に読むべき宣言

次はソース直後の `DkMath.FLT.Five.Body5` です。

本定理で Branch B 第五冪標準形から抽象 core への adapter が完成します。続く `BranchB.lean` は gap と巡回因子の積を

```lean
def Body5 (g y : ℕ) : ℕ :=
  g * GN5 g y
```

として再び明示化します。
