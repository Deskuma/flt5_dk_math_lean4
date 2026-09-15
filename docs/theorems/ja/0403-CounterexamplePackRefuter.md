# 0403 `CounterexamplePackRefuter`

## 宣言種別

`abbrev`

## Lean の型

```lean
/-- Refuters for both routed orientations refute every primitive packet. -/
abbrev CounterexamplePackRefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

## 数学的主張・宣言の意味

`CounterexamplePackRefuter` は定理そのものではなく、後続の closure 定理が共有して使う命題型の略記である。

展開すると

$$
\forall x,y,z\in\mathbb N,
\quad
\mathrm{CounterexamplePack}(x,y,z)\to\bot
$$

である。

`CounterexamplePack x y z` は正の自然数による primitive FLT5 反例候補を束ねるため、数学的には

$$
x^5+y^5=z^5,
\qquad
x,y,z>0,
\qquad
\gcd(x,y)=1
$$

を満たす primitive candidate が一つ与えられれば矛盾を導ける、という refuter interface を表す。

したがって、この型の inhabitant を一つ構築できれば、primitive FLT5 counterexample は存在できない。

重要なのは、ここではまだその inhabitant を構築していないことである。`CounterexamplePackRefuter` は「何を証明すれば primitive 層が閉じるのか」を名前付きの型として固定する宣言である。

## 証明全体での役割

直前の `CounterexamplePack.branchB_orientation` は、任意の primitive packet に対して

$$
5\nmid(z-y)
\quad\text{または}\quad
5\nmid(z-x)
$$

を保証した。

これにより、元の packet か `p.swap` のどちらかを Branch B の clean orientation に必ず送れる。

`CounterexamplePackRefuter` は、その routing 結果を最終的に

$$
\text{primitive packet}\longrightarrow\bot
$$

へ閉じるための受け口である。

直後の

```lean
theorem counterexamplePackRefuter_of_unitFifthPowerExclusion
    (hExclude : SignedGoldenUnitFifthPowerExclusion) :
    CounterexamplePackRefuter := by
  intro x y z p
  rcases p.branchB_orientation with hyGap | hxGap
  · exact branchB_false_of_unitFifthPowerExclusion hExclude p hyGap
  · exact branchB_false_of_unitFifthPowerExclusion hExclude p.swap hxGap
```

が、この interface の最初の具体的 inhabitant を構築する。

したがって証明全体の階層は

$$
\text{local Branch-B exclusion}
\longrightarrow
\text{orientation routing}
\longrightarrow
\texttt{CounterexamplePackRefuter}
\longrightarrow
\text{positive FLT5 refuter}
$$

と整理できる。

この `abbrev` は局所的な代数・5-adic・golden-order 証明群と、最終的な FLT5 closure 層との境界を明示する API である。

## 直接依存する定義・補題

### `CounterexamplePack`

この宣言が直接参照する唯一の DkMath 固有定義である。

正本の冒頭では次の structure として定義されている。

```lean
structure CounterexamplePack (x y z : ℕ) : Prop where
  hx : 0 < x
  hy : 0 < y
  hz : 0 < z
  hxy : Nat.Coprime x y
  hEq : Fermat5Equation x y z
```

したがって `CounterexamplePackRefuter` は、この primitive packet 全体を入力として `False` を返す関数型である。

### `False`

Lean の標準命題 `False : Prop`。packet が存在すると仮定したとき矛盾を導くことを意味する。

### 暗黙引数 `{x y z : ℕ}`

`x`, `y`, `z` は implicit binder になっているため、後続 theorem では packet `p : CounterexamplePack x y z` から値を推論できる。

この宣言自体は `branchB_orientation` や golden-order 側の theorem を直接参照しない。それらは `CounterexamplePackRefuter` の inhabitant を構築する後続 theorem の依存である。

## 構築の流れ

`abbrev` なので証明スクリプトは存在しない。構築は型の設計だけで完了している。

### 1. 対象を primitive packet に固定する

```lean
∀ {x y z : ℕ}, CounterexamplePack x y z → ...
```

任意の自然数三つ組を直接扱うのではなく、primitive normalization 済みの packet を境界型にする。

### 2. 出力を `False` に固定する

```lean
CounterexamplePack x y z → False
```

各 packet から矛盾を返せればよい。

### 3. 全 packet を量化する

```lean
∀ {x y z : ℕ}, ...
```

特定の反例候補ではなく、primitive candidate 全体を一つの refuter で閉じる。

このため `CounterexamplePackRefuter` は、概念的には

$$
\mathrm{CounterexamplePackRefuter}
\simeq
\prod_{x,y,z:\mathbb N}
\bigl(\mathrm{CounterexamplePack}(x,y,z)\to\bot\bigr)
$$

という依存関数型である。

## Lean 固有の処理

### `abbrev` の使用

`def` ではなく `abbrev` が使われている。

`abbrev` は reducible な略記として扱われやすく、Lean の elaborator や simplification が必要に応じて右辺へ展開できる。そのため後続 theorem では

```lean
CounterexamplePackRefuter := by
  intro x y z p
  ...
```

と、そのまま全称量化された関数型として証明を開始できる。

この用途では opaque な抽象化より、軽量な interface alias として `abbrev` を選ぶ設計が自然である。

### implicit binder

```lean
∀ {x y z : ℕ}, ...
```

と波括弧を使うことで、利用側が毎回 `x y z` を明示せずとも packet から推論できる。

例えば後続では

```lean
exact hPrimitive p
```

のような適用が可能になる。

### `Prop` に閉じた interface

structure やデータを新たに生成するのではなく、型全体が `Prop` に属する。したがってここで必要なのは computational data ではなく「primitive packet を否定できる」という証明能力だけである。

## 冗長・重複箇所

この宣言は一行の型 alias なので、内部の冗長性はほぼない。

ただし証明アーキテクチャ上は、後に現れる

```lean
abbrev PositiveFermat5Refuter : Prop :=
  ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → ¬ Fermat5Equation x y z
```

と同じ「refuter を名前付き `Prop` として公開する」パターンを持つ。

この反復は冗長というより、証明層ごとの boundary contract を明示する意図的な設計と見るのが妥当である。

## 最適化候補

### 現状維持が第一候補

この宣言は十分に小さく、最適化による実益はほぼない。

`abbrev` を消して後続 theorem に

```lean
∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

を直接書くこともできるが、そうすると closure 層の意味的な名前が失われる。

したがって現在の named interface の方が可読性・再利用性ともに良い。

### 一般 refuter 型への抽象化

理論上は

```lean
abbrev Refuter (P : α → Prop) : Prop := ∀ a, P a → False
```

のような一般形へ抽象化できる。

しかし `CounterexamplePack` は三つの index を持つ dependent proposition であり、一般化するとかえって型が複雑になる。またこの証明では `PositiveFermat5Refuter` など各 closure boundary の数学的意味を名前で残す価値が高い。

従って、この一般化は現時点では推奨しない。

### `¬ CounterexamplePack ...` との比較

右辺を

```lean
∀ {x y z : ℕ}, ¬ CounterexamplePack x y z
```

と書くことも論理的には同値である。

現在の

```lean
CounterexamplePack x y z → False
```

は後続の関数適用として直接読みやすく、`hPrimitive p` という closure API によく合っている。変更する必要性は低い。

## 必要な Mathlib import

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

ただし `CounterexamplePackRefuter` 自身は Mathlib 固有 theorem や tactic を一つも呼び出していない。直接必要なのは

- `ℕ`
- `Prop`
- `False`
- 全称量化と関数型
- 先行定義 `CounterexamplePack`

だけである。

`CounterexamplePack` の元ソースは standalone manifest 上では `DkMath/FLT/Five/Basic.lean` であるため、モジュール分割された DkMath 側なら概念上はその Basic module が直接依存になる。

### import 最適化候補

この宣言単独のために `import Mathlib` 全体を必要とするわけではない。

しかし `CounterexamplePack` 自体が `Nat.Coprime` と `Fermat5Equation` を含むため、実際の最小 Mathlib import は「この一行」だけでなく `Basic.lean` 全体をコンパイルできる import 集合として決める必要がある。

今回 Lean build は行わないため、厳密な最小 import の確定はしていない。従って `import Mathlib` から特定の細分化 import へ置換可能である、という点までは確実だが、最小集合の具体名は未確認である。

## Comparator challenge 化の可否

**可能だが、単独では challenge として非常に弱い。**

理由は、この宣言が proof を含まない単純な `abbrev` だからである。

例えば

```lean
example : CounterexamplePackRefuter ↔
    (∀ {x y z : ℕ}, CounterexamplePack x y z → False) := by
  rfl
```

のような challenge は作れるが、実質的には reducibility の確認だけであり、数学的 proof search はほぼ発生しない。

Comparator 向けにするなら、この宣言単独ではなく直後の

```lean
counterexamplePackRefuter_of_unitFifthPowerExclusion
```

と組み合わせ、

1. `CounterexamplePackRefuter` を展開する。
2. `branchB_orientation` で二方向へ分岐する。
3. 元 packet と `p.swap` を適切な Branch B refuter へ送る。

という routing proof を challenge にした方が有益である。

したがって評価は

- interface/elaboration challenge: 可
- 数論 proof challenge: 不向き
- closure-routing challenge の前提型として: 非常に有用

となる。

## 次に読むべき宣言

次は

```lean
theorem counterexamplePackRefuter_of_unitFifthPowerExclusion
    (hExclude : SignedGoldenUnitFifthPowerExclusion) :
    CounterexamplePackRefuter := by
  intro x y z p
  rcases p.branchB_orientation with hyGap | hxGap
  · exact branchB_false_of_unitFifthPowerExclusion hExclude p hyGap
  · exact branchB_false_of_unitFifthPowerExclusion hExclude p.swap hxGap
```

である。

`CounterexamplePackRefuter` が「primitive packet を全て否定できる」という **型だけを定義** したのに対し、次の theorem は `SignedGoldenUnitFifthPowerExclusion` を仮定して、その型の inhabitant を実際に構築する。

ここで直前の 0402 `CounterexamplePack.branchB_orientation` が初めて closure に直接消費される。

流れは

$$
\mathrm{SignedGoldenUnitFifthPowerExclusion}
\longrightarrow
\mathrm{branchB\ orientation}
\longrightarrow
\mathrm{CounterexamplePackRefuter}
$$

であり、次の宣言は局所的な Branch B 排除を primitive FLT5 全体の refutation へ持ち上げる重要な closure theorem である。
