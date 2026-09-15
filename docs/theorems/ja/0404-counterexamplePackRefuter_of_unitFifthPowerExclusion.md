# 0404 `counterexamplePackRefuter_of_unitFifthPowerExclusion`

## 宣言種別

`theorem`

## Lean の型

```lean
/-- The unit-times-fifth-power exclusion closes every primitive packet unconditionally. -/
theorem counterexamplePackRefuter_of_unitFifthPowerExclusion
    (hExclude : SignedGoldenUnitFifthPowerExclusion) :
    CounterexamplePackRefuter := by
  intro x y z p
  rcases p.branchB_orientation with hyGap | hxGap
  · exact branchB_false_of_unitFifthPowerExclusion hExclude p hyGap
  · exact branchB_false_of_unitFifthPowerExclusion hExclude p.swap hxGap
```

## 数学的主張・宣言の意味

この theorem は、golden-order 側で得られた

```lean
SignedGoldenUnitFifthPowerExclusion
```

を仮定すれば、すべての primitive FLT5 counterexample packet を否定できることを示す。

すなわち

$$
\mathrm{SignedGoldenUnitFifthPowerExclusion}
\Longrightarrow
\mathrm{CounterexamplePackRefuter}
$$

である。

`CounterexamplePackRefuter` を展開すると、結論は

$$
\forall x,y,z\in\mathbb N,
\quad
\mathrm{CounterexamplePack}(x,y,z)\to\bot
$$

である。

ここで `SignedGoldenUnitFifthPowerExclusion` は、ramifier-stripped packet の golden factor `beta` が

$$
\beta=\varepsilon\gamma^5
$$

という unit-times-fifth-power 形を取る可能性を排除する receiver contract である。

一方、`branchB_false_of_unitFifthPowerExclusion` は clean gap orientation

$$
5\nmid(z-y)
$$

を持つ primitive packet を、その exclusion から直接矛盾へ送る。

問題は、任意の primitive packet が最初から `5 \nmid (z-y)` を満たすとは限らないことである。直前の `CounterexamplePack.branchB_orientation` は

$$
5\nmid(z-y)
\quad\text{または}\quad
5\nmid(z-x)
$$

を保証する。

前者なら元 packet `p` をそのまま Branch B refuter へ送り、後者なら `x` と `y` を交換した `p.swap` を送り込む。`p.swap` における gap は元の `z-x` なので、どちらの分岐でも同じ Branch B theorem を再利用できる。

したがって数学的な流れは

$$
\mathrm{primitive\ packet}
\xrightarrow{\text{orientation}}
\begin{cases}
5\nmid(z-y), & p,\\
5\nmid(z-x), & p.swap,
\end{cases}
\xrightarrow{\text{Branch B exclusion}}
\bot.
$$

である。

## 証明全体での役割

この theorem は局所的な Branch B contradiction を、primitive FLT5 全体の refuter へ持ち上げる closure theorem である。

証明アーキテクチャ上は、次の境界を接続する。

$$
\text{golden unit/fifth-power exclusion}
\longrightarrow
\text{routed Branch-B contradiction}
\longrightarrow
\text{primitive packet refuter}.
$$

直前の 0403 `CounterexamplePackRefuter` は「primitive packet をすべて否定する証明」の型だけを定義した。0404 はその型の具体的 inhabitant を初めて与える。

この theorem 自身は新しい 5-adic 計算、golden integer 計算、無限降下を行わない。それらはすべて前段で証明済みであり、ここでは二つの orientation を正しい既存 refuter へ配線することだけが役割である。

さらに直後の

```lean
theorem counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
```

は `SignedGoldenUnitFifthPowerExclusion` 自体を

- `GoldenUnitClassesModFifth`
- `GoldenZeroSectorArithmeticExclusion`

から構築し、この 0404 に渡す。従って 0404 は closure chain の中央にある再利用可能な adapter である。

## 直接依存する定義・補題

### `SignedGoldenUnitFifthPowerExclusion`

入力 `hExclude` の型。

概念的には、任意の stripped packet `p` と golden integers `epsilon`, `gamma` に対して

$$
\epsilon\text{ が unit},
\qquad
p.beta=\epsilon\gamma^5
$$

なら `False` を返す exclusion contract である。

0404 はこの contract の内部証明には立ち入らず、既存 Branch B refuter へそのまま渡す。

### `CounterexamplePackRefuter`

0403 で定義された conclusion type。

```lean
abbrev CounterexamplePackRefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

`intro x y z p` は、この `abbrev` が右辺へ展開された形をそのまま導入している。

### `CounterexamplePack.branchB_orientation`

直前の routing theorem。

```lean
p.branchB_orientation :
  ¬ 5 ∣ z - y ∨ ¬ 5 ∣ z - x
```

0404 の場合分けを完全に決定する直接依存である。

### `branchB_false_of_unitFifthPowerExclusion`

Branch B の contradiction theorem。

正本では先行して

```lean
theorem branchB_false_of_unitFifthPowerExclusion
    (hExclude : SignedGoldenUnitFifthPowerExclusion)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False :=
  branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_unitFifthPowerExclusion hExclude) hPack hBranch
```

と定義されている。

つまり 0404 はその theorem を両 orientation に再利用している。

### `CounterexamplePack.swap`

第2分岐で用いる packet の左右交換。

元の packet が `CounterexamplePack x y z` なら `p.swap` は `CounterexamplePack y x z` を与える。これにより、元の条件

$$
5\nmid(z-x)
$$

が swap 後の Branch B condition

$$
5\nmid(z-y')
$$

としてちょうど必要な位置に移る。

`swap` の内部構築そのものはこの theorem では行わず、先行 API を利用する。

## 証明の流れ

### 1. refuter の全称引数を導入する

```lean
intro x y z p
```

`CounterexamplePackRefuter` が reducible な `abbrev` なので、Lean は結論を

```lean
∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

として扱える。

これで任意の primitive packet

```lean
p : CounterexamplePack x y z
```

を固定する。

### 2. orientation theorem で二分する

```lean
rcases p.branchB_orientation with hyGap | hxGap
```

得られる二ケースは

```lean
hyGap : ¬ 5 ∣ z - y
```

または

```lean
hxGap : ¬ 5 ∣ z - x
```

である。

### 3. 第1 orientation は元 packet を直接閉じる

```lean
exact branchB_false_of_unitFifthPowerExclusion hExclude p hyGap
```

これは Branch B theorem の期待する gap がそのまま `z-y` なので、変換を必要としない。

### 4. 第2 orientation は packet を swap して閉じる

```lean
exact branchB_false_of_unitFifthPowerExclusion hExclude p.swap hxGap
```

`p.swap` では左右入力が交換されるため、Branch B theorem から見た `z-y` が元 packet の `z-x` になる。

この一行が証明の設計上もっとも重要である。orientation ごとに別 theorem を用意するのではなく、対称性を packet API に押し込み、一つの Branch B refuter を二度使う。

## Lean 固有の処理

### `abbrev` conclusion の自動展開

結論は `CounterexamplePackRefuter` という名前だが、proof は直接

```lean
intro x y z p
```

から始まる。

これは `CounterexamplePackRefuter` が `abbrev` であり、elaborator が必要に応じて

```lean
∀ {x y z : ℕ}, CounterexamplePack x y z → False
```

へ展開できるためである。

### `rcases ... with ... | ...`

```lean
rcases p.branchB_orientation with hyGap | hxGap
```

は `Or` の elimination を行う tactic syntax である。

数学的には単純な場合分けだが、Lean 上では各 branch に対応する hypothesis の名前を同時に導入できる。

### dependent indices と `p.swap`

`p` の型は index 付き

```lean
CounterexamplePack x y z
```

である。

`p.swap` は

```lean
CounterexamplePack y x z
```

という別の index を持つ packet になるが、`branchB_false_of_unitFifthPowerExclusion` の `{x y z}` は implicit なので、Lean が `p.swap` から新しい index を推論する。

その結果、`hxGap : ¬ 5 ∣ z - x` が swap 後の theorem の `hBranch` と型一致する。

この dependent-index inference により、明示的な `simpa` や rewrite が不要になっている。

### `exact` による terminal application

両 branch とも既存 theorem の適用結果がちょうど `False` なので、追加の tactic 処理なしに `exact` で終了する。

## 冗長・重複箇所

証明は非常に短く、局所的な冗長性はほぼない。

二つの branch は

```lean
branchB_false_of_unitFifthPowerExclusion hExclude ... ...
```

を繰り返すが、異なる点は `p` / `p.swap` と `hyGap` / `hxGap` だけである。

これは論理構造そのものが二分岐なので、現在の明示形は可読性が高い。

無理に共通化すると、orientation と packet transformation を pair に梱包する helper が必要となり、4 行の theorem より抽象化コストが大きくなる。

また `branchB_false_of_unitFifthPowerExclusion` 自体が

```lean
signedBranchARefuter_of_unitFifthPowerExclusion
```

を経由する adapter なので、closure 層には複数の薄い theorem が並ぶ。しかしこれは receiver boundary を明示し、各層を独立に再利用・監査できるようにする設計であり、単なる重複とは見なしにくい。

## 最適化候補

### 現状の二分岐を維持するのが第一候補

この theorem は routing logic を最短に近い形で表している。

特に

```lean
p.branchB_orientation
```

と

```lean
p.swap
```

の二つを並べることで、「どちらかの gap を clean orientation にする」という数学的意味がコードから直接読める。

### orientation を packet と gap の witness にまとめる案

理論上は、先行 theorem を

```lean
∃ p' : CounterexamplePack _ _ z, ¬ 5 ∣ z - (...)
```

のような「routed packet + gap certificate」を返す API に変更すれば、0404 側を一回の Branch B theorem 適用にできる。

しかし existential/dependent pair が複雑になり、元の `x,y` との対応も読みにくくなる。現状の `Or` + `swap` の方が単純である。

### generic symmetric router の抽象化

同様の「左または右の条件を、swap で一つの theorem に統一する」パターンが他 exponent や他 branch でも大量に現れるなら、generic routing lemma を導入する価値はある。

ただし、このファイルだけを見る限り 0404 単独を目的に一般化する必要はない。

## 必要な Mathlib import

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

0404 の proof 本体で直接使う Lean/Mathlib 機能は主に

- `Or` の場合分け
- `rcases`
- implicit argument inference
- 先行 DkMath declarations

であり、数論 tactic や algebra tactic は使用していない。

Mathlib 側の重い依存はこの theorem 自身ではなく、次の先行宣言の型・証明側にある。

- `CounterexamplePack`
- `SignedGoldenUnitFifthPowerExclusion`
- `CounterexamplePack.branchB_orientation`
- `branchB_false_of_unitFifthPowerExclusion`
- `CounterexamplePack.swap`

standalone manifest 上では 0404 は `DkMath/FLT/Five/SignedGoldenClosure.lean` に属し、先行する `SignedGoldenUnitClasses.lean` などの公開 API を利用する。

### import 最適化候補

0404 単体のために `import Mathlib` 全体を必要とするわけではない。

モジュール化された DkMath 側では、`SignedGoldenClosure.lean` が直接利用する DkMath modules と、それらが要求する最小 Mathlib imports に絞れる可能性が高い。

ただし今回 Lean build は行わないため、厳密な最小 import 集合は未確認である。特定の細分化 Mathlib module 名を最小集合として断定することはしない。

## Comparator challenge 化の可否

**可能であり、0403 単独より適している。**

この theorem は短いが、単なる `rfl` ではなく次の要素を含む。

1. `abbrev` conclusion の展開。
2. `Or` elimination。
3. dependent packet の `swap`。
4. implicit indices の再推論。
5. 同じ refuter theorem を二方向へ適用する routing。

Comparator challenge としては、前提として

```lean
hExclude : SignedGoldenUnitFifthPowerExclusion
p : CounterexamplePack x y z
```

および必要な API を与え、

```lean
False
```

を証明させる形が自然である。

難度は低から中程度で、深い数論探索よりも Lean の interface composition と dependent elaboration の品質を比較する challenge になる。

より有益な challenge にするなら、完成 theorem 名 `counterexamplePackRefuter_of_unitFifthPowerExclusion` 自体は隠し、

- `branchB_orientation`
- `branchB_false_of_unitFifthPowerExclusion`
- `CounterexamplePack.swap`

だけを利用可能にして再構築させるとよい。

## 次に読むべき宣言

次は

```lean
theorem counterexamplePackRefuter_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    CounterexamplePackRefuter :=
  counterexamplePackRefuter_of_unitFifthPowerExclusion
    (signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector hClasses
      (signedGoldenZeroSectorExclusion_of_arithmetic hArithmetic))
```

である。

0404 は

$$
\mathrm{SignedGoldenUnitFifthPowerExclusion}
\Longrightarrow
\mathrm{CounterexamplePackRefuter}
$$

という closure を提供した。

次の theorem は、その入力である `SignedGoldenUnitFifthPowerExclusion` をさらに

$$
\mathrm{GoldenUnitClassesModFifth}
$$

と

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
$$

から組み立てる。

従って次の段階では

$$
(\text{unit classification})
+
(\text{zero-sector arithmetic})
\longrightarrow
\text{all primitive packets are impossible}
$$

という、より上位の receiver composition を読むことになる。
