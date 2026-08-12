# 0039 — `BranchBCleanGN5ChannelProvider`

## 1. 宣言

```lean
/-- A Branch-B counterexample receives at least one existential clean GN5 channel. -/
abbrev BranchBCleanGN5ChannelProvider : Prop :=
  ∀ {x y z : ℕ},
    CounterexamplePack x y z →
    ¬ 5 ∣ z - y →
    ∃ q : ℕ, CleanGN5Channel (z - y) y q
```

## 2. Lean の型

`BranchBCleanGN5ChannelProvider` は値を計算する関数ではなく、型 `Prop` を持つ命題の略称である。

暗黙の自然数 `x y z` ごとに、

- `CounterexamplePack x y z`
- Branch B 条件 `¬ 5 ∣ z - y`

を受け取り、ある自然数 `q` と、その `q` が `CleanGN5Channel (z-y) y q` を満たす証拠を返す。

`abbrev` なので、利用時にはこの全称命題へ透過的に展開される。

## 3. 数学的主張

原始的な正の Fermat 反例候補

$$
x^5+y^5=z^5
$$

が Branch B、すなわち

$$
5\nmid z-y
$$

に属するなら、少なくとも一つの素数 `q` が存在し、

$$
q\mid GN5(z-y,y),
$$

$$
q\nmid z-y,
$$

$$
q^2\nmid GN5(z-y,y)
$$

を満たす、とする供給契約である。素数性を含むこれら四条件は `CleanGN5Channel` 構造体に束ねられている。

この宣言そのものは、そのような `q` が常に存在することを証明していない。存在証明を後続の consumer へ渡すための仮定インターフェースを命名している。

## 4. 証明全体での役割

前号 `counterexample_false_of_clean_GN5Channel_by_dvd` は、具体的な clean channel が一つ与えられれば Branch B の反例候補を直ちに `False` へ送る。しかし、そこで `q` を発見する責任は未解決のまま残った。

本宣言は、その供給責任を独立した provider API として切り出す。

- provider 側は `q` と clean-channel 証拠を作る。
- refuter 側は、その証拠から完全第五冪 body との矛盾を作る。

この分離により、素数探索・no-lift 証明と、局所矛盾の利用を交換可能な部品として監査できる。

ソースコメントによれば、この provider は有用な条件付き公開インターフェースとして保持されているが、最終的な無条件 FLT5 経路は global provider を仮定せず、signed five-adic normalization と golden descent を通る。

## 5. 直接依存する定義・補題

### 5.1 `CounterexamplePack`

正値性、`Nat.Coprime x y`、Fermat 方程式を保持する入力パケットである。本宣言はフィールドを展開せず、provider の入力型としてそのまま使う。

### 5.2 `CleanGN5Channel`

```lean
CleanGN5Channel (z - y) y q
```

は次を束ねる。

- `Nat.Prime q`
- `q ∣ GN5 (z-y) y`
- `¬ q ∣ z-y`
- `¬ q^2 ∣ GN5 (z-y) y`

### 5.3 自然数減算と Branch B

`z-y` は `ℕ` の切り捨て減算である。ただし provider の入力には `CounterexamplePack` があり、前段の定理から実際には `y<z` を導ける。本宣言の型ではその順序証拠を別引数にせず、必要なら provider 実装側が `hPack` から回収する。

## 6. 証明の流れ

本宣言は `abbrev` なので証明本体を持たない。利用時の論理的な流れは次の通りである。

1. 任意の `x y z` を取る。
2. `hPack : CounterexamplePack x y z` を受け取る。
3. `hBranch : ¬ 5 ∣ z-y` を受け取る。
4. clean channel を担う `q` を選ぶ。
5. `CleanGN5Channel (z-y) y q` の四フィールドを構成する。
6. witness と証拠を `⟨q, hClean⟩` として返す。

後続の adapter は、この存在を `rcases` で分解し、前号の局所 refuter に渡す。

## 7. Lean 固有の処理

### 7.1 `abbrev` の透過性

`def` よりも積極的に展開される略称であり、`hProvider : BranchBCleanGN5ChannelProvider` は直接

```lean
hProvider hPack hBranch
```

と適用できる。通常は `unfold BranchBCleanGN5ChannelProvider` を要求しない。

### 7.2 暗黙全称量化

`{x y z : ℕ}` は暗黙引数である。`hPack` の型から Lean が三変数を推論するため、consumer 側では通常 `hProvider hPack hBranch` とだけ書ける。

### 7.3 カリー化された含意

Lean では

```lean
CounterexamplePack x y z → ¬ 5 ∣ z-y → ∃ q, ...
```

は二つの証拠を順に受け取る関数型である。provider はパケットを受け取った後、Branch B 証拠を受け取って存在証拠を返す。

### 7.4 存在量化と構造体

結論は `∃ q, CleanGN5Channel ... q` である。外側は existential witness、内側は四フィールドの `Prop` 構造体という二層の束縛になっている。

## 8. 冗長・重複箇所

`BranchBCleanGN5ChannelProvider` は展開すれば一行の全称命題であり、論理内容を増やさない。しかし、次の境界を名前で固定する価値がある。

- 入力は任意の Branch B `CounterexamplePack`
- 出力は具体的な prime channel の存在
- provider の実装と consumer の実装を分離

`q` の四条件を直接連言で返す設計も可能だが、既存の `CleanGN5Channel` を再利用する現在の形の方が重複を避け、後続補題をそのまま適用できる。

## 9. 最適化候補

### 9.1 `def` または `class` への変更

`def` にすれば API 境界は強くなるが、利用時の unfold が増える。`class` にすれば typeclass search で provider を注入できるが、数学的に重大な仮定が暗黙探索へ隠れるため不適切である。明示引数として渡す現行 `abbrev` が監査しやすい。

### 9.2 Branch B 入力の構造体化

`CounterexamplePack` と `¬ 5 ∣ z-y` を一つの Branch B パケットへ束ねれば引数を一つ減らせる。しかし現段階では小さな adapter のために構造体を増やす方が重い。

### 9.3 `q` の素数型化

`q : ℕ` と `Nat.Prime q` を構造体内部に保持する代わりに、素数の subtype を witness にする案もある。ただし既存 API が自然数上の整除を中心に構成されているため、coercion が増える可能性が高い。

以上は設計提案であり、本作業では Lean ビルドによる検証を行っていない。

## 10. 必要 Mathlib import と import 最適化候補

生成済み standalone ソースは全体で `import Mathlib` を使用する。確認できた宣言自体が直接必要とする基盤は、自然数、整除、存在量化、命題構造体である。

プロジェクト内では少なくとも次の宣言が見える import が必要である。

- `CounterexamplePack`
- `CleanGN5Channel`

したがって個別 `Provider.lean` は、推測上 `DkMath.FLT.Five.BranchB` または `DkMath.FLT.Five.CleanChannel` と `DkMath.FLT.Five.Basic` を import すれば十分な可能性がある。ただし standalone 生成物は個別モジュールの import 行を保存していないため、正確な最小集合は未確認である。import 最適化は `lake env lean` によるモジュール単体監査が必要だが、本作業では Lean ビルドを行わない。

## 11. Comparator challenge 化の可否

適している。証明探索ではなく、API 設計と論理型の読解を比較する challenge に向く。

### Challenge A — provider 型の再構成

日本語仕様だけを与え、`CounterexamplePack` と `CleanGN5Channel` を使って同じ `Prop` を宣言させる。暗黙引数、Branch B 条件、existential witness の順序が評価点となる。

### Challenge B — bundled / unbundled 比較

`CleanGN5Channel` を返す版と、四条件の連言を直接返す版を提示し、再利用性・projection・後続補題適用の差を説明させる。

### Challenge C — `abbrev` / `def` / `class` 比較

三つの実装候補を比較し、仮定の可視性、展開挙動、typeclass search による隠蔽リスクを評価させる。

## 12. 根拠と推測の区別

確認済み事項：

- 宣言名、型、`abbrev` 本体
- `Provider.lean` の冒頭に置かれていること
- 条件付き clean-channel interface として意図されていること
- 無条件最終経路は signed five-adic normalization と golden descent を通るというソースコメント
- 直後の宣言が `BranchBNoLiftEscape` であること

推測・監査候補：

- 個別 `Provider.lean` の正確な import 行と最小 import 集合
- `def` や Branch B 専用構造体へ変更した場合の保守性
- subtype prime witness の実用性

## 13. 次に読むべき宣言

次は、同じ局所データを構造体ではなく素数性と三つの整除条件の連言として返す

```lean
DkMath.FLT.Five.BranchBNoLiftEscape
```

を読む。

`BranchBCleanGN5ChannelProvider` が bundled provider interface なら、`BranchBNoLiftEscape` はその unbundled kernel である。両者の型の対応を確認した後、`branchBCleanGN5ChannelProvider_of_noLiftEscape` が連言を `CleanGN5Channel` 構造体へ再梱包する流れへ進む。