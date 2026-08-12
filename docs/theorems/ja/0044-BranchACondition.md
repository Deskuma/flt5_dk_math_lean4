# 0044 — `DkMath.FLT.Five.BranchACondition`

## 1. 宣言

```lean
def BranchACondition (y z : ℕ) : Prop :=
  5 ∣ z - y
```

本宣言は `DkMath.FLT.Five.BranchA` に置かれた定義であり、指数五の証明における例外側の分岐条件を名前付き命題として切り出す。

## 2. Lean の型

```lean
BranchACondition : ℕ → ℕ → Prop
```

二つの自然数 `y`、`z` を受け取り、自然数減算による gap `z - y` が `5` で割り切れるという命題を返す。

## 3. 数学的主張

数学的には、

$$
BranchACondition(y,z) \iff 5\mid(z-y)
$$

である。

FLT5 の正の反例候補では先行定理から $y<z$ が得られるため、実際の反例経路では `z - y` は通常の正の差を表す。ただし、この定義単独は `y≤z` を仮定しない。したがって一般の入力では Lean の自然数減算が切り詰め減算であることに注意が必要である。特に `z<y` なら `z-y=0` となり、`5 ∣ 0` により条件は真になる。

## 4. 証明全体での役割

本宣言は、これまで読んだ Branch B 条件

$$
5\nmid(z-y)
$$

の論理的補集合を公開 API として命名する。

Branch B では gap と `GN5` の互いに素な分離、第五冪因子分解、clean channel/no-lift provider が用いられた。一方 Branch A では、gap に五が入るため、その初期の分離経路をそのまま適用できない。ソースコメントによれば、この分岐は後続の signed Branch A、exact five-adic packet、golden-order descent へ送られる。

したがって `BranchACondition` は数論を証明する定理ではなく、証明ルータの判定ラベルである。

## 5. 直接依存する定義・補題

直接必要なのは次だけである。

- 自然数 `ℕ`
- 自然数減算 `z - y`
- 整除関係 `5 ∣ z - y`

`CounterexamplePack`、`Fermat5Equation`、`GN5` には定義本体として依存しない。これらは後続の利用側で結び付けられる。

## 6. 証明の流れ

`def` 宣言なので証明項は存在しない。右辺の命題に名前を与えるだけである。

```text
入力 y, z
  ↓
gap z - y を作る
  ↓
5 が gap を割るか判定する命題
  ↓
BranchACondition y z
```

## 7. Lean 固有の処理

### 7.1 `Prop` を返す定義

`BranchACondition` は Boolean 判定ではなく命題である。したがって使用時には証拠

```lean
hA : BranchACondition y z
```

を受け取り、必要なら `unfold BranchACondition at hA` または `simpa [BranchACondition] using hA` によって `5 ∣ z - y` として扱う。

### 7.2 自然数減算

`Nat` の減算は切り詰められる。本分岐を数学的な差 $z-y>0$ と読むには、通常は `CounterexamplePack` と `right_lt_of_fermat5Equation` から `y<z` を別途確保する必要がある。

### 7.3 数値リテラル `5`

型は整除式の周囲から `ℕ` に推論される。明示すれば `(5 : ℕ) ∣ z - y` と同じである。

## 8. 冗長・重複箇所

命題そのものは既存の Branch B 仮定 `¬ 5 ∣ z - y` の内部に繰り返し現れるため、文字列としては重複している。しかし命名には次の価値がある。

- Branch A の公開インターフェースを安定させる。
- 後続 theorem の型を意味論的に読みやすくする。
- signed/five-adic/golden descent 層へ渡す契約を明示する。
- 実装詳細の整除式を将来変更する場合に利用側を隔離する。

したがって、この重複は除去対象というより意図的な semantic wrapper と評価できる。

## 9. 最適化候補

### 9.1 `abbrev` への変更

透過性だけを重視するなら `abbrev` も可能だが、分岐 API として独立した名前と展開制御を持つ `def` は妥当である。変更の必要性は低い。

### 9.2 順序仮定を含む強化版

切り詰め減算の誤読を防ぐため、別途

```lean
def PositiveBranchACondition (y z : ℕ) : Prop :=
  y < z ∧ 5 ∣ z - y
```

のような強化版を設ける案はある。ただし `CounterexamplePack` から順序が必ず導出される現設計では、既存 API へ組み込むと重複が増える。必要性は後続利用箇所の監査で判断すべきである。

## 10. 必要 Mathlib import と import 最適化候補

生成済み standalone ソースは `import Mathlib` で検証されている。宣言単体が必要とする機能は自然数、減算、整除だけであり、Mathlib 全体は過剰である。

ただし元の分割モジュール `BranchA.lean` の正確な import 行は、この回では standalone artifact からは確定できなかった。最小 import 候補を断定せず、次のように監査対象とする。

- `Mathlib.Data.Nat.Basic` 周辺で足りる可能性が高い。
- 実際には直後の `BranchARefuter` が `CounterexamplePack` を使うため、プロジェクト内の先行モジュール import が必要になる。
- import 最適化は `BranchA.lean` 全体を対象に行うべきであり、本定義だけを孤立させて判断しない。

## 11. Comparator challenge 化の可否

可能である。ただし定理証明ではなく、定義展開と自然数減算の意味を問う小課題が適する。

### Challenge A

```lean
example {y z : ℕ} (h : BranchACondition y z) : 5 ∣ z - y := by
  exact h
```

定義の透過性によりそのまま通るか、`simpa [BranchACondition] using h` が必要かを比較する。

### Challenge B

```lean
example {y z : ℕ} (h : 5 ∣ z - y) : BranchACondition y z := by
  exact h
```

### Challenge C

`z<y` の場合にも `BranchACondition y z` が真になり得る理由を、`Nat.sub_eq_zero_of_le` と `dvd_zero` を使って形式化する。これは切り詰め減算への理解を測る良い Comparator challenge となる。

## 12. 根拠と留保

確認済み事項は次である。

- 宣言名、引数、型、定義本体。
- `BranchA.lean` の冒頭宣言であること。
- 直後に `BranchARefuter` が続くこと。
- ソースコメントが Branch A を signed five-adic packet と golden-order descent へ送ると説明していること。

元の分割モジュールの正確な import 行だけは未確認であり、import 節の提案は明示的な監査候補である。

## 13. 次に読むべき宣言

次は

```lean
DkMath.FLT.Five.BranchARefuter
```

を読む。

これは `CounterexamplePack x y z` と `BranchACondition y z` を受け取って `False` を返す、完成済み signed five-adic / golden-order refutation の再利用可能な receiver contract である。