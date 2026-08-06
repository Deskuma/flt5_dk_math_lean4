# 0045 — `DkMath.FLT.Five.BranchARefuter`

## 1. 宣言

```lean
/-- Reusable receiver for the completed signed five-adic and golden-order refutation
of a primitive candidate whose natural gap is divisible by five. -/
abbrev BranchARefuter : Prop :=
  ∀ {x y z : ℕ}, CounterexamplePack x y z → BranchACondition y z → False
```

本号は定理の証明ではなく、Branch A を反証する完成済み手続きを受け取るための命題インターフェースを読む。

## 2. Lean の型

`BranchARefuter` 自体の型は `Prop` である。展開後は暗黙の自然数 `x y z` を任意に取り、

```lean
CounterexamplePack x y z → BranchACondition y z → False
```

という関数型になる。

`abbrev` なので、Lean は必要に応じて右辺へ透過的に展開できる。新しい構造体や不透明な定義を導入しているわけではない。

## 3. 数学的主張

`CounterexamplePack x y z` は正の原始的候補

$$
x^5+y^5=z^5
$$

を表し、`BranchACondition y z` は

$$
5\mid(z-y)
$$

を表す。したがって `BranchARefuter` は、これら二条件を同時に満たす候補は存在しない、すなわち

$$
\forall x,y,z\in\mathbb N,\quad
CounterexamplePack(x,y,z)\land 5\mid(z-y)\Longrightarrow\bot
$$

という反証器の契約である。

注意すべきは、この宣言そのものが矛盾を証明しているのではない点である。後続の signed five-adic 正規化と黄金整数環上の降下が最終的に、この契約を満たす具体的な項を構築する。

## 4. 証明全体での役割

前号 `BranchACondition` が例外側の分岐を命名したのに対し、本号はその分岐を閉じるための公開受け口を定める。

役割は次の分離にある。

```text
自然数上の分岐判定
  CounterexamplePack + BranchACondition
                 ↓
          BranchARefuter
                 ↓
signed five-adic packet / golden-order descent
```

上位の主定理は Branch A の内部証明を逐一知る必要がなく、`BranchARefuter` を受け取って適用すればよい。一方、下位の長い降下証明は、最終成果をこの単純な関数型へ圧縮できる。

## 5. 直接依存する定義・補題

### 5.1 `CounterexamplePack`

正値、左辺二項の互いに素性、Fermat 方程式を束ねる原始候補パケットである。

### 5.2 `BranchACondition`

```lean
def BranchACondition (y z : ℕ) : Prop :=
  5 ∣ z - y
```

自然数 gap が 5 で割り切れる例外分岐を表す。

### 5.3 `False`

結論はデータではなく矛盾である。そのため `BranchARefuter` は任意の Branch A 候補を消去できる否定関数として働く。

## 6. 証明の流れ

本宣言は `abbrev` なので証明スクリプトを持たない。利用時の標準的な流れは次の形になる。

```lean
have hFalse : False := hRefuter hPack hBranchA
exact hFalse
```

あるいは目標が `False` なら、

```lean
exact hRefuter hPack hBranchA
```

だけで閉じられる。

実質的な証明責任は、後続モジュールが

```lean
BranchARefuter
```

型の項を構築する箇所に移されている。

## 7. Lean 固有の処理

### 7.1 暗黙量化

`{x y z : ℕ}` は暗黙引数であり、`hPack` と `hBranchA` の型から推論される。

### 7.2 Curry 化された含意

右辺は連言ではなく二段の関数、

```lean
CounterexamplePack x y z → BranchACondition y z → False
```

である。利用時には `hRefuter hPack hBranchA` と順に適用する。

### 7.3 `abbrev` の透過性

`abbrev` は型別名に近い。後続定理で `intro x y z hPack hBranchA` と直接開始でき、通常は `unfold BranchARefuter` を要求しない。

### 7.4 `Prop` 内の計算

このインターフェースは証明の実装を隠すが、Lean のカーネル検査を迂回しない。具体的な refuter 項は最終的に `False` の証明を返さねばならない。

## 8. 冗長・重複箇所

`BranchARefuter` は右辺の関数型に名前を与えただけで、論理的には冗長である。しかし設計上の重複ではなく、長い証明経路の出口を安定させる semantic alias と評価できる。

前段の Branch B provider interfaces と同様、ここでも「数論本体」と「上位ルーティング」を切り離す API 境界が意図されている。

## 9. 最適化候補

### 9.1 現状維持が第一候補

型は短く、用途も明確である。`def` や `structure` へ変更する利益は小さい。

### 9.2 引数名の意味強化

`hBranchA` のような利用側の名前を統一すると、`5 ∣ z - y` を直接渡す場合より証明の可読性が高い。

### 9.3 一般化は慎重に行う

一般的な分岐反証器

```lean
∀ p, Pack p → Condition p → False
```

へ抽象化することも可能だが、この宣言は FLT5 の公開語彙として十分に小さく、過剰抽象化は依存追跡を難しくする可能性がある。

## 10. 必要な Mathlib import

宣言そのものが直接必要とするのは、次の既存宣言が利用可能であることだけである。

```lean
CounterexamplePack
BranchACondition
```

`ℕ`、`Prop`、`False`、含意、全称量化は Lean の基礎環境に属する。したがって `BranchA.lean` の観点では、直前モジュールまたはこれら二宣言を提供する最小 DkMath import があれば足り、`import Mathlib` 全体は本宣言単独には過大である。

正確な最小 import はリポジトリのモジュール境界に依存する。standalone 版は生成物として `import Mathlib` を用いるため、これは最小性の根拠にはしない。

## 11. Import 最適化候補

`BranchA.lean` が `CounterexamplePack` を定義する `Basic` のみへ依存し、`BranchACondition` を同ファイル内で定義する構成なら、候補は概念的に次である。

```lean
import DkMath.FLT.Five.Basic
```

ただし正本リポジトリにおける実ファイルの import 行は、この博物館ブランチの生成済み standalone ソースだけからは確定できない。ここは **最小化候補** であり、確認済み事実ではない。

## 12. Comparator challenge 化の可否

適性は高い。ただし数学問題というより API 設計・Lean 型読解の challenge になる。

### Challenge A

次の型別名を `abbrev` で定義せよ。

```lean
∀ {x y z : ℕ}, CounterexamplePack x y z → BranchACondition y z → False
```

### Challenge B

`hRefuter : BranchARefuter`、`hPack : CounterexamplePack x y z`、`hA : BranchACondition y z` から `False` を一行で示せ。

期待解は、

```lean
exact hRefuter hPack hA
```

である。

### Challenge C

同じ契約を `structure` で包む版と比較し、適用時の構文、透過性、将来のフィールド追加可能性の差を説明せよ。

## 13. 根拠と推測の区別

確認済み事項は次のとおりである。

- 宣言名は `DkMath.FLT.Five.BranchARefuter`。
- `abbrev BranchARefuter : Prop` として定義される。
- 展開形は `CounterexamplePack x y z → BranchACondition y z → False`。
- ソースコメントは signed five-adic と golden-order による完成済み反証の再利用受け口と位置付ける。
- `BranchA.lean` の終端宣言である。

一方、最小 import の具体的な一行は候補であり、正本モジュールの import ヘッダを別途監査する必要がある。

## 14. 次に読むべき定理

次は

```lean
DkMath.FLT.Five.CounterexamplePack.swap
```

を読む。

これは signed Branch A ルーティングの入口で、Fermat 方程式の左辺二項を交換しても `CounterexamplePack` が保存されることを示す。Branch B の候補を、差 gap と和 gap の二つの five-adic orientation のどちらかへ送る際の対称性 bridge となる。
