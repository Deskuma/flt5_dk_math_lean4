# 0106 — `BranchBSquareGoldenCore`

## Lean の型

```lean
/-- The narrowed receiver after both fifth-power and square-golden reduction. -/
abbrev BranchBSquareGoldenCore : Prop :=
  ∀ {x y z a b : ℕ}, BranchBSquareGoldenNormalForm x y z a b → False
```

## 数学的主張

`BranchBSquareGoldenCore` は通常の「数式を証明する theorem」ではなく、Branch-B の square/golden normal form を受け取れば必ず矛盾 `False` を返せる、という **矛盾受信器の型** である。

数学的には、任意の自然数 $x,y,z,a,b$ について、

$$
\operatorname{BranchBSquareGoldenNormalForm}(x,y,z,a,b)
\longrightarrow \bot
$$

を一括して要求する。

0104 `BranchBSquareGoldenNormalForm` が保持する packet を展開すれば、元の Branch-B fifth-power normal form に加えて、

$$
M=z^2+y^2,\qquad N=zy,
$$

$$
\operatorname{GoldenNorm}(M,N)=b^5,
$$

$$
M-2N=a^{10},
$$

$$
M^2-4N^2=(z^2-y^2)^2,
$$

$$
(2M+N)^2-5N^2=4b^5
$$

という square/golden invariant が同時に存在する。

したがって `BranchBSquareGoldenCore` は、これらの invariant を満たす packet が存在しないことを証明するための **最終矛盾コアの契約** である。

## 証明全体での役割

0105 `exists_branchB_squareGoldenNormalForm` までは、Branch-B の仮定から witness $a,b$ と square/golden packet を **構築する側** であった。

本宣言から proof architecture は反転する。

$$
\text{Branch-B candidate}
\longrightarrow
\text{square/golden packet}
\longrightarrow
\text{BranchBSquareGoldenCore}
\longrightarrow
\bot.
$$

つまり前半の算術的・cast 的・座標変換的な詳細をすべて 0105 までに閉じ込め、後半は `BranchBSquareGoldenNormalForm` 一個だけを入力として矛盾を導けばよい。

この設計により、後続の矛盾証明は `GN5` の因数分解や `ℕ → ℤ` の変換を繰り返す必要がなくなる。proof engineering の観点では、これは **reduction boundary** であり、FLT5 の Branch-B 証明を「正規形構築」と「正規形排除」の二つに分離している。

## 直接依存する定義・補題

直接依存する project-local 宣言は 0104 `BranchBSquareGoldenNormalForm` のみである。

```lean
BranchBSquareGoldenNormalForm x y z a b → False
```

という型そのものが contract の全内容であり、本宣言の内部では 0097、0099、0102、0103、0105 を直接参照しない。

ただし意味論的には、0104 の各 field がそれらの定理によって供給され、0105 が packet の inhabitant を構築する。そのため依存グラフ上では、本 core は 0104 を介して前段の square/golden bridge 全体を受け取る。

## 証明の流れ

`abbrev` なので証明 script は存在しない。Lean は単に

```lean
∀ {x y z a b : ℕ}, BranchBSquareGoldenNormalForm x y z a b → False
```

という proposition に `BranchBSquareGoldenCore` という短い名前を与える。

後続 theorem ではこの名前が実際の consumer interface として使われる。

```lean
theorem branchB_false_of_squareGoldenCore
    (hCore : BranchBSquareGoldenCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  rcases exists_branchB_squareGoldenNormalForm hPack hBranch with ⟨a, b, hNF⟩
  exact hCore hNF
```

0105 が packet を作り、本 core がその packet を拒絶することで Branch-B を閉じる。

## Lean 固有の処理

### 1. `abbrev` による透明な別名

`def` ではなく `abbrev` を使っているため、`BranchBSquareGoldenCore` は reducible な別名として扱われる。必要なら Lean は容易に

```lean
∀ {x y z a b : ℕ}, BranchBSquareGoldenNormalForm x y z a b → False
```

へ展開できる。

この用途では計算内容を隠蔽したいのではなく、長い高階 proposition に意味のある名前を与えたいので `abbrev` は自然である。

### 2. implicit binder による witness 非依存性

```lean
∀ {x y z a b : ℕ}, ...
```

と全変数を implicit にしている。consumer は具体的な $x,y,z,a,b$ を明示的に渡さず、packet `hNF` から Lean に推論させられる。

後続の

```lean
exact hCore hNF
```

が一行で済むのはこの設計による。

### 3. `False` を返す関数としての矛盾コア

Lean では proposition $P$ の否定は `P → False` である。本 core は単一 packet の否定ではなく、すべての witness に対してその否定を与える多相な refuter である。

## 冗長・重複箇所

### `BranchBFifthPowerCore` と同型の proof-interface pattern

前段には

```lean
abbrev BranchBFifthPowerCore : Prop :=
  ∀ {x y z a b : ℕ}, BranchBFifthPowerNormalForm x y z a b → False
```

という同型の interface がある。今回の宣言は packet 型を `BranchBSquareGoldenNormalForm` に差し替えた specialization であり、proof architecture 上は意図的な重複である。

この重複は悪い duplication ではない。各 reduction phase の終了点ごとに「ここから先はこの packet だけ見ればよい」という明確な境界を作っている。

### `∀ ... → False` は `¬ ∃ ...` と論理的に対応する

数学的には

$$
\forall x,y,z,a,b,\ P(x,y,z,a,b)\to\bot
$$

と

$$
\neg\exists x,y,z,a,b,\ P(x,y,z,a,b)
$$

は対応する。したがって existential nonexistence theorem として表現することもできる。

しかし downstream で packet を得た直後に `hCore hNF` と適用する現在の形の方が Lean の consumer API として直接的である。

## 最適化候補

### 候補 A — generic packet refuter alias

複数の normal-form core が同じ形を持つため、例えば

```lean
abbrev Refuter (P : α → Prop) : Prop := ∀ x, P x → False
```

のような一般 abstraction を考えることはできる。

ただし current core は複数の implicit witness を持つ dependent な proposition であり、generic 化すると tuple/structure 化が必要になる。名前から数学的 phase が即座に分かる現行 API の方が可読性は高い。

### 候補 B — `¬ ∃ ...` 形式との Comparator

```lean
¬ ∃ x y z a b : ℕ, BranchBSquareGoldenNormalForm x y z a b
```

を core とする設計も可能である。論理的には等価だが、後続 theorem では existential packet を一度再梱包する必要がある。

現在の function form は 0105 から得た witness を `rcases` した後、`hCore hNF` と直結できるので、Lean 実装としては簡潔である。

### 候補 C — structure packet の witness を内部化する

`BranchBSquareGoldenNormalForm` 自体が $x,y,z,a,b$ を parameter として持つ代わりに、witness も field に持つ existential packet structure を用意すれば、core は

```lean
SquareGoldenPacket → False
```

まで単純化できる。

一方で現在の parameterized structure は各 witness を theorem statement に露出させるため、既存 arithmetic API との rewrite が容易である。最適化は単純な短縮ではなく API 設計上の trade-off である。

## 必要な Mathlib import と import 最適化候補

本宣言単独は `Prop`、`∀`、`False`、自然数、既存 project-local structure のみを使い、tactic を一切必要としない。

したがって `BranchBSquareGoldenCore` 自体が Mathlib の重い import を要求するわけではない。実際の必要 import は `BranchBSquareGoldenNormalForm` を提供する project-local module に依存する。

standalone artifact は全体として `import Mathlib` を使用しているが、この一宣言だけを基準にすれば大幅に縮小可能である。

import 最適化の実務的候補は、`SquareGoldenNormalForm.lean` が直接利用する tactic (`ring`, `exact_mod_cast`, `simpa`) と前段 module の import を明示化し、`import Mathlib` 依存を module 単位で削ることである。ただし本博物館では Lean build を実行していないため、最小 import 集合は候補としてのみ記録する。

## Comparator challenge 化の可否

**適している。** ただし algebraic proof challenge ではなく proof-interface design challenge として扱うのがよい。

比較候補は次の三形式である。

```lean
-- A: 現行 function core
abbrev CoreA : Prop :=
  ∀ {x y z a b : ℕ}, BranchBSquareGoldenNormalForm x y z a b → False

-- B: existential nonexistence
abbrev CoreB : Prop :=
  ¬ ∃ x y z a b : ℕ, BranchBSquareGoldenNormalForm x y z a b

-- C: witness を内包した packet を作り、その一変数 refuter にする
-- abbrev CoreC : Prop := ExistentialSquareGoldenPacket → False
```

比較軸は、後続 theorem の短さ、witness 推論、rewrite のしやすさ、error message の読みやすさ、generalization のしやすさである。

現行 A は `exact hCore hNF` という consumer 側の短さが強みである。

## 既存資料との対応

形式的根拠は対象ブランチ `docs/flt5-theorem-museum` の `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/SquareGoldenNormalForm.lean` generated section である。

既存の日本語・英語 PDF は narrative context の補助資料とする方針だが、今回の GitHub connector の code search は upstream error となり、PDF 内の具体的なページ・節位置は確認できなかった。そのためページ番号や節番号を推測で補っていない。

## 次に読むべき定理

直後の theorem は

```lean
theorem branchB_false_of_squareGoldenCore
    (hCore : BranchBSquareGoldenCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  rcases exists_branchB_squareGoldenNormalForm hPack hBranch with ⟨a, b, hNF⟩
  exact hCore hNF
```

である。

0105 が Branch-B から packet を構築し、0106 が packet を拒絶する abstract receiver を定義した。次の `branchB_false_of_squareGoldenCore` はこの二つを二行で接続して Branch-B 全体を閉じる。

したがって次号では、

$$
\text{existence of packet}
+\text{universal packet refuter}
\Longrightarrow \bot
$$

という proof-interface の最終接続を読むのが依存順として自然である。
