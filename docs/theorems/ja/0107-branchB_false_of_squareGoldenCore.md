# 0107 — `branchB_false_of_squareGoldenCore`

## Lean の型

```lean
/-- A contradiction for every square-golden packet closes Branch B. -/
theorem branchB_false_of_squareGoldenCore
    (hCore : BranchBSquareGoldenCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  rcases exists_branchB_squareGoldenNormalForm hPack hBranch with ⟨a, b, hNF⟩
  exact hCore hNF
```

## 数学的主張

この定理は、Branch-B 条件

$$
5\nmid(z-y)
$$

を満たす反例候補 `CounterexamplePack x y z` があり、さらに任意の `BranchBSquareGoldenNormalForm` を矛盾へ送る core

$$
\operatorname{BranchBSquareGoldenCore}
$$

が与えられているなら、`False` が従うことを主張する。

0105 により Branch-B の反例候補からある自然数 $a,b$ が存在して

$$
\operatorname{BranchBSquareGoldenNormalForm}(x,y,z,a,b)
$$

を得る。一方 0106 はそのような packet をすべて拒絶する関数型の proposition である。したがって数学的には

$$
\bigl(\exists a,b,\ P(a,b)\bigr)
\land
\bigl(\forall a,b,\ P(a,b)\to\bot\bigr)
\Longrightarrow \bot
$$

という最終接続である。

## 証明全体での役割

`SquareGoldenNormalForm.lean` 章の終端 theorem であり、square/golden reduction を Branch-B の contradiction に戻す **adapter theorem** である。

前段では 0105 `exists_branchB_squareGoldenNormalForm` が、Branch-B から witness $a,b$ と正規形 packet を構築した。0106 `BranchBSquareGoldenCore` は、その packet が存在すれば矛盾を返す抽象 interface を定義した。本定理はこの二者を接続するだけでよい。

proof architecture は

$$
\text{CounterexamplePack}
+\text{Branch-B}
\longrightarrow
\exists a,b,\ \text{SquareGoldenNormalForm}
\longrightarrow
\text{SquareGoldenCore}
\longrightarrow
\bot
$$

となる。

重要なのは、本定理自身が `GoldenNorm`、平方判別式、$a^{10}$、判別式 $5$ の各数式を再証明しないことである。それらは 0105 以前に packet 化され、本定理では完全に abstraction barrier の向こう側へ隠れている。

## 直接依存する定義・補題

直接依存は次の三つである。

1. `CounterexamplePack x y z`
2. 0105 `exists_branchB_squareGoldenNormalForm`
3. 0106 `BranchBSquareGoldenCore`

実際の証明で project-local theorem として明示的に呼ぶのは 0105 だけで、0106 は仮定 `hCore` の型として利用される。

間接的には 0105 を通じて `BranchBFifthPowerNormalForm`、`SquareGoldenM`、`SquareGoldenN`、`GoldenNorm`、`squareGolden_tenth_boundary_base`、`squareGolden_square_discriminant`、`goldenNorm_eq_fifth_power_of_GN5`、`four_mul_goldenNorm_eq_discriminant_five` などの square/golden bridge 全体を受け取っている。

## 証明の流れ

証明は二段しかない。

### 1. 正規形 packet の witness を取り出す

```lean
rcases exists_branchB_squareGoldenNormalForm hPack hBranch with ⟨a, b, hNF⟩
```

0105 から

```lean
∃ a b : ℕ, BranchBSquareGoldenNormalForm x y z a b
```

を得て、`rcases` で witness $a,b$ と proof `hNF` に分解する。

### 2. universal refuter を適用する

```lean
exact hCore hNF
```

`hCore` の実体は

```lean
∀ {x y z a b : ℕ},
  BranchBSquareGoldenNormalForm x y z a b → False
```

なので、`hNF` を渡すだけで `False` が得られる。$x,y,z,a,b$ は implicit argument として `hNF` の型から推論される。

## Lean 固有の処理

### 1. `rcases ... with ⟨a, b, hNF⟩`

existential witness を一度に三要素へ分解している。ここでは witness 自体を後続の算術に使わず、最後の packet proof `hNF` だけを core に渡す。

したがって $a,b$ は論理的には unpack に必要だが、consumer 側では名前を使わない witness である。

### 2. implicit arguments による `exact hCore hNF`

`BranchBSquareGoldenCore` が $x,y,z,a,b$ を implicit binder にしているため、

```lean
exact hCore hNF
```

だけで適用できる。明示的に

```lean
exact hCore (x := x) (y := y) (z := z) (a := a) (b := b) hNF
```

と書く必要はない。

### 3. tactic-free algebra boundary

この theorem には `ring`、`norm_num`、`omega`、`exact_mod_cast`、`norm_cast` が一切ない。すべての algebraic/cast complexity は upstream theorem に封じ込められている。

これは Lean で abstraction barrier が機能している明瞭な例である。

## 冗長・重複箇所

### `branchB_false_of_fifthPowerCore` と同型の bridge pattern

前段には fifth-power normal form に対する類似 theorem がある。構造は

```lean
rcases exists_... with ⟨..., hNF⟩
exact hCore ...
```

という同じ producer-consumer bridge である。

したがって proof pattern 自体には重複があるが、各 reduction layer ごとに closure theorem を置くことで、どの abstraction level で Branch-B が閉じられるかが明示される。これは保守性を高める意図的な重複である。

### witness 名 `a`, `b` は本体で未使用

`rcases` 後に `a`, `b` を明示的には参照しないため、

```lean
rcases exists_branchB_squareGoldenNormalForm hPack hBranch with ⟨_, _, hNF⟩
```

とも書ける。

ただし witness の数学的意味を読者に見せる現在形には文書性がある。

## 最適化候補

### 候補 A — `obtain` への置換

```lean
obtain ⟨a, b, hNF⟩ := exists_branchB_squareGoldenNormalForm hPack hBranch
exact hCore hNF
```

とできる。意味は同じで、好みの差に近い。

### 候補 B — existential elimination を一行化

```lean
rcases exists_branchB_squareGoldenNormalForm hPack hBranch with ⟨_, _, hNF⟩
exact hCore hNF
```

と witness 名を捨てれば少し短い。ただし博物館的には $a,b$ が正規形 witness であることが見えにくくなる。

### 候補 C — core を existential nonexistence にする

0106 を

```lean
¬ ∃ x y z a b : ℕ, BranchBSquareGoldenNormalForm x y z a b
```

と定義していれば、本 theorem は existential packet をまとめ直して core に渡す形になる。現在の function-style core の方が `hCore hNF` と局所適用でき、ここでは簡潔である。

### 候補 D — producer-consumer bridge の一般化

「`A → ∃ w, P w` と `∀ w, P w → False` から `A → False`」という generic theorem を用意することはできる。しかしこの二行は既に十分短く、generic 化すると theorem 名から square/golden phase が失われるため、現状の specialized theorem には高い説明価値がある。

## 必要な Mathlib import と import 最適化候補

本 theorem 単独では existential elimination と関数適用しか用いず、Mathlib tactic は不要である。

必要な実質依存は project-local な

- `CounterexamplePack`
- `BranchBSquareGoldenCore`
- `exists_branchB_squareGoldenNormalForm`

を提供する module である。

standalone artifact 全体は `import Mathlib` だが、本 theorem を理由に broad `Mathlib` import が必要になることはない。`SquareGoldenNormalForm.lean` 全体では upstream proof に `ring`、`simpa`、`exact_mod_cast` などがあるため、module 単位の最小 import はそれらを含めて検証する必要がある。

本博物館では Lean build を行わないため、具体的最小 import 集合は候補に留める。

## Comparator challenge 化の可否

**非常に適している。** ただし algebraic challenge ではなく、proof plumbing / API design challenge として扱うのがよい。

比較案は例えば次の通り。

```lean
-- A: 現行
rcases exists_branchB_squareGoldenNormalForm hPack hBranch with ⟨a, b, hNF⟩
exact hCore hNF

-- B: witness 名を捨てる
rcases exists_branchB_squareGoldenNormalForm hPack hBranch with ⟨_, _, hNF⟩
exact hCore hNF

-- C: obtain
obtain ⟨a, b, hNF⟩ := exists_branchB_squareGoldenNormalForm hPack hBranch
exact hCore hNF
```

比較軸は、短さ、proof state の読みやすさ、witness の意味保存、error message、将来 packet に field が増えた場合の保守性である。

現行 A は二行でありながら witness の数学的意味も保持しており、かなり良い局所最適解に見える。

## 既存資料との対応

形式的根拠は対象ブランチ `docs/flt5-theorem-museum` の `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/SquareGoldenNormalForm.lean` generated section である。

GitHub connector の code search は今回 upstream 502 を返したため、既存日本語・英語 PDF 内の具体的ページ・節位置は確定できなかった。したがって PDF のページ番号や節番号は推測で補っていない。

Lean source 上では本 theorem の直後に `SquareGoldenNormalForm.lean` の generated section が終了し、次の module `SignedSquareGoldenExceptional.lean` が始まる。

## 次に読むべき定理

次の module `SignedSquareGoldenExceptional.lean` の最初の宣言は

```lean
structure SignedSquareGoldenExceptionalPacket
    (u v w : ℕ) : Type where
  powerSplit : SignedFiveAdicPowerSplit u v w
  M : ℤ
  N : ℤ
  delta : ℤ
  ...
```

である。

したがって依存順では、次号は `SignedSquareGoldenExceptionalPacket` を読み、signed five-adic power split が square/golden exceptional packet へどう拡張されるかを見るのが自然である。
