# 0152 — `GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero`

## Lean の型

```lean
theorem GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero {x y : GoldenInt}
    (h : x * y = 0) : x = 0 ∨ y = 0 := by
  have hemb : goldenDoubleEmbedding x * goldenDoubleEmbedding y = 0 := by
    rw [goldenDoubleEmbedding_mul]
    rw [show goldenMul x y = 0 by exact h]
    rfl
  rcases Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero hemb with hx | hy
  · left
    apply goldenDoubleEmbedding_injective
    calc
      goldenDoubleEmbedding x = 0 := hx
      _ = goldenDoubleEmbedding 0 := by ext <;> rfl
  · right
    apply goldenDoubleEmbedding_injective
    calc
      goldenDoubleEmbedding y = 0 := hy
      _ = goldenDoubleEmbedding 0 := by ext <;> rfl
```

これは theorem である。`GoldenInt` 上で積が零なら、少なくとも一方の因子が零であることを示す。すなわち `GoldenInt` が零因子を持たないことを、後続の `NoZeroDivisors GoldenInt` instance に渡せる形で証明している。

## 数学的主張

主張は

$$
xy=0 \Longrightarrow x=0 \lor y=0
$$

である。

ここで `GoldenInt` は $a+b\varphi$、$\varphi^2=\varphi+1$ という座標環であり、0148 で定義した

$$
E(a+b\varphi)=(2a+b)+b\sqrt5
$$

という doubled embedding `goldenDoubleEmbedding` を用いる。0151 により

$$
E(x)E(y)=2E(xy)
$$

が成立するので、$xy=0$ なら `Zsqrtd 5` 側でも $E(x)E(y)=0$ となる。`Zsqrtd 5` には 0149 の nonsquare instance を通じて零積分解が利用できるため、$E(x)=0$ または $E(y)=0$ を得る。最後に 0150 の単射性から $x=0$ または $y=0$ を引き戻す。

したがって本 theorem は、黄金整数環そのものの零因子排除を、既に整備された $\mathbb Z[\sqrt5]$ 側の零因子排除へ輸送して証明する bridge theorem である。

## 証明全体での役割

0148–0151 で準備した doubled embedding machinery が、ここで初めて一つの algebraic consequence に回収される。

依存の流れは概念的に

$$
\texttt{goldenDoubleEmbedding}
\rightarrow
\texttt{goldenFiveNonsquare}
\rightarrow
\texttt{goldenDoubleEmbedding\_injective}
\rightarrow
\texttt{goldenDoubleEmbedding\_mul}
\rightarrow
\texttt{GoldenInt.eq\_zero\_or\_eq\_zero\_of\_mul\_eq\_zero}
$$

である。

この theorem の直後には

```lean
instance : NoZeroDivisors GoldenInt where
  eq_zero_or_eq_zero_of_mul_eq_zero :=
    GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero
```

が置かれ、その後 `Nontrivial GoldenInt`、`IsDomain GoldenInt` へ進む。したがって本 theorem は `GoldenInt` を単なる `CommRing` から整域方向へ昇格させる決定的な中継点である。

FLT5 の後続ではノルム、整除、単元、Euclidean domain、gcd、第五冪因子分解を使うため、零因子がないことは代数基盤として重要である。

## 直接依存する定義・補題

直接依存する主要事項は次である。

- `GoldenInt`
- `goldenDoubleEmbedding`
- `goldenDoubleEmbedding_mul`
- `goldenDoubleEmbedding_injective`
- `Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero`
- `GoldenInt.ext`

また `Zsqrtd 5` 側で零積分解を利用する背景には 0149 `goldenFiveNonsquare : Zsqrtd.Nonsquare 5` がある。

## 証明の流れ

最初に仮定

```lean
h : x * y = 0
```

を doubled embedding 側の零積

```lean
hemb : goldenDoubleEmbedding x * goldenDoubleEmbedding y = 0
```

へ変換する。

ここでは

```lean
rw [goldenDoubleEmbedding_mul]
rw [show goldenMul x y = 0 by exact h]
rfl
```

と進む。0151 の公式で左辺を $2E(xy)$ に変形し、`x * y = 0` を raw multiplication `goldenMul x y = 0` として使い、最後は定義的計算で閉じる。

次に

```lean
rcases Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero hemb with hx | hy
```

で `Zsqrtd 5` 側の零積分解を行い、二枝に分ける。

第一枝では $E(x)=0$、第二枝では $E(y)=0$ を得る。各枝で 0150 の単射性を適用し、零元の像との等式

```lean
goldenDoubleEmbedding 0 = 0
```

を `ext <;> rfl` で示して元の `GoldenInt` 側へ戻す。

## Lean 固有の処理

### `show goldenMul x y = 0 by exact h`

仮定 `h` は標準 notation の `x * y = 0` である。一方 0151 の右辺には raw function `goldenMul x y` が現れる。`Mul GoldenInt` は `goldenMul` を登録した instance なので両者は定義的に同じであり、`exact h` だけで型が合う。

### `rcases ... with hx | hy`

`Zsqrtd` 側の theorem が返す disjunction を二枝へ分解し、`left` / `right` で最終結論の対応する側を選ぶ。

### `apply goldenDoubleEmbedding_injective`

単射性を「像が等しいなら元が等しい」という方向で使用する。目標 `x = 0` は `E(x)=E(0)` に変換される。

### `by ext <;> rfl`

`Zsqrtd 5` の零元と `goldenDoubleEmbedding 0` が座標ごとに定義的に一致することを extensionality で示す。数学的内容はほぼないが、異なる型の零元・座標 constructor を Lean に明示的に接続する処理である。

## 冗長・重複箇所

証明には左右対称な二枝があり、`x` と `y` だけを入れ替えた同型の処理が重複している。これは disjunction を明確に扱うための意図的な重複と見られる。

また

```lean
rw [show goldenMul x y = 0 by exact h]
```

は `golden_mul_eq` などの bridge lemma を使う形にも書ける可能性がある。ただし現行形は typeclass notation と raw operation が definitional に一致することを直接利用しており、余分な rewrite theorem に依存しない利点がある。

`goldenDoubleEmbedding 0 = 0` も専用 simp lemma を用意すれば二枝で再利用できるが、この theorem 内でしか必要なければ `ext <;> rfl` のままでも十分短い。

## 最適化候補

1. $E(0)=0$ を `[simp]` lemma として公開し、各枝を `simpa` で短縮する。
2. `goldenDoubleEmbedding_injective` と `Zsqrtd` の零積 theorem を組み合わせた一般的な「単射な scaled multiplicative map による零因子輸送」補題を抽象化する。
3. doubled embedding をより構造化された map として表現し、乗法互換性と injectivity を field として持たせる。
4. `GoldenInt` を最初から既存の quadratic-order / `AdjoinRoot` 系構造で構築し、既存の domain instance を再利用する。

ただし現行実装は、FLT5 で必要な最小限の事実を座標レベルで監査可能に保つという利点がある。一般化によってコード量は減っても、proof provenance が見えにくくなる可能性がある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。これはリポジトリ上の生成 artifact で確認できる。

本 theorem が実質的に必要とする機能は、`Zsqrtd` の型と零積 theorem、`Function.Injective`、typeclass ベースの環演算、extensionality、基本 rewrite tactic である。`ring` や `omega` は本 theorem 自体では直接使わないが、直接依存する 0150・0151 の証明では使われる。

したがって module 単位では `Mathlib` 全体より小さい import 集合へ削減できる可能性が高い。ただし今回 Lean build は行わないため、正確な最小 import は未検証であり、最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。少なくとも次の三方式を比較できる。

- 現行の doubled embedding を介した零因子輸送
- `GoldenInt` の座標式から直接 $xy=0$ を解く証明
- generic quadratic-order / `AdjoinRoot` の既存 domain structure を利用する証明

比較軸は、証明行数、非線形整数算術への依存、再利用する Mathlib infrastructure の量、定義的透明性、後続 `NoZeroDivisors` / `IsDomain` instance の簡潔さ、FLT5 固有コードの監査可能性である。

特に座標からの直接証明は式変形が重くなりやすい一方、doubled embedding 方式は `Zsqrtd` 側の既存構造へ責務を移し、証明を非常に局所化している。この trade-off は Comparator challenge として明瞭である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された generated `DkMath/FLT/Five/GoldenOrder.lean` section である。standalone artifact は `import Mathlib` を使用し、元の ordered source module として `DkMath/FLT/Five/GoldenOrder.lean` を列挙している。

対象ブランチには `docs/pdf/FLT5-main-ja-v0-r1.pdf` と `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在することを確認した。ただし本 theorem に対応する具体的ページ・節は今回直接特定していないため、PDF 側の位置は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
instance : NoZeroDivisors GoldenInt where
  eq_zero_or_eq_zero_of_mul_eq_zero :=
    GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero
```

である。

0152 で零積分解 theorem が完成したため、次はその theorem を標準 typeclass `NoZeroDivisors GoldenInt` に登録する一段の interface declaration へ進む。