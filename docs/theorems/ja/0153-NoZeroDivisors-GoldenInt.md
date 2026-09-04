# 0153 — `instance : NoZeroDivisors GoldenInt`

## Lean の型

```lean
instance : NoZeroDivisors GoldenInt where
  eq_zero_or_eq_zero_of_mul_eq_zero :=
    GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero
```

これは theorem ではなく、`GoldenInt` に対して Mathlib 標準の型クラス `NoZeroDivisors` を登録する匿名 `instance` である。

## 数学的主張・宣言の意味

`NoZeroDivisors GoldenInt` は、黄金整数環で零積が起きたなら少なくとも一方の因子が零である、という性質を型クラスとして公開する。

数学的には

$$
xy=0 \Longrightarrow x=0 \lor y=0
$$

である。

この数学的内容そのものは直前の 0152

```lean
theorem GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero {x y : GoldenInt}
    (h : x * y = 0) : x = 0 ∨ y = 0
```

ですでに証明済みである。0153 は新しい数学を証明するのではなく、その theorem を `NoZeroDivisors` が要求する field にそのまま登録し、Mathlib の一般的な代数 API から利用可能にする宣言である。

## 証明全体での役割

0148 `goldenDoubleEmbedding` から 0152 までは、`GoldenInt` の零因子排除を具体的に証明するための machinery を構築していた。

概略は

$$
\texttt{GoldenInt}
\xrightarrow{\texttt{goldenDoubleEmbedding}}
\texttt{Zsqrtd 5}
\longrightarrow
\text{零積分解}
\longrightarrow
\texttt{GoldenInt}
$$

という流れである。

0152 でその結果が theorem として完成した後、0153 はその結果を algebra hierarchy に登録する。この登録により、後続コードは専用 theorem 名を毎回明示せず、`NoZeroDivisors GoldenInt` という標準的な型クラス制約として零因子がないことを利用できる。

したがって本宣言は、具体的な座標・埋め込み証明から Mathlib の抽象代数世界へ戻る interface boundary である。後続の `Nontrivial GoldenInt` と `IsDomain GoldenInt` へ進むためにも重要である。

## 直接依存する定義・補題

直接依存は次の二点である。

- Mathlib 標準型クラス `NoZeroDivisors`
- 0152 `GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero`

依存関係は極めて単純で、

$$
\texttt{GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero}
\longrightarrow
\texttt{NoZeroDivisors GoldenInt}
$$

となる。

0152 の内部では `goldenDoubleEmbedding_mul`、`Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero`、`goldenDoubleEmbedding_injective` などに依存しているが、それらは0153から見れば間接依存である。

## 証明・構築の流れ

証明 script は存在しない。

```lean
instance : NoZeroDivisors GoldenInt where
  eq_zero_or_eq_zero_of_mul_eq_zero :=
    GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero
```

という structure syntax で、`NoZeroDivisors` が要求する零積分解 field に0152の theorem を代入しているだけである。

構築の流れは

$$
\text{proved theorem}
\longrightarrow
\text{typeclass field}
\longrightarrow
\text{generic algebra API}
$$

という一段の再包装である。

## Lean 固有の処理

この宣言の重要点は typeclass registration にある。

Lean は後続で `[NoZeroDivisors GoldenInt]` が必要になったとき、この匿名 instance を typeclass search で自動的に発見する。したがって利用側では

```lean
GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero h
```

と専用 theorem を直接呼ばずとも、Mathlib が `NoZeroDivisors` に対して用意している一般 theorem や instance 構築を利用できる。

また `where` syntax を使って field 名 `eq_zero_or_eq_zero_of_mul_eq_zero` を明示しているため、0152 theorem と型クラスの契約の対応が非常に読みやすい。

## 冗長・重複箇所

0152 と0153は同じ命題内容を theorem と typeclass field の二層で保持するため、表面的には重複している。

しかし役割は明確に異なる。

- 0152 は具体的な証明内容を保持する named theorem。
- 0153 はその証明を標準 algebra hierarchy に公開する instance。

named theorem を残すことで、具体的証明の provenance を追跡できる。一方 instance 化することで下流の抽象的コードが implementation detail に依存しなくなる。この二層化は Lean のライブラリ設計として自然である。

## 最適化候補

考えられる候補は三つある。

1. 現行どおり0152を named theorem として証明し、0153で instance に登録する。
2. 0152を独立 theorem にせず、`NoZeroDivisors GoldenInt` instance の field 内で直接証明する。
3. より一般的な injective map / zero-product transfer theorem を先に作り、それを使って `NoZeroDivisors GoldenInt` を構築する。

コード行数だけなら2が短くなる可能性がある。しかし現行方式は、複雑な doubled embedding 証明を named theorem として監査でき、その結果だけを typeclass に渡すため、可読性と再利用性に優れる。

FLT5 のように証明 provenance を追跡したい開発では、現行の theorem → instance の二段構成を維持する価値が高い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は全体として `import Mathlib` を使用している。本宣言自身が直接必要とするのは `NoZeroDivisors` の定義と、上流で既に定義された `GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero` だけである。

したがって0153単独のために `Mathlib` 全体を import する必要はないと考えられる。実際の最小 import は `NoZeroDivisors` を含む algebra hierarchy と `GoldenOrder` 上流定義の import に支配される。

今回は Lean build を行わないため、正確な最小 import 集合は未検証である。この点は import 最適化候補としての推測である。

## Comparator challenge 化の可否

適しているが、単独では非常に小さな challenge になる。

比較対象としては、

- named theorem を先に証明して instance に登録する方式
- instance field 内で直接証明する方式
- 一般的な zero-product transfer 補題を介して instance を作る方式

を用意できる。

比較軸は、proof provenance の追跡性、再利用可能な theorem surface、typeclass inference の単純さ、コード量、下流 `IsDomain` 構築の簡潔さである。

特に「数学的証明を named theorem として残すか、それとも instance 内に埋め込むか」という Lean library design の比較課題として有用である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの Lean source と、直前の0152文書である。対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` も存在する。

ただし、本 `NoZeroDivisors` instance に対応する具体的 PDF ページは今回直接特定していない。そのためページ番号・節番号は推測しない。

## 次に読むべき宣言

依存順の次は `GoldenInt` が自明な一元環ではないことを登録する `Nontrivial GoldenInt` instance である。

概念的には

```lean
instance : Nontrivial GoldenInt := ...
```

であり、`0 ≠ 1` を保証する。

0153 の `NoZeroDivisors` とこの `Nontrivial` が揃うことで、続く `IsDomain GoldenInt` への algebra hierarchy が完成に近づく。