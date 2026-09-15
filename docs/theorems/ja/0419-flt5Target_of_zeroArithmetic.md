# 0419 `flt5Target_of_zeroArithmetic`

## 宣言種別

`theorem`

## Lean の型

```lean
/-- Conditional receiver after the proved unit classification is supplied. -/
theorem flt5Target_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  flt5Target_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

## 数学的主張・宣言の意味

この theorem は、zero-sector に残る Diophantine 候補を排除する算術契約

```lean
GoldenZeroSectorArithmeticExclusion
```

だけを仮定すれば、指数 5 の Fermat 方程式に正の自然数解が存在しないという公開 target

```lean
FLT5Target
```

が従うことを述べる。

型を数式的に読むと

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{FLT5Target}
$$

である。0417 `FLT5Target` を展開すれば結論は

$$
\forall x,y,z\in\mathbb N_{>0},
\qquad
x^5+y^5\ne z^5
$$

である。

直前の 0418

```lean
flt5Target_of_unitClasses_of_zeroArithmetic
```

は

$$
\mathrm{GoldenUnitClassesModFifth}
\to
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{FLT5Target}
$$

という二入力の conditional endpoint だった。0419 はその第一入力 `GoldenUnitClassesModFifth` に、既に証明済みの theorem

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

を代入することで、外部仮定を一つ減らしている。

したがって 0419 自身は新しい数論計算や場合分けを行わない。これは「黄金単元の第五冪剰余類分類はもはや未解決の入力ではない」という事実を Main 層へ反映する specialization theorem である。

## 証明全体での役割

FLT5 の最終 closure は、Main 層で仮定を順に消していく形になっている。

0418 では

$$
\mathrm{GoldenUnitClassesModFifth}
+
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\mathrm{FLT5Target}
$$

が公開された。

0419 では unit-class 側を既証明 provider

```lean
goldenUnitClassesModFifth
```

で埋めるため、残る boundary は

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
$$

だけになる。

さらに次の 0420 `flt5Target` では、0412 で既に無条件に得られている

```lean
goldenZeroSectorArithmeticExclusion : GoldenZeroSectorArithmeticExclusion
```

を 0419 に代入することで、最終 target を仮定なしで閉じる。

従って Main 層の最後の三段階は

$$
\begin{aligned}
&\mathrm{GoldenUnitClassesModFifth}
+\mathrm{GoldenZeroSectorArithmeticExclusion}
\to \mathrm{FLT5Target},\\
&\mathrm{GoldenZeroSectorArithmeticExclusion}
\to \mathrm{FLT5Target},\\
&\mathrm{FLT5Target}
\end{aligned}
$$

という dependency discharge の列として読める。

0419 はその中央段であり、unit classification の条件付き境界を消去する役割を持つ。

## 直接依存する定義・補題

### `flt5Target_of_unitClasses_of_zeroArithmetic`

0418 で解説した Main 層の conditional receiver である。

```lean
theorem flt5Target_of_unitClasses_of_zeroArithmetic
    (hClasses : GoldenUnitClassesModFifth)
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic hClasses hArithmetic
```

0419 が直接呼び出す theorem はこれである。

### `goldenUnitClassesModFifth`

黄金整数環の unit classification を無条件に供給する theorem である。

```lean
/-- Every golden unit has a representative among five classes modulo fifth powers. -/
theorem goldenUnitClassesModFifth : GoldenUnitClassesModFifth := by
  intro epsilon hepsilon
  exact goldenUnitFifthClass_of_unit epsilon hepsilon
```

これにより、0418 の第一引数は外部仮定として保持する必要がなくなる。

数学的には、任意の golden unit が第五冪を除けば五つの代表 class のいずれかに属するという分類結果を provider として渡している。

### `GoldenZeroSectorArithmeticExclusion`

0419 に残される唯一の仮定である。

zero-sector で生じる整数パラメータの Diophantine configuration を排除する contract であり、0419 はその内部構造には立ち入らず、完成済み proposition `hArithmetic` を 0418 へそのまま転送する。

### `FLT5Target`

0417 で定義された公開 target である。

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

0419 の結論型である。

## 証明または構築の流れ

証明は一つの theorem application だけで構成される。

```lean
flt5Target_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

### 1. zero-sector arithmetic を受け取る

```lean
hArithmetic : GoldenZeroSectorArithmeticExclusion
```

0419 が外部から要求する唯一の入力である。

### 2. unit classification を既証明 theorem で固定する

```lean
goldenUnitClassesModFifth
```

は型

```lean
GoldenUnitClassesModFifth
```

を持つため、0418 の第一引数にそのまま入る。

### 3. 0418 を特殊化する

```lean
flt5Target_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

と適用すると、0418 の二つの引数が両方埋まり、結果として

```lean
FLT5Target
```

が返る。

追加の rewrite、case split、算術 tactic は必要ない。

## Lean 固有の処理

### theorem を値として引数へ渡す

Lean では proposition の theorem は、その proposition の proof term である。

したがって

```lean
goldenUnitClassesModFifth : GoldenUnitClassesModFifth
```

という theorem は、0418 が要求する

```lean
hClasses : GoldenUnitClassesModFifth
```

の具体的な値として直接渡せる。

これは Curry–Howard 対応がコード上に最も素直に現れる箇所の一つである。

### partial specialization

0418 は二入力の curried theorem である。

```lean
GoldenUnitClassesModFifth →
GoldenZeroSectorArithmeticExclusion →
FLT5Target
```

0419 は第一引数を `goldenUnitClassesModFifth` に固定した specialization と見ることができる。

概念的には

```lean
fun hArithmetic =>
  flt5Target_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

であり、実際の宣言では `hArithmetic` が明示引数なので lambda を書く必要がない。

### tactic block を使わない term proof

証明は

```lean
:=
  flt5Target_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

という term-style であり、`by` block は不要である。

この短さは、新しい証明探索ではなく、既存 theorem の dependency を埋めているだけであることを正確に反映している。

## 冗長・重複箇所

0419 は数学的内容としては 0418 の特殊化に過ぎず、新しい lemma を導出しているわけではない。

コード量だけを見れば、0420 `flt5Target` から直接

```lean
flt5Target_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth
  goldenZeroSectorArithmeticExclusion
```

と書けば 0419 を省略できる。

しかし 0419 を残すことで、証明境界が明確になる。

- unit classification は完全に解決済み
- zero-sector arithmetic だけを差し替え可能な receiver として残す
- 最終 endpoint はその receiver に無条件 provider を入れるだけ

この分離は、依存監査や将来の別証明 route の差し替えに有利である。

0418、0419、0420 は薄い wrapper が連続するが、これは偶然の重複というより、conditional assumptions が一つずつ discharge される様子を名前付き theorem として記録する設計である。

## 最適化候補

### 1. 0419 を削除して 0420 で二 provider を直接代入する

最短コードだけを目標とするなら可能である。

```lean
flt5Target_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth
  goldenZeroSectorArithmeticExclusion
```

とすれば最終 theorem を一段で構築できる。

ただし `GoldenZeroSectorArithmeticExclusion → FLT5Target` という有用な中間 API が消えるため、監査性と再利用性は下がる。

### 2. `flt5Target_of_unitClasses_of_zeroArithmetic` を直接 closure theorem に置換する

0419 は理論上

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth hArithmetic
```

と書くこともできる。

しかし Main 層から closure 層の内部 API を直接参照する形になるため、現在の 0418 を経由する構造の方が module boundary は明確である。

### 3. provider 注入パターンの一般化

「条件付き theorem の一引数を既証明 provider で固定する」というパターン自体は一般化可能である。しかし、この程度の一行 specialization に generic combinator を導入すると、かえって読みづらくなる可能性が高い。

現状の explicit application が妥当である。

## 必要な Mathlib import

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

ただし 0419 の本体が直接使用する Lean 機能は theorem application のみであり、Mathlib の算術 tactic、環論 API、valuation API などを直接呼び出していない。

実質的な依存は次の DkMath 宣言を供給する module 群である。

- `FLT5Target`
- `GoldenZeroSectorArithmeticExclusion`
- `goldenUnitClassesModFifth`
- `flt5Target_of_unitClasses_of_zeroArithmetic`

standalone の ordered source modules では、unit classification は `GoldenUnitClassification.lean`、zero-sector closure は `SignedGoldenZeroSectorFinal.lean`、公開 receiver は `Main.lean` に対応する。

### import 最適化候補

0419 単体に `import Mathlib` 全体が必要とは考えにくい。分割ソースでは、上記 DkMath declarations を提供する imports が閉じていれば十分な可能性が高い。

ただし今回は Lean build を実施しておらず、最小 import closure を実測していない。そのため具体的な Mathlib module 名を最小構成として断定しない。

## Comparator challenge 化の可否

 **適している。難度は低め。**

基本 challenge は次の形にできる。

```lean
theorem challenge
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target := by
  ?_
```

利用可能な theorem として

```lean
goldenUnitClassesModFifth
flt5Target_of_unitClasses_of_zeroArithmetic
```

を与えれば、solver が「未解決の第一引数を既証明 provider で埋める」という dependency specialization を認識できるかを検査できる。

難度を上げるなら 0418 を隠し、

```lean
positiveFermat5Refuter_of_unitClasses_of_zeroArithmetic
```

から直接 `FLT5Target` へ到達させる構成にすれば、`PositiveFermat5Refuter` と `FLT5Target` の definitional equality まで理解する必要がある。

さらに 0420 と組み合わせれば、二つの conditional input を既証明 provider で順次 discharge して無条件 theorem を構成する小さな dependency-resolution challenge にできる。

## 次に読むべき宣言

次は 0420 `flt5Target`、種別は `theorem` である。

```lean
/--
The unconditional exponent-five target for positive natural numbers. It denies
`Fermat5Equation x y z`, namely `x^5 + y^5 = z^5`, for every positive
`x`, `y`, and `z`. This is not a general-exponent or signed-integer theorem.
-/
theorem flt5Target : FLT5Target :=
  flt5Target_of_zeroArithmetic goldenZeroSectorArithmeticExclusion
```

0419 が

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{FLT5Target}
$$

を確立したのに対し、0420 は既証明の無条件 provider

```lean
goldenZeroSectorArithmeticExclusion
```

を代入し、ついに

$$
\mathrm{FLT5Target}
$$

を仮定なしで得る。

したがって 0420 は conditional receiver chain を閉じる公開の無条件 endpoint であり、その後は通常引数形式の wrapper へ進む。