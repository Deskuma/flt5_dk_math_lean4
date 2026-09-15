# 0420 `flt5Target`

## 宣言種別

`theorem`

## Lean の型

```lean
/--
The unconditional exponent-five target for positive natural numbers. It denies
`Fermat5Equation x y z`, namely `x^5 + y^5 = z^5`, for every positive
`x`, `y`, and `z`. This is not a general-exponent or signed-integer theorem.
-/
theorem flt5Target : FLT5Target :=
  flt5Target_of_zeroArithmetic goldenZeroSectorArithmeticExclusion
```

## 数学的主張・宣言の意味

この theorem は、指数 5 の Fermat 方程式について、この開発が最終的に公開する無条件 target を証明する。

0417 `FLT5Target` を展開すると、型は

```lean
∀ x y z : ℕ,
  0 < x →
  0 < y →
  0 < z →
  ¬ Fermat5Equation x y z
```

であり、`Fermat5Equation` は

```lean
x ^ 5 + y ^ 5 = z ^ 5
```

を表す。従って数学的には

$$
\forall x,y,z\in\mathbb N_{>0},
\qquad
x^5+y^5\ne z^5
$$

を主張する。

重要なのは、0420 にはもはや仮定引数が存在しないことである。0418 と 0419 では proof boundary を条件付き receiver として公開していたが、0420 は最後に残っていた

```lean
GoldenZeroSectorArithmeticExclusion
```

を既証明 theorem

```lean
goldenZeroSectorArithmeticExclusion
```

で埋める。この一行で、FLT5 証明の依存鎖が無条件 endpoint まで閉じる。

ただし正本の docstring が明示する通り、これは指数 5・正の自然数に限定した theorem であり、一般指数の Fermat 最終定理や任意の符号付き整数についての theorem を主張するものではない。

## 証明全体での役割

0420 は `Main.lean` における中心的な無条件 endpoint である。

直前の 0419 は

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{FLT5Target}
$$

という receiver

```lean
flt5Target_of_zeroArithmetic
```

を与えた。

一方、0412 `goldenZeroSectorArithmeticExclusion` は strict infinite descent を含む zero-sector の全構築を経て、

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
$$

そのものを仮定なしで証明している。

0420 はこの二つを合成する。

$$
\bigl(
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{FLT5Target}
\bigr)
+
\mathrm{GoldenZeroSectorArithmeticExclusion}
\Longrightarrow
\mathrm{FLT5Target}
$$

従ってここでは新しい数論的議論、場合分け、降下、valuation 計算は行わない。これまで個別 module に分離されていた proof obligations がすべて解決済みであることを、最終 proposition の proof term として接続する closure point である。

依存鎖を Main 層だけで見ると、

$$
\begin{aligned}
&\mathrm{GoldenUnitClassesModFifth}
\to
\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{FLT5Target},\\
&\mathrm{GoldenZeroSectorArithmeticExclusion}
\to
\mathrm{FLT5Target},\\
&\mathrm{FLT5Target}
\end{aligned}
$$

と段階的に仮定が消えていき、0420 が最後の行に相当する。

## 直接依存する定義・補題

### `FLT5Target`

0417 で定義された `abbrev : Prop` である。

```lean
abbrev FLT5Target : Prop :=
  ∀ x y z : ℕ,
    0 < x →
    0 < y →
    0 < z →
    ¬ Fermat5Equation x y z
```

0420 の返り値そのものである。

### `flt5Target_of_zeroArithmetic`

0419 で解説した conditional receiver である。

```lean
theorem flt5Target_of_zeroArithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) : FLT5Target :=
  flt5Target_of_unitClasses_of_zeroArithmetic
    goldenUnitClassesModFifth hArithmetic
```

0420 はこの theorem の唯一の引数を埋める。

### `goldenZeroSectorArithmeticExclusion`

0412 で得られた無条件 provider である。

```lean
theorem goldenZeroSectorArithmeticExclusion :
    GoldenZeroSectorArithmeticExclusion :=
  goldenZeroSectorArithmeticExclusion_of_factorExclusion
    goldenZeroSectorFactorExclusion
```

その背後では candidate、inversion packet、factor packet、descent packet という zero-sector の構造を経て、strict infinite descent により候補が排除される。0420 自身はその内部を再展開せず、完成済みの proposition proof として受け取る。

## 証明または構築の流れ

証明本体は

```lean
flt5Target_of_zeroArithmetic goldenZeroSectorArithmeticExclusion
```

だけである。

### 1. 条件付き endpoint を取る

0419 から

```lean
flt5Target_of_zeroArithmetic :
  GoldenZeroSectorArithmeticExclusion → FLT5Target
```

がある。

### 2. 最後の input に無条件 provider を渡す

0412 の

```lean
goldenZeroSectorArithmeticExclusion :
  GoldenZeroSectorArithmeticExclusion
```

を適用する。

### 3. `FLT5Target` を得る

関数適用の結果として

```lean
FLT5Target
```

の proof term が生成される。

追加の `by` block、rewrite、simp、omega、norm_num、ring などは不要である。

## Lean 固有の処理

### proposition と proof term の接続

Lean では

```lean
GoldenZeroSectorArithmeticExclusion
```

は `Prop` であり、

```lean
goldenZeroSectorArithmeticExclusion
```

はその proof term である。

したがって

```lean
flt5Target_of_zeroArithmetic
```

が要求する proposition 引数へ theorem をそのまま値として渡せる。

0420 は Curry–Howard 対応が最終 closure に直接現れた例である。

### term-style proof

宣言は

```lean
:=
  flt5Target_of_zeroArithmetic goldenZeroSectorArithmeticExclusion
```

という完全な term proof である。

証明が一行なのは内容が浅いからではない。むしろ全ての proof search と算術的困難が依存先で解決済みであり、この地点では型の接続だけで閉じるよう設計されているためである。

### `abbrev` の transparency

結論型 `FLT5Target` は `abbrev` なので、後続 theorem は必要に応じてその本体

```lean
∀ x y z : ℕ, ...
```

として扱える。そのため次の `fermatFive_no_positive_solution` では `flt5Target x y z hx hy hz` と通常の関数のように直接適用できる。

## 冗長・重複箇所

0420 自体は 0419 と 0412 の単純合成であり、数論上の新情報を追加しない。

最短化だけを目標にするなら、0418 を直接用いて

```lean
flt5Target_of_unitClasses_of_zeroArithmetic
  goldenUnitClassesModFifth
  goldenZeroSectorArithmeticExclusion
```

と書くこともできる。さらに内部 closure theorem へ直接接続する設計も理論上は可能である。

しかし現行構造では、

- 0418: unit classification と zero-sector arithmetic の両方を公開する receiver
- 0419: unit classification を discharge した receiver
- 0420: zero-sector arithmetic も discharge した unconditional endpoint

という三段階が名前付き theorem として保存される。

これは証明境界の監査、依存差し替え、将来の別 route 比較に有益であり、単なる重複とは言い切れない。

## 最適化候補

### 1. Main 層 wrapper の圧縮

コード量だけを削減するなら 0419 を省略し、0420 で二つの provider を直接 0418 に渡せる。

ただし conditional API が一段失われるため、現行構造の方が proof architecture を読みやすい。

### 2. endpoint 名の統合

`FLT5Target` と `PositiveFermat5Refuter` は proposition shape が対応しており、内部 closure から直接 public endpoint を返す設計も可能である。しかし内部 refuter と公開 theorem target を別名で維持する現在の設計は、層の役割を明示する利点がある。

### 3. proof term の変更

現状の一行 term はすでにほぼ最小であり、局所的な最適化余地はない。`exact` や `simpa` を挟む方がむしろ冗長になる。

## 必要な Mathlib import

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

ただし 0420 の本体が直接必要とする機能は theorem application のみであり、Mathlib の tactic や算術 API を直接参照しない。

実質的に必要なのは、次の DkMath 宣言が利用可能であることだけである。

- `FLT5Target`
- `flt5Target_of_zeroArithmetic`
- `goldenZeroSectorArithmeticExclusion`

standalone の ordered source modules では、`SignedGoldenZeroSectorFinal.lean` が無条件 zero-sector provider を供給し、`Main.lean` が public endpoint を構成する。

### import 最適化候補

分割ソースでは、上記宣言を供給する DkMath module import の推移閉包だけで十分である可能性が高く、0420 単独のために `Mathlib` 全体を直接 import する必要性は低い。

ただし今回は Lean build を実施しておらず、最小 import closure を実測していない。そのため具体的な Mathlib module の最小集合は未確認であり、断定しない。

## Comparator challenge 化の可否

 **適している。難度は低いが、proof dependency resolution の教材として明快である。**

基本 challenge は

```lean
theorem challenge : FLT5Target := by
  ?_
```

として、

```lean
flt5Target_of_zeroArithmetic
goldenZeroSectorArithmeticExclusion
```

を利用可能にすればよい。

solver が

```lean
GoldenZeroSectorArithmeticExclusion → FLT5Target
```

と

```lean
GoldenZeroSectorArithmeticExclusion
```

を合成できるかを検査できる。

難度を上げるなら 0419 を隠し、0418 と二つの provider から直接 `FLT5Target` を構築させる。さらに receiver 群も隠せば、closure 層の `PositiveFermat5Refuter` と `FLT5Target` の definitional correspondence を辿る challenge にできる。

0420 単独は数学探索 challenge ではなく、巨大な証明依存グラフの最後の proof-term composition を認識する challenge として価値がある。

## 次に読むべき宣言

次は 0421 `fermatFive_no_positive_solution`、種別は `theorem` である。

```lean
/--
Ordinary-argument wrapper around `flt5Target`: for positive natural numbers
`x`, `y`, and `z`, it proves the negation of `Fermat5Equation x y z`, i.e.
`x^5 + y^5 = z^5`. It does not expose a general-exponent theorem or a theorem
about arbitrary signed integers.
-/
theorem fermatFive_no_positive_solution
    (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ¬ Fermat5Equation x y z :=
  flt5Target x y z hx hy hz
```

0420 は proposition 全体としての無条件 endpoint を返す。0421 はそれを通常の引数 `x y z hx hy hz` を取る theorem として展開し、利用者が直接適用しやすい公開 wrapper にする。

従って 0420 で証明自体の無条件 closure は完成するが、宣言列としてはまだ後続の public wrapper と追加 facade theorem が残っている。