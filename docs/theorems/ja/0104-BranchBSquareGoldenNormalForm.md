# 0104 — `BranchBSquareGoldenNormalForm`

## Lean の型

```lean
structure BranchBSquareGoldenNormalForm
    (x y z a b : ℕ) : Prop where
  normal : BranchBFifthPowerNormalForm x y z a b
  golden_eq :
    GoldenNorm (SquareGoldenM z y) (SquareGoldenN z y) = (b : ℤ) ^ 5
  tenth_boundary :
    SquareGoldenM z y - 2 * SquareGoldenN z y = (a : ℤ) ^ 10
  square_discriminant :
    (SquareGoldenM z y) ^ 2 - 4 * (SquareGoldenN z y) ^ 2 =
      ((z : ℤ) ^ 2 - (y : ℤ) ^ 2) ^ 2
  discriminant_five_eq :
    (2 * SquareGoldenM z y + SquareGoldenN z y) ^ 2 -
        5 * (SquareGoldenN z y) ^ 2 =
      4 * (b : ℤ) ^ 5
```

これは theorem ではなく、Branch-B の fifth-power normal form を square/golden 座標へ射影した後に保持したい四つの事実を束ねる `Prop` 値の structure である。

## 数学的主張

0100・0101 の座標を

$$
M=z^2+y^2,\qquad N=zy
$$

と書く。本 structure は、既に得られている Branch-B fifth-power normal form と同時に、次の三種類の二次形式情報を保持する。

まず golden norm の fifth-power 条件

$$
\operatorname{GoldenNorm}(M,N)=b^5.
$$

次に gap から来る tenth-power 境界

$$
M-2N=a^{10}.
$$

さらに endpoint-square 判別式

$$
M^2-4N^2=(z^2-y^2)^2.
$$

最後に golden norm を判別式 $5$ の形へ対角化した式

$$
(2M+N)^2-5N^2=4b^5.
$$

したがって `BranchBSquareGoldenNormalForm` は単一の新恒等式を主張する宣言ではない。Branch-B の自然数データ、fifth-power 分解、square-world の完全平方境界、golden quadratic form、判別式 $5$ を一つの証明 packet として同時に保存する。

特に二本の「平方世界」が並行している点が重要である。

$$
M-2N=a^{10}=(a^5)^2
$$

は gap 自身の平方境界であり、

$$
M^2-4N^2=(z^2-y^2)^2
$$

は endpoint-square 座標が持つ独立な平方判別式である。一方、

$$
(2M+N)^2-5N^2=4b^5
$$

は同じ $(M,N)$ を黄金比型二次形式へ読むと現れる判別式 $5$ の境界である。

## 証明全体での役割

この structure の役割は **保存量の合流点** である。

それ以前の proof chain では、情報が別々の補題として存在していた。

- `BranchBFifthPowerNormalForm` は $z=y+a^5$ と `GN5 ... = b^5` を含む Branch-B の fifth-power normal form を保持する。
- 0099 `goldenNorm_eq_fifth_power_of_GN5` は GN5 の fifth-power 情報を golden norm へ輸送する。
- 0102 `squareGolden_tenth_boundary_base` は $M-2N=(z-y)^2$ を与える。
- 0103 `squareGolden_square_discriminant` は $M^2-4N^2=(z^2-y^2)^2$ を与える。
- 0097 `four_mul_goldenNorm_eq_discriminant_five` は golden norm を判別式 $5$ の形へ対角化する。

`BranchBSquareGoldenNormalForm` はこれらを一つの型に閉じ込め、後続 proof が再び元の cyclotomic 展開へ戻らなくても、必要な invariant を field projection だけで取得できるようにする。

Lean source では直後の `exists_branchB_squareGoldenNormalForm` がこの structure の inhabitant を構成する。そこで

```lean
exact ⟨a, b, hNF, hGolden, hTenth, hSquare, hDiscFive⟩
```

と、五つのパラメータのうち existential に選ぶ `a,b` に続き、structure の四フィールドが順に投入される。つまり本 structure は後続 theorem の **target data model** である。

さらに、その次の

```lean
abbrev BranchBSquareGoldenCore : Prop :=
  ∀ {x y z a b : ℕ}, BranchBSquareGoldenNormalForm x y z a b → False
```

によって、この packet を受け取って矛盾を返すだけの狭い core interface が作られる。証明全体のアーキテクチャ上、本 structure は「複雑な前処理」と「最終 contradiction core」を切り離す境界でもある。

## 直接依存する定義・補題

宣言の型に直接現れる project-local 依存は次である。

1. `BranchBFifthPowerNormalForm`
2. 0093 `GoldenNorm`
3. 0100 `SquareGoldenM`
4. 0101 `SquareGoldenN`

加えて、各 field を実際に構成する直後の theorem では次の既存結果が実質的依存になる。

1. 0099 `goldenNorm_eq_fifth_power_of_GN5`
2. 0102 `squareGolden_tenth_boundary_base`
3. 0103 `squareGolden_square_discriminant`
4. 0097 `four_mul_goldenNorm_eq_discriminant_five`

ただし structure 宣言そのものはこれら四 theorem を参照しない。Lean では structure の型を宣言することと、その inhabitant を構成することは分離されているためである。

## 証明の流れ

本宣言自体には `by` proof script がない。代わりに「何を証明済みとして一緒に運ぶか」を field として指定する。

概念的には次の四段階で読むとよい。

### 1. 元の fifth-power provenance を保持する

```lean
normal : BranchBFifthPowerNormalForm x y z a b
```

この field を残すことで、square/golden 座標への射影後も元の Branch-B normal form に戻れる。

### 2. golden norm の fifth-power 値を固定する

```lean
golden_eq :
  GoldenNorm (SquareGoldenM z y) (SquareGoldenN z y) = (b : ℤ) ^ 5
```

GN5 で得た fifth-power carrier を整数二次形式へ移して保存する。

### 3. square-world の二本の境界を同時保存する

```lean
tenth_boundary :
  SquareGoldenM z y - 2 * SquareGoldenN z y = (a : ℤ) ^ 10
```

および

```lean
square_discriminant :
  (SquareGoldenM z y) ^ 2 - 4 * (SquareGoldenN z y) ^ 2 =
    ((z : ℤ) ^ 2 - (y : ℤ) ^ 2) ^ 2
```

である。前者は gap $a^5=z-y$ から来る平方、後者は endpoint coordinates 自体の平方判別式である。

### 4. 判別式 $5$ の形を保存する

```lean
discriminant_five_eq :
  (2 * SquareGoldenM z y + SquareGoldenN z y) ^ 2 -
      5 * (SquareGoldenN z y) ^ 2 =
    4 * (b : ℤ) ^ 5
```

これは golden norm の対角化を packet 内に materialize した field である。後続では `GoldenNorm` を unfold し直すことなく、直接 Pell 型・quadratic-order 型の式として利用できる。

## Lean 固有の処理

### 1. `structure ... : Prop` による proof packet

本 structure はデータ構造でありながら sort は `Prop` である。したがって各 field は計算用データではなく証明情報であり、proof irrelevance の世界に属する。

これは「新しい数値を計算する object」ではなく、「同じ $(x,y,z,a,b)$ が複数の invariant を同時に満たす」という certificate を表す設計である。

### 2. 型境界を `ℤ` 側へ固定している

パラメータ `x y z a b` はすべて `ℕ` だが、quadratic form の各 field は整数値で記述される。特に差や判別式を扱うため、`SquareGoldenM/N : ℕ → ℕ → ℤ` の時点で整数へ移している。

このため structure 内では `Nat.sub` の切り詰め問題を避けられ、

$$
M-2N
$$

や

$$
(2M+N)^2-5N^2
$$

を通常の環演算として保持できる。

### 3. field 名が API になる

後続では `.normal`、`.golden_eq`、`.tenth_boundary`、`.square_discriminant`、`.discriminant_five_eq` という projection が自動生成される。

とりわけ現行 source の最後の field 名は `discriminant_five_eq` である。記事作成時点の branch source を基準とし、古い説明や推測で別名を採用しない。

### 4. 証明の構成順が field 順序に依存する

constructor 記法

```lean
⟨hNF, hGolden, hTenth, hSquare, hDiscFive⟩
```

を用いる場合、field 順序が意味を持つ。named-field constructor にすれば順序依存を弱められるが、現行 theorem は簡潔な positional constructor を採用している。

## 冗長・重複箇所

最も明確な重複は `golden_eq` と `discriminant_five_eq` の関係である。0097 により一般に

$$
4\operatorname{GoldenNorm}(M,N)=(2M+N)^2-5N^2
$$

なので、`golden_eq` があれば `discriminant_five_eq` は導出可能である。

したがって論理的には後者は冗長 field である。しかし API としては価値がある。後続で必要なのが判別式 $5$ の式なら、毎回 0097 を適用する必要がなく、packet から直接 projection できるからである。

同様に `square_discriminant` は 0100・0101 の定義だけから恒等式として再証明できる。それでも field として materialize することで、「この packet が square invariant まで構築済み」という phase boundary が明示される。

`normal` も downstream が square/golden 情報しか使わない段階では過剰に見えるが、provenance を保持するために有用である。これを落とすと元の positivity・coprimality・fifth-power normal form 情報へ戻りにくくなる。

したがって本 structure の重複は、論理最小化より **証明段階の情報保存と API 明示性** を優先したものと読むべきである。

## 最適化候補

### 候補 A — 最小 core packet と derived API を分離する

論理的に最小化するなら、例えば

- `normal`
- `golden_eq`
- `tenth_boundary`
- `square_discriminant`

だけを field とし、`discriminant_five_eq` は theorem projection として後から導出する設計がある。

利点は invariant 間の依存関係が明確になり、constructor obligation が一つ減ること。欠点は downstream で判別式 $5$ を使うたび導出が必要になることだ。

### 候補 B — named-field constructor を使う

後続 theorem の

```lean
exact ⟨a, b, hNF, hGolden, hTenth, hSquare, hDiscFive⟩
```

は短いが、structure の field 追加・並べ替えに弱い。例えば

```lean
refine ⟨a, b, {
  normal := hNF
  golden_eq := hGolden
  tenth_boundary := hTenth
  square_discriminant := hSquare
  discriminant_five_eq := hDiscFive
}⟩
```

のように named fields を使えば保守性は上がる。ただし記述量は増える。

### 候補 C — 座標を structure 化する

`SquareGoldenM z y` と `SquareGoldenN z y` が各 field で何度も現れるため、

```lean
structure SquareGoldenCoordinates where
  M : ℤ
  N : ℤ
```

のような座標 object を導入する案もある。

しかし現在は二つの `def` が軽量で、rewrite も単純である。座標 structure を導入すると projection と constructor が増え、Lean proof surface が必ずしも小さくならない。

### 候補 D — field の semantic grouping

square-side と golden-side を substructure に分ける設計も考えられる。例えば `SquareBoundaryPacket` と `GoldenNormPacket` を作り、それらを合成する方式である。

これは概念分離には有効だが、この段階では packet が四 field しかないため、現行の flat structure のほうが読みやすい可能性が高い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は

```lean
import Mathlib
```

を使用している。

`BranchBSquareGoldenNormalForm` 宣言そのものは tactic を一切使用しない。必要なのは

- `ℕ`, `ℤ`
- 冪・加減乗算の notation と基本型クラス
- project-local な `BranchBFifthPowerNormalForm`
- `GoldenNorm`
- `SquareGoldenM`
- `SquareGoldenN`

である。

したがってこの structure 単体だけを見れば `Mathlib` 全体 import は大きく過剰である。

一方、同じ `SquareGoldenNormalForm.lean` module の直後の構成 theorem は `simpa`、`exact_mod_cast`、`ring`、`rw` を利用し、依存先 0097・0099・0102・0103 も tactic 群を必要とする。ゆえに module 全体の最小 import はこの structure だけからは確定できない。

import 最適化を行うなら、まず project-local dependency graph を明示し、その上で tactic import を `Mathlib.Tactic` の必要部分へ縮小し、Lean build で確認するのが安全である。本回はユーザー指定どおり Lean build を実施していないため、具体的な最小 import list は推測として断定しない。

## Comparator challenge 化の可否

適している。ただし通常の「同じ theorem をどう短く証明するか」ではなく、 **proof packet API 設計 challenge** として扱うのがよい。

比較対象は例えば次である。

1. 現行の flat structure で derived invariant も field に materialize する。
2. 論理最小 field のみ保持し、`discriminant_five_eq` を derived theorem にする。
3. square-side / golden-side を substructure に分割する。
4. `(M,N)` 自体を座標 structure として保持する。
5. `normal` を provenance として保持する設計と、必要 invariant だけに縮約する設計を比較する。

評価軸は、field 数の少なさだけではない。downstream proof の短さ、依存方向の明瞭さ、rewrite の安定性、projection の使いやすさ、元 normal form への provenance preservation、将来の field 追加に対する保守性まで見るべきである。

この観点では、現行 design は論理的最小性よりも proof phase boundary と downstream 利便性を優先した設計と評価できる。

## 次に読むべき定理

Lean source で本 structure の直後にある theorem は

```lean
theorem exists_branchB_squareGoldenNormalForm
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    ∃ a b : ℕ, BranchBSquareGoldenNormalForm x y z a b := by
  ...
```

である。

ここで初めて、本 0104 で宣言した packet が空の interface ではなく、任意の Branch-B candidate から実際に構成できることが証明される。

その proof は

1. `exists_branchB_fifthPowerNormalForm` から `a,b,hNF` を得る。
2. 0099 により `golden_eq` を作る。
3. 0102 と $z-y=a^5$ から `tenth_boundary` を作る。
4. 0103 から `square_discriminant` を得る。
5. 0097 と `golden_eq` から `discriminant_five_eq` を作る。
6. 最後に structure を constructor する。

という、0104 の各 field がどこから来るかを完全に可視化した theorem である。

したがって次号 0105 は `exists_branchB_squareGoldenNormalForm` を読むのが依存順として自然である。

## 根拠と注記

形式的根拠は `docs/flt5-theorem-museum` ブランチ上の generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` に含まれる `DkMath/FLT/Five/SquareGoldenNormalForm.lean` 区間である。現在の source では 0103 相当の `squareGolden_square_discriminant` の直後に本 structure があり、その直後に `exists_branchB_squareGoldenNormalForm` が続く。

また、現在の field 名は `discriminant_five_eq` である。過去の説明に別表記があった場合でも、本記事では対象 branch の現行 Lean source を優先する。

既存日本語・英語 PDF の本宣言に対する具体的なページ・節対応は本回では確定できなかった。GitHub code search は upstream error となったため、PDF 上の位置を推測で補っていない。

standalone artifact は generated file であり、split source 名として `DkMath/FLT/Five/SquareGoldenNormalForm.lean` を記録している。本記事では対象 branch から取得した現在の standalone 内容を一次的な形式根拠としている。