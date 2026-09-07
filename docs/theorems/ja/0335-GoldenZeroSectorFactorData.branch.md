# 0335 — `GoldenZeroSectorFactorData.branch`

## 宣言種別

この宣言は theorem ではなく **`def`** である。

`GoldenZeroSectorFactorData p` が保持する重い証明データから、対応する軽量な branch label `GoldenZeroSectorFactorBranch` だけを取り出す射影関数を定義する。

```lean
/-- Branch label of an exact factor datum. -/
def GoldenZeroSectorFactorData.branch
    {p : GoldenZeroSectorInversionPacket} :
    GoldenZeroSectorFactorData p → GoldenZeroSectorFactorBranch
  | .odd .. => .odd
  | .evenLeftLow .. => .evenLeftLow
  | .evenRightLow .. => .evenRightLow
```

## Lean の型

宣言の型は

```lean
GoldenZeroSectorFactorData.branch :
  {p : GoldenZeroSectorInversionPacket} →
  GoldenZeroSectorFactorData p → GoldenZeroSectorFactorBranch
```

である。

暗黙引数

```lean
{p : GoldenZeroSectorInversionPacket}
```

を固定すると、

```lean
GoldenZeroSectorFactorData p → GoldenZeroSectorFactorBranch
```

という通常の関数になる。

入力側 `GoldenZeroSectorFactorData p` は 0334 で定義された dependent inductive であり、各 constructor は第五冪因子 $e,f$、正性、互いに素性、奇偶性、$A_0,B_0$ の分解、`zeroSectorQ` の ownership、branch 固有の差分方程式を保持する。一方、出力側 `GoldenZeroSectorFactorBranch` は 0333 の三値列挙型で、

```lean
.odd
.evenLeftLow
.evenRightLow
```

の branch 名だけを保持する。

したがってこの `def` は「証明 certificate 全体」から「どの二進 branch に属するか」というタグだけを抽出する忘却写像である。

## 数学的意味

数学的に新しい命題を証明する宣言ではない。

零セクター反転後の factorization は三つの場合に分類される。

1. odd branch

$$
A_0 = 2e^5,
\qquad
B_0 = 2f^5.
$$

2. even-left-low branch

$$
A_0 = 8e^5,
\qquad
B_0 = 16f^5.
$$

3. even-right-low branch

$$
A_0 = 16e^5,
\qquad
B_0 = 8f^5.
$$

`GoldenZeroSectorFactorData p` はこれらを証明付きで保持するが、後続 theorem の中には因子化の全情報ではなく、「現在どの branch か」だけを仮定として受け取りたいものがある。

`branch` は、その用途のために

$$
\text{exact factor certificate}
\longmapsto
\text{branch label}
$$

という情報圧縮を行う。

## 証明全体での役割

この関数の直後には

```lean
theorem GoldenZeroSectorFactorData.odd_eleven_channel
    {p : GoldenZeroSectorInversionPacket}
    (data : GoldenZeroSectorFactorData p)
    (hbranch : data.branch = .odd) :
    ...
```

が置かれている。

ここで `odd_eleven_channel` は `data` 自体を受け取る一方、追加条件として

```lean
hbranch : data.branch = .odd
```

を要求する。

この設計により、呼び出し側は dependent inductive の constructor を直接露出させず、公開された branch label の等式として場合を指定できる。

証明内部では `cases data` により三 constructor を展開し、odd constructor では実際の $e,f$ と差分方程式を利用し、even constructor では `hbranch` が不可能な等式となるため排除する。

したがって `branch` は、

- 内部表現: 証明データを持つ dependent inductive
- 外部インターフェース: 三値の branch label

を分離する小さな API 境界として働く。

## 直接依存する定義・宣言

### `GoldenZeroSectorInversionPacket`

暗黙 index `p` の型である。

今回の関数本体では `p` の field を直接参照しないが、入力型

```lean
GoldenZeroSectorFactorData p
```

を形成するために必要である。

### `GoldenZeroSectorFactorData`

0334 の dependent inductive。

三 constructor

```lean
.odd
.evenLeftLow
.evenRightLow
```

を pattern match する。

### `GoldenZeroSectorFactorBranch`

0333 の branch label 型。

入力 constructor と同名の出力 constructor

```lean
.odd
.evenLeftLow
.evenRightLow
```

へ写す。

直接依存する theorem や算術補題はない。

## 構築の流れ

この `def` は三行の pattern matching だけで完成している。

### 1. odd constructor

```lean
| .odd .. => .odd
```

`GoldenZeroSectorFactorData.odd` が持つ $e,f$ や多数の proof field を `..` ですべて捨て、branch label `.odd` を返す。

### 2. even-left-low constructor

```lean
| .evenLeftLow .. => .evenLeftLow
```

同様に certificate の内容を捨て、`.evenLeftLow` を返す。

### 3. even-right-low constructor

```lean
| .evenRightLow .. => .evenRightLow
```

`.evenRightLow` を返す。

これで `GoldenZeroSectorFactorData` の constructor と `GoldenZeroSectorFactorBranch` の constructor の対応が全域で定義される。

## Lean 固有の処理

### dependent inductive を通常の label へ落とす

入力型は `p` に依存する

```lean
GoldenZeroSectorFactorData p
```

だが、出力型

```lean
GoldenZeroSectorFactorBranch
```

は `p` に依存しない。

したがってこの関数は dependent data から非依存な分類情報を取り出している。

### `..` pattern

各 constructor は多数の引数を持つが、branch 判定には一つも必要ない。

```lean
.odd ..
```

という pattern により、それらの field を個別に命名せず無視している。これはこの `def` の意図を非常に明瞭にする Lean の記法である。

### constructor 名の文脈解決

左辺の `.odd` は `GoldenZeroSectorFactorData.odd`、右辺の `.odd` は `GoldenZeroSectorFactorBranch.odd` と、期待される型から Lean が解決する。

同名 constructor を使っているため、写像が視覚的にも一対一であることが分かる。

## 冗長・重複箇所

実装上の冗長性はほぼない。

三 constructor を三 constructor へ写すため、pattern match の三行は必要である。

ただし設計レベルでは `GoldenZeroSectorFactorData` と `GoldenZeroSectorFactorBranch` が同じ三 branch 名を二重に持っている。この重複は意図的と考えられる。前者は proof-carrying data、後者は軽量な公開 label であり、役割が異なるからである。

もし branch label を独立型として必要としない設計なら `GoldenZeroSectorFactorData` を直接 `cases` すれば済むが、直後の `odd_eleven_channel` の API から見ると、独立 label は明確な用途を持っている。

## 最適化候補

### 現行実装

現行の pattern match はすでに最小級であり、コード量・実行時意味ともにほぼ最適である。

### `@[simp]` の付与

候補としては

```lean
@[simp] def GoldenZeroSectorFactorData.branch ...
```

または constructor ごとの simp lemma を用意する方法がある。

後続では実際に

```lean
simp [GoldenZeroSectorFactorData.branch] at hbranch
```

として even branch の不可能性を処理しているため、`@[simp]` 化すればこの呼び出しをさらに短くできる可能性がある。

ただし `@[simp]` 属性を公開 API に付けるかはライブラリ全体の rewrite 方針に関わるため、ここでは最適化候補に留める。Lean ビルドを行っていないので影響範囲は未検証である。

### branch label と certificate の統合

型設計を大きく変えるなら label-indexed family

```lean
GoldenZeroSectorFactorData : GoldenZeroSectorFactorBranch → ...
```

のような設計も考えられる。しかしこれは後続 API と constructor 設計を大幅に変更し、現在の単純な existential/certificate 運用より複雑になる可能性が高い。現行設計の方が実用上は軽い。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

ただし、この `def` の本体そのものは pattern matching と既存の三つの型しか利用せず、新たな Mathlib theorem・tactic・算術 API を一切使用していない。

したがって、この宣言単体の追加 Mathlib 依存は事実上ない。必要なのは前段の

```lean
GoldenZeroSectorInversionPacket
GoldenZeroSectorFactorData
GoldenZeroSectorFactorBranch
```

が利用可能であることだけである。

source module 単位で `import Mathlib` をどこまで縮小できるかは、同じ `SignedGoldenZeroSectorFactorization.lean` 内の他宣言が `Nat.Coprime`、`Odd`、`Even`、`omega`、`norm_num`、`ring` などを広く利用しているため、この一宣言だけからは確定できない。最小 import 集合は未検証である。

## Comparator challenge 化の可否

**可能。難度は低い。**

課題としては、0333 と 0334 の型を与えたうえで

```lean
def GoldenZeroSectorFactorData.branch ...
```

を実装させる形式が適している。

判定ポイントは明快で、三 constructor が対応する三 label に正しく写るかだけである。

一方、数論的内容そのものを問う challenge には向かない。この `def` は数学的推論ではなく、proof-carrying inductive からタグを抽出する Lean のデータ設計・pattern matching の理解を測る問題である。

## 次に読むべき宣言

次は

```lean
theorem GoldenZeroSectorFactorData.odd_eleven_channel
```

を読むべきである。

この theorem は今回の

```lean
data.branch = .odd
```

という軽量 label 条件を実際に利用し、odd branch の factor data から

$$
11 \mid d,
$$

さらに

$$
11 \nmid c,
\qquad
11 \nmid e,
\qquad
11 \nmid f,
\qquad
11 \nmid ef
$$

をまとめて抽出する。

0331 `fifth_mod_eleven_cases`、0332 `eleven_dvd_d_of_fifth_add_four_fifth` で準備した mod $11$ channel が、0334 の exact factor certificate と今回の branch API を経由して、ここで初めて branch-specific packet 情報として表面化する。