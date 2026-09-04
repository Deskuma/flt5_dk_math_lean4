# 0156 — `golden_add_eq`

## Lean の型

```lean
@[simp] theorem golden_add_eq (x y : GoldenInt) :
    goldenAdd x y = x + y := rfl
```

これは `theorem` であり、raw operation `goldenAdd` と、`Add GoldenInt` instance を通した標準記法 `x + y` が定義的に同一であることを公開する `@[simp]` 補題である。

## 数学的主張・宣言の意味

`GoldenInt` を

$$
x=a+b\varphi,\qquad y=c+d\varphi
$$

と読むと、上流の `goldenAdd` は座標加法

$$
goldenAdd(x,y)=(a+c)+(b+d)\varphi
$$

を実装する。一方、標準記法 `x + y` も 0129 で登録された

```lean
instance : Add GoldenInt := ⟨goldenAdd⟩
```

を経由して同じ関数を参照する。

したがって本 theorem は新しい代数恒等式を証明するのではなく、

$$
\texttt{goldenAdd x y}=x+y
$$

という raw API と standard algebra API の一致を、再利用可能な rewrite rule として名前付きで公開する。

## 証明全体での役割

0155 までで `GoldenInt` は `CommRing`、`NoZeroDivisors`、`Nontrivial`、`IsDomain` を備え、Mathlib の標準環論 hierarchy に入った。0156 からは、その抽象 API と初期の明示的座標 API の間を整える段階へ移る。

この bridge は、後続コードが `goldenAdd` を使って書かれていても、simp によって標準記法 `+` へ正規化できることを意味する。逆に、初期の構築で raw operation を使った理由を保ちながら、以後の一般 algebra theorem では標準 notation を使える。

source では本 theorem の直後に `golden_neg_eq`、`golden_sub_eq`、`golden_mul_eq`、`golden_pow_eq` が並ぶ。つまり 0156 は raw operation equivalence 群の先頭であり、加法から始めて否定・減算・乗法・冪まで同じ API 境界を順に閉じる。 

## 直接依存する定義・補題

直接依存する主要要素は次の通りである。

- `GoldenInt`
- `goldenAdd`
- `instance : Add GoldenInt := ⟨goldenAdd⟩`
- Lean 標準の `Add` notation
- `rfl`

数学的には座標加法そのものに依存するが、本 theorem の proof term は `rfl` だけである。これは `x + y` の実体が definitionally `goldenAdd x y` であるためで、加法の結合律や可換律などの theorem は直接必要としない。

## 証明・構築の流れ

証明は一段で終わる。

```lean
@[simp] theorem golden_add_eq (x y : GoldenInt) :
    goldenAdd x y = x + y := rfl
```

Lean は右辺 `x + y` を `Add GoldenInt` instance から展開し、その operation が `goldenAdd` であることを知る。よって左辺と右辺は定義的に同じ式になり、反射律 `rfl` で閉じる。

概念的には

$$
\text{raw function}
\longleftrightarrow
\text{typeclass notation}
$$

の同一性を theorem 名として固定している。

## Lean 固有の処理

重要なのは `@[simp]` と definitional equality の組み合わせである。

`rfl` だけで証明できる事実なら theorem を置かずとも `dsimp` や unfolding で処理できる。しかし `@[simp]` theorem として登録すると、simp engine は raw form

```lean
goldenAdd x y
```

を標準形

```lean
x + y
```

へ明示的に正規化できる。

rewrite の向きが raw → standard になっていることも重要である。これは後続の algebraic simplification を Mathlib 標準 notation 側へ寄せ、専用 API を局所的な実装詳細として扱いやすくする。

## 冗長・重複箇所

定義的等価性だけを見ると、本 theorem は情報を追加していないため冗長に見える。

```lean
goldenAdd x y = x + y
```

は instance 展開だけで成立するからである。

ただし API 設計としては役割がある。

- raw operation の名前を残したまま標準 notation へ橋渡しできる。
- `simp` の正規化方向を明示できる。
- downstream proof が instance の内部実装を直接 unfold する必要を減らせる。
- 将来 `Add` instance の実装方法を変更した場合、bridge theorem が互換層として働く余地がある。

したがって「数学的には冗長、API としては有用」という性格の宣言である。

## 最適化候補

候補は次の通りである。

1. 現行の `@[simp] theorem ... := rfl` を維持する。
2. theorem を削除し、必要箇所で instance を unfold する。
3. raw operation 群を非公開化し、以後すべて標準 notation のみを使う。
4. `golden_add_eq` から `golden_pow_eq` までを API bridge section として明示的にまとめる。

本 formalization は explicit coordinate layer を監査可能な形で残す設計なので、1 または 4 が自然である。数行の削減より、raw layer と algebra layer の境界が読める価値の方が大きい。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 単独で高度な Mathlib lemma は使わず、必要なのは `GoldenInt`、`goldenAdd`、`Add GoldenInt` instance、`@[simp]` 属性と標準 equality machinery である。

したがって 0156 のためだけに `Mathlib` 全体が必要とは考えにくい。ただし実際の module は `GoldenOrder` 全体として `ring`、`omega`、`norm_num`、`Zsqrtd`、algebra typeclass hierarchy などを使用するため、最小 import は module 全体の依存で決まる。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、ここは import 最適化候補としての推測である。

## Comparator challenge 化の可否

適している。比較対象は数学アルゴリズムではなく API normalization strategy になる。

比較候補は、

- `@[simp]` bridge theorem を置く現行方式
- raw operation を毎回 unfold する方式
- raw operation を非公開化して標準 notation のみ使う方式

である。

比較軸は、simp の安定性、proof script の短さ、定義変更への耐性、error message の読みやすさ、raw coordinate layer の監査可能性、downstream theorem の notation 一貫性となる。

特に `rfl` で証明できる bridge theorem をあえて残す価値を測る、小さく明瞭な Comparator challenge になる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `GoldenOrder` generated section である。source 上では 0155 `IsDomain GoldenInt` の直後に本 `golden_add_eq` が置かれ、その後に raw operation equivalence 群が連続している。

standalone artifact は generated source の ordered modules に `DkMath/FLT/Five/GoldenOrder.lean` を含み、全体として `import Mathlib` を使用している。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的 PDF ページ・節は今回直接特定していないため、推測しない。

## 次に読むべき宣言

依存順の次は

```lean
@[simp] theorem golden_neg_eq (x : GoldenInt) :
    goldenNeg x = -x := rfl
```

である。

0156 が raw 加法と標準加法を接続したのに対し、次の 0157 は raw negation `goldenNeg` と標準 unary minus `-x` の定義的一致を同じ方針で公開する。