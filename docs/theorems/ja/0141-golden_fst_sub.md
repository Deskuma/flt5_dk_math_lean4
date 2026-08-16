# 0141 — `golden_fst_sub`

## Lean の型

```lean
@[simp] theorem golden_fst_sub (x y : GoldenInt) :
    (x - y).fst = x.fst - y.fst := rfl
```

これは `theorem` であり、`@[simp]` 属性を持つ減算の第一座標射影補題である。

## 数学的主張・宣言の意味

`GoldenInt` を整数対 `⟨a,b⟩` による黄金整数

$$
a+b\varphi
$$

として読む。二つの黄金整数を

$$
x=a+b\varphi,\qquad y=c+d\varphi
$$

とすると、減算は

$$
x-y=(a-c)+(b-d)\varphi
$$

である。本定理はその第一座標について

$$
\operatorname{fst}(x-y)=\operatorname{fst}(x)-\operatorname{fst}(y)
$$

を述べる。

上流の raw operation は

```lean
def goldenSub (x y : GoldenInt) : GoldenInt :=
  goldenAdd x (goldenNeg y)
```

と、加法と否定から構築されている。さらに

```lean
instance : Sub GoldenInt := ⟨goldenSub⟩
```

によって標準記法 `x - y` に接続されている。本定理は、その標準減算の第一座標を整数の通常の減算へ正規化する public simp API である。

## 証明全体での役割

0140 までで `GoldenInt` の零元・単位元・加法・否定に対する座標 projection API が整備された。本定理から subtraction projection の組に入り、まず第一座標を扱う。

この補題は、後続の

```lean
instance goldenAddCommGroup : AddCommGroup GoldenInt := by
  ...
  intros <;> ext <;> simp [add_comm, add_left_comm]
```

のような証明スタイルを支える。`GoldenInt.ext` により黄金整数の等式を `fst` と `snd` の二つの整数等式へ分解したあと、`simp` が `(x - y).fst` を `x.fst - y.fst` へ落とせるため、減算を含む式を黄金整数専用の計算から整数算術へ移せる。

FLT5 本体の第五冪因数分解を直接述べる定理ではないが、黄金整数を明示座標から Mathlib の標準加法群・可換環へ持ち上げる infrastructure theorem であり、後段のノルム、整除、単元、Euclidean-domain 構造に必要な algebra interface を安定させる役割を持つ。

## 直接依存する定義・補題

直接依存するのは次である。

- `GoldenInt`
- `goldenSub`
- `instance : Sub GoldenInt := ⟨goldenSub⟩`
- `GoldenInt.fst`
- 整数の標準減算

`goldenSub` の内部では `goldenAdd` と `goldenNeg` に依存するため、概念的な依存関係は

$$
\texttt{goldenAdd},\ \texttt{goldenNeg}
\longrightarrow
\texttt{goldenSub}
\longrightarrow
\texttt{Sub GoldenInt}
\longrightarrow
\texttt{golden\_fst\_sub}
$$

となる。

直前の 0139 `golden_fst_neg` と 0140 `golden_snd_neg` は subtraction の内部構築を理解する上では関連するが、本定理の証明はそれらを theorem として呼び出さず、定義的等価性だけで閉じる。

## 証明・構築の流れ

証明は `rfl` 一語である。

1. `x - y` は `Sub GoldenInt` instance により `goldenSub x y` へ展開される。
2. `goldenSub x y` は `goldenAdd x (goldenNeg y)` である。
3. その第一座標は `x.fst + (-y.fst)` へ定義展開される。
4. `Int` 上の `x.fst - y.fst` も標準減算の定義により同じ項へ還元される。
5. 両辺が同一の Lean term となるため `rfl` が成立する。

したがって、ここでは `rw`、`simp`、`ring` などを証明本体に使っていない。減算 API の定義順そのものが proof term になっている。

## Lean 固有の処理

`rfl` で閉じることは、単に数学的に自明というだけでなく、標準記法 `x - y`、`Sub GoldenInt` instance、`goldenSub`、`goldenAdd`、`goldenNeg`、整数減算の定義が互いに整合し、reduction 後に左右が definitionally equal であることを示す。

`@[simp]` により simplifier は

```lean
(x - y : GoldenInt).fst
```

を

```lean
x.fst - y.fst
```

へ自動的に変換する。

この dedicated projection theorem を置くことで、利用側は `goldenSub`、`goldenAdd`、`goldenNeg` を毎回 unfold する必要がない。内部構築は隠したまま、外部 API では標準整数減算を normal form として得られる。

## 冗長・重複箇所

次の 0142 `golden_snd_sub` とは `fst` と `snd` の違いだけでほぼ対称であり、API-level の意図的重複がある。

また `goldenSub` を直接 unfold し、さらに `goldenAdd` と `goldenNeg` を展開すれば同じ結果を得られるため、raw definition と projection theorem の間にも意味上の重なりがある。ただし、個別の `@[simp]` lemma を置くことで内部実装の大規模 unfold を避け、simp normal form を安定させる利点がある。

## 最適化候補

比較候補は主に三つある。

1. 現行どおり `fst` / `snd` の subtraction projection theorem を個別に保持する。
2. `goldenSub`、あるいは `goldenAdd` と `goldenNeg` を simp 展開対象にして projection theorem を削減する。
3. `GoldenInt` を積型や一般 quadratic algebra の既存構造へ寄せ、汎用 subtraction projection API を再利用する。

宣言数だけなら 2 や 3 が短くなる可能性がある。一方、現行方式は `simp` がどの形まで展開するかを局所的に制御でき、proof trace と normal form が読みやすい。FLT5 のように監査可能性を重視する形式化では、この明示的 API は合理的である。

## 必要 Mathlib import と import 最適化候補

standalone source は全体として `import Mathlib` を使用している。本定理単独が直接必要とするのは `GoldenInt`、`Sub` instance、structure projection、`@[simp]`、`rfl`、整数の加法・否定・減算に関する基礎 infrastructure であり、高度な Mathlib theorem は利用しない。

したがって、この補題単独のために `Mathlib` 全体を import する必要はないと考えられる。実際の modular source の最小 import は `GoldenOrder` 上流定義と整数・typeclass infrastructure に支配される。

今回は Lean build を行わないため、具体的な最小 import 集合は未検証である。この部分は import 最適化候補としての推測であり、確定事項ではない。

## Comparator challenge 化の可否

適している。たとえば次の方式を比較できる。

- dedicated `@[simp]` projection theorem を持つ現行方式
- `goldenSub` の unfold に依存する方式
- `x + (-y)` まで展開して加法・否定 projection lemma だけを再利用する方式
- product / quadratic-algebra の汎用 subtraction API を利用する方式

比較軸は、downstream proof 行数、`rfl` で閉じる補題数、simp trace の長さ、unfold 後の term サイズ、内部表現変更への耐性、`ext <;> simp` の自動化率である。

特に、本定理は `goldenSub` を独立 raw operation として残す設計が definitional transparency にどの程度寄与するかを測る小さな Comparator challenge に向いている。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `GoldenOrder.lean` generated section と、直前までの theorem museum 文書である。依存順は

```lean
@[simp] theorem golden_fst_neg (x : GoldenInt) : (-x).fst = -x.fst := rfl
@[simp] theorem golden_snd_neg (x : GoldenInt) : (-x).snd = -x.snd := rfl
@[simp] theorem golden_fst_sub (x y : GoldenInt) :
    (x - y).fst = x.fst - y.fst := rfl
@[simp] theorem golden_snd_sub (x y : GoldenInt) :
    (x - y).snd = x.snd - y.snd := rfl
```

という並びである。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在することを確認した。ただし、本定理のような小さな definitional projection lemma に対応する具体的 PDF ページ・節番号は今回特定していないため、ページ対応は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
@[simp] theorem golden_snd_sub (x y : GoldenInt) :
    (x - y).snd = x.snd - y.snd := rfl
```

である。0141 が subtraction の第一座標を整数減算へ落としたので、次の 0142 で第二座標も揃い、減算に対する完全な二座標 simp API が完成する。