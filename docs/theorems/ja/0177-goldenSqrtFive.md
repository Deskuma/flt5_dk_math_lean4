# 0177 — `goldenSqrtFive`

## Lean の型

```lean
/-- The ramified square root `2*phi - 1` of five. -/
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩
```

これは `theorem` ではなく `def` であり、黄金整数環 `GoldenInt` の具体的な元

$$
-1+2\varphi
$$

を `goldenSqrtFive` という名前で定義する。

## 数学的主張または宣言の意味

黄金整数の基底元は

$$
\varphi=\frac{1+\sqrt5}{2}
$$

と読むので、

$$
2\varphi-1=\sqrt5
$$

である。`GoldenInt` の座標表示では `⟨a,b⟩` が $a+b\varphi$ を表すため、

$$
\sqrt5=-1+2\varphi
$$

に対応する座標は

$$
(-1,2)
$$

となる。したがって

```lean
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩
```

は、二次環内部にある「5 の平方根」に対応する ramified element を明示的に固定している。

重要なのは、この定義そのものは `goldenPhi` を式として参照していない点である。数学的意味は $2\varphi-1$ だが、Lean 実装では既に還元済みの整数座標 `⟨-1,2⟩` を直接採用している。

## 証明全体での役割

0176 `golden_mul_conj` までで、黄金整数における共役とノルムの基本関係

$$
x\overline{x}=N(x)
$$

が整備された。本定義からは、素数 `5` の ramification を担う具体的な元へ進む。

source では本定義の後に `goldenTau := ⟨2,1⟩`、短縮 alias、さらに

```lean
theorem goldenSqrtFive_sq :
    goldenMul goldenSqrtFive goldenSqrtFive = goldenOfInt 5 := by
  decide

theorem goldenNorm_sqrtFive : goldenNorm goldenSqrtFive = -5 := by
  norm_num [goldenNorm, goldenSqrtFive]
```

が続く。したがって `goldenSqrtFive` は後続で

$$
(\sqrt5)^2=5,
\qquad
N(\sqrt5)=-5
$$

を形式化するための基準元である。

さらに

```lean
theorem goldenTau_eq_phi_mul_sqrtFive :
    goldenTau = goldenMul goldenPhi goldenSqrtFive := by
  decide
```

により、distinguished norm-five element `goldenTau` とも直接結び付く。FLT5 の五進的 exceptional factor を黄金整数環側で扱う際の、ramified prime above five の具体的な座標代表とみなせる。

## 直接依存する定義・補題

この `def` が syntactic に直接依存するものは少ない。

- `GoldenInt`
- `GoldenInt` の `fst` / `snd` 座標型が `ℤ` であること
- 整数 literal `-1`, `2`

数学的な意味付けとしては、上流の

- 0161 `goldenPhi`
- 0163 `goldenConj`
- 0164 `goldenNorm`

と密接に関係するが、定義本体ではそれらを呼び出していない。

また 0165 `golden_phi_sq` の

$$
\varphi^2=\varphi+1
$$

から $(2\varphi-1)^2=5$ を導けるが、本定義そのものには theorem-level dependency はない。

## 証明または構築の流れ

proof script は存在しない。

```lean
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩
```

という structure literal だけで構築される。

概念的には、

1. $\sqrt5=2\varphi-1$ とみなす。
2. $a+b\varphi$ の係数を読む。
3. $a=-1$, $b=2$ を `GoldenInt` の二座標へ格納する。

という変換である。

## Lean 固有の処理

`⟨-1, 2⟩` は期待型 `GoldenInt` から structure constructor を推論する。座標型が `ℤ` なので、`-1` と `2` も整数として elaboration される。

ここで algebraic expression

```lean
2 * goldenPhi - 1
```

のような標準記法を使わず座標 literal を直接置いているため、後続の closed theorem は定義展開によって具体的な整数座標計算へ落ちる。実際 `goldenSqrtFive_sq` が `by decide` で閉じるのは、この representation の計算透明性によるところが大きい。

一方、この宣言自体には `@[simp]` は付いていない。`goldenSqrtFive` は正規化 rule ではなく、後続算術で明示的に使う named element だからである。

## 冗長・重複箇所

直後の source には

```lean
abbrev sqrtFiveElement : GoldenInt := goldenSqrtFive
```

という短い public alias が置かれる。そのため `goldenSqrtFive` と `sqrtFiveElement` は値として完全に同一で、API-level の重複がある。

ただし役割は区別できる。

- `goldenSqrtFive`: GoldenOrder 固有の明示座標名
- `sqrtFiveElement`: downstream で使いやすい短い public name

また数学的には `goldenSqrtFive = 2 * goldenPhi - 1` なので、座標 literal と algebraic expression の二つの表現候補が存在する。現行 source は座標透明性を優先して前者を採用している。

## 最適化候補

1. 現行の `⟨-1,2⟩` を維持し、closed computation の単純さを優先する。
2. `goldenSqrtFive` を `2 * goldenPhi - 1` から定義し、数学的由来を定義式へ直接埋め込む。
3. 現行定義を維持しつつ、別 theorem

```lean
goldenSqrtFive = 2 * goldenPhi - 1
```

を標準 notation で追加して、数学的意味と計算表現を分離する。
4. `sqrtFiveElement` alias の downstream 使用状況を調べ、不要なら API 名を一本化する。
5. 一般の二次環における discriminant element / ramified element として抽象化し、`5` 固有の座標 literal を特殊化として扱う。

局所的には一行定義なので、最適化対象は proof 長ではなく API naming と抽象化レベルである。

## 必要 Mathlib import と import 最適化候補

本 `def` 単独で必要なのは `GoldenInt` と整数 literal を扱える基本環境だけであり、高度な Mathlib theorem や tactic は直接使用しない。

standalone artifact は `import Mathlib` を使用しているが、本宣言だけを考えれば明らかに広い。もっとも `GoldenOrder` module 全体では `Zsqrtd`、`ring`、`omega`、`norm_num`、`interval_cases`、各種 algebra typeclass を利用するため、実際の import 最適化は module 単位で評価すべきである。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、具体的な削減先は候補としてのみ扱う。

## Comparator challenge 化の可否

適している。

比較候補は、

- explicit coordinate 定義 `⟨-1,2⟩`
- algebraic 定義 `2 * goldenPhi - 1`
- generic quadratic-order / `AdjoinRoot` 上の discriminant element からの構成

である。

比較軸は、

- `goldenSqrtFive_sq` がどれだけ簡単に証明できるか
- definitional transparency
- 数学的由来の読みやすさ
- simp / norm_num / decide との相性
- downstream ramification theorem の proof burden
- 一般化可能性

である。

特に「座標を先に固定して計算を軽くする」設計と「数学式を定義へ直接書いて意味を明瞭にする」設計の差が小さな例で明確に観察できる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `GoldenOrder` generated source である。source 上では 0176 `golden_mul_conj` の直後に本定義があり、その次に `goldenTau` が続く。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、本定義に対応する具体的 PDF ページ・節番号は直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は

```lean
/-- The distinguished ramifier `2 + phi`. -/
def goldenTau : GoldenInt := ⟨2, 1⟩
```

である。

0177 で $2\varphi-1=\sqrt5$ に対応する ramified square-root element を固定した。次は norm-five ramifier として実際に downstream factor extraction に使われる

$$
\tau=2+\varphi
$$

を導入し、その後 `sqrtFiveElement` / `tau` の public alias、平方・ノルム・`\varphi\sqrt5` との関係へ進む。