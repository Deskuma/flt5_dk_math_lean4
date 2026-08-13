# 0122 — `goldenNeg`

## Lean の型

```lean
def goldenNeg (x : GoldenInt) : GoldenInt := ⟨-x.fst, -x.snd⟩
```

`goldenNeg` は 0118 で導入した `GoldenInt` の二つの整数座標をそれぞれ符号反転する単項演算である。

`GoldenInt` を

$$
x=a+b\varphi
$$

と読むと、

$$
goldenNeg(x)=(-a)+(-b)\varphi
$$

に対応する。

## 数学的主張

この宣言は theorem ではなく定義であり、黄金整数座標系における加法逆元候補を

$$
-(a,b)=(-a,-b)
$$

として与える。

この段階ではまだ標準の `Neg GoldenInt` instance は導入されていない。後続で

```lean
instance : Neg GoldenInt := ⟨goldenNeg⟩
```

と登録され、標準記法 `-x` が `goldenNeg x` に接続される。

## 証明全体での役割

0121 `goldenAdd` が加法を定めたのに対し、0122 `goldenNeg` はその加法に対する逆元演算を固定する。

直後の

```lean
def goldenSub (x y : GoldenInt) : GoldenInt := goldenAdd x (goldenNeg y)
```

は本定義を直接再利用するため、減法の意味は

$$
x-y=x+(-y)
$$

という通常の環構造そのものになる。

さらに後続の `AddCommGroup GoldenInt` 構築では、各座標が整数の加法群であることへ還元することで逆元則が証明される。したがって `goldenNeg` は `GoldenInt` を単なる座標集合から加法群へ育てる primitive operation の一つである。

FLT5 の five-adic 分岐や黄金ノルムを直接扱わないが、後続の可換環、共役、整除、Euclidean-domain 構造、単元分類、五乗因子抽出はすべてこの加法群構造の上に構築される。

## 直接依存する定義・補題

直接依存は小さい。

- `GoldenInt` — 入力と出力の型。
- `GoldenInt.fst`, `GoldenInt.snd` — 二つの整数座標への projection。
- 整数の単項負号 `Int` の `-`。
- `GoldenInt` constructor — `⟨..., ...⟩` による結果の構築。

直接には theorem、five-adic lemma、golden norm lemma へ依存しない。

主要な直接利用先は `goldenSub`、`Neg GoldenInt` instance、`AddCommGroup GoldenInt`、および負号の座標 simp theorem である。

## 証明・構築の流れ

proof script は存在しない。定義本体がそのまま計算規則である。

1. `x.fst` を整数として符号反転する。
2. `x.snd` を整数として符号反転する。
3. 二つの結果を `GoldenInt` constructor に渡す。

したがって

```lean
goldenNeg x
```

を unfolding すると

```lean
⟨-x.fst, -x.snd⟩
```

へ定義簡約される。

後続の `Neg GoldenInt` instance 導入後には、座標 projection に関する補題は本質的に `rfl` で閉じられる設計である。

## Lean 固有の処理

### structure projection

`x.fst` / `x.snd` を直接取り出して整数上で演算するため、quotient や coercion を介さない。

### 期待型による constructor 推論

返り値型が `GoldenInt` と決まっているため、

```lean
⟨-x.fst, -x.snd⟩
```

は `GoldenInt.mk (-x.fst) (-x.snd)` と elaboration される。

### overloaded negation

`-x.fst` と `-x.snd` は `ℤ` 上の負号として解釈される。`GoldenInt` 自身の `Neg` instance はまだ不要であるため、定義循環は起こらない。

### definitional equality

`goldenNeg` は definition なので、unfolding 後の座標計算は definitional equality で扱える。後続の simp API を軽量に保つ重要な性質である。

### raw operation と typeclass operation の分離

先に explicit な `goldenNeg` を定義し、その後で `Neg GoldenInt` に登録する二層構造になっている。この設計は 0119 `goldenZero`、0120 `goldenOne`、0121 `goldenAdd` と同じ規則である。

## 冗長・重複箇所

定義本体に内部的な冗長性はない。

設計上は後続の

```lean
instance : Neg GoldenInt := ⟨goldenNeg⟩
```

によって raw API `goldenNeg x` と標準記法 `-x` が同じ演算を二つの入口から参照することになる。

これは論理的な重複ではなく、座標演算を監査しやすい explicit layer と Mathlib の typeclass layer を分離する意図的な重複と読める。

また `goldenSub` が `goldenAdd x (goldenNeg y)` と定義されるため、減法座標をもう一度

```lean
⟨x.fst - y.fst, x.snd - y.snd⟩
```

と展開しない点は、重複回避として良い設計である。

## 最適化候補

### 1. `Neg` instance へ直接 inline する

```lean
instance : Neg GoldenInt :=
  ⟨fun x => ⟨-x.fst, -x.snd⟩⟩
```

とすれば宣言数は減る。しかし `goldenSub` など raw operation を typeclass 登録より前に明示利用する構造が失われ、primitive coordinate API の監査性が下がる。

### 2. `goldenSub` を直接座標定義する

減法を

```lean
⟨x.fst - y.fst, x.snd - y.snd⟩
```

と直接定義することもできるが、`x-y=x+(-y)` という algebraic dependency が source から見えにくくなる。現行の合成定義の方が構造的には自然である。

### 3. coordinatewise unary helper を導入する

```lean
def goldenMapCoords (f : ℤ → ℤ) (x : GoldenInt) : GoldenInt :=
  ⟨f x.fst, f x.snd⟩
```

のような helper で negation を表せる。ただし現状では一行定義の方が明瞭で、抽象化の費用に見合わない可能性が高い。

### 4. additive structure をまとめて構築する

`Zero`、`Add`、`Neg` を個別 raw 定義にせず `AddCommGroup GoldenInt` を一括構築する設計も可能である。しかし現行設計は各 primitive operation の計算規則が `rfl` で追跡でき、教育性・監査性に優れる。

## 必要 Mathlib import と import 最適化候補

standalone source は冒頭で

```lean
import Mathlib
```

を一括 import している。

`goldenNeg` 単独が直接必要とするのは `GoldenInt` と整数の negation だけであり、`ring`、`omega`、`norm_num`、Euclidean-domain API、number field API は使わない。

したがって本宣言単独では `Mathlib` 全体は過大であり、整数型と基本代数演算を提供する小さな import で足りるはずである。

ただし `GoldenOrder.lean` module 全体では後続の `AddCommGroup`、`CommRing`、`Zsqrtd 5`、domain 構造、各種 tactic が必要になる。正確な最小 import 集合は Lean build を行っていないため未検証であり、ここでは最適化候補としてのみ述べる。

## Comparator challenge 化の可否

**適する。** 難しい証明探索ではなく、同じ意味を保った API 設計比較に向く。

比較候補は次の通り。

- raw `goldenNeg` を先に定義して後から `Neg` instance に登録する現行方式。
- `Neg GoldenInt` を直接定義する方式。
- coordinatewise unary helper を経由する方式。
- `AddCommGroup GoldenInt` を一括構築する方式。

評価軸は、定義簡約の透明性、`rfl` simp lemma の作りやすさ、依存順の明瞭さ、typeclass elaboration への依存度、後続の `goldenSub` の読みやすさである。

## 根拠と推測

形式的根拠は `docs/flt5-theorem-museum` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `GoldenOrder.lean` generated section である。

既存の日本語・英語 PDF は補助資料として位置づけられているが、本記事では `goldenNeg` に対応する具体的ページ・節番号を直接照合していない。そのため PDF 固有の説明やページ番号は推測で補っていない。

import 最小化案と helper 抽象化案は設計上の候補であり、Lean build による検証は行っていない。

## 次に読むべき宣言

次は

```lean
def goldenSub (x y : GoldenInt) : GoldenInt := goldenAdd x (goldenNeg y)
```

である。

0121 の加法と 0122 の加法逆元を合成し、黄金整数上の減法を

$$
x-y=x+(-y)
$$

として定義する。依存順では 0123 `goldenSub` が自然な次号となる。
