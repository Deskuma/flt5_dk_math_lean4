# 0372 `goldenZeroSectorLift`

## 宣言種別

`def`

## Lean コード

```lean
/--
The quadratic re-entry map used in the golden-order exponent-five descent.  Its
norm is the quartic occurring in the second coordinate of a golden fifth
power, while its second coordinate is a square.
-/
def goldenZeroSectorLift (x : GoldenInt) : GoldenInt :=
  ⟨x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2, x.snd ^ 2⟩
```

## Lean の型

```lean
goldenZeroSectorLift : GoldenInt → GoldenInt
```

入力 `x : GoldenInt` の二座標を

```lean
x.fst : ℤ
x.snd : ℤ
```

とすると、出力は

```lean
⟨x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2,
  x.snd ^ 2⟩
```

である。

数学的に $x=(r,s)$ と書けば、これは二次写像

$$
T(r,s)=\bigl(r^2+rs+s^2,\ s^2\bigr)
$$

を定義している。

## 数学的主張または宣言の意味

これは命題を証明する theorem ではなく、zero-sector descent で繰り返し使用する **再入写像そのものを定義する宣言** である。

第一座標

$$
r^2+rs+s^2
$$

と第二座標

$$
s^2
$$

を組にして、新しい黄金整数を作る。

この形が選ばれている理由は、後続 theorem

```lean
goldenZeroSectorLift_norm
```

で

$$
\operatorname{Norm}(T(r,s))
=
H(r,s)
$$

が成立し、ここで $H(r,s)$ は黄金整数の fifth power の第二座標に現れる quartic factor `goldenFifthSndFactor r s` だからである。

したがってこの写像は、整数座標上の quartic 条件を黄金整数の norm 条件へ戻す **algebraic re-entry** を実装している。

## 証明全体での役割

0371 `goldenUnitClassesModFifth` までで、任意の黄金 unit を fifth powers を法として五つの sector に分類する準備が完成した。

今回の `goldenZeroSectorLift` からは `SignedGoldenZeroSectorDescent.lean` に入り、zero sector を strict descent で排除する段階へ移る。

zero-sector packet の基底座標を $x=(r,s)$ とすると、まず

$$
T(r,s)=\bigl(r^2+rs+s^2,s^2\bigr)
$$

を黄金整数として作る。後続ではこの lift について

$$
\operatorname{Norm}(T(r,s))
=
\texttt{goldenFifthSndFactor}(r,s)
$$

を示し、その norm が fifth power である状況から coprime factorization を通じて

$$
T(r,s)=\gamma^5
$$

という fifth root を回収する。

さらにその $\gamma$ から新しい descent packet を作り、可視 measure を厳密に減少させる。

したがって本定義は、

$$
\text{zero-sector arithmetic}
\longrightarrow
\text{golden norm factorization}
\longrightarrow
\text{new fifth-power root}
\longrightarrow
\text{strict descent}
$$

という後半の再帰回路の入口である。

## 直接依存する定義・補題

### `GoldenInt`

本定義の入出力型である。コードから `fst` と `snd` の二座標を持つことが分かる。

今回の定義では、その constructor syntax

```lean
⟨..., ...⟩
```

を直接用いている。

### 整数上の加算・乗算・冪

座標式

```lean
x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2
x.snd ^ 2
```

を構成するために、`ℤ` 上の `+`, `*`, `^` を使用する。

この `def` 自体は他の FLT5 固有 theorem を呼び出さない。

### 後続で直接使われる関連宣言

本定義を最初に展開するのは

```lean
theorem goldenZeroSectorLift_snd (x : GoldenInt) :
    (goldenZeroSectorLift x).snd = x.snd ^ 2 := rfl
```

であり、続いて

```lean
theorem goldenZeroSectorLift_norm
```

が norm と quartic factor の恒等式を証明する。

これらは依存先ではなく **本定義の最初の利用者** である。

## 構築の流れ

定義本体は一行だが、構造は明確である。

### 1. 第一座標を作る

```lean
x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2
```

数学的には

$$
r^2+rs+s^2.
$$

### 2. 第二座標を平方にする

```lean
x.snd ^ 2
```

数学的には

$$
s^2.
$$

### 3. `GoldenInt` として組み立てる

```lean
⟨..., ...⟩
```

により二つの整数座標から新しい `GoldenInt` を構成する。

証明 tactic は存在せず、完全に計算的な定義である。

## Lean 固有の処理

### projection `fst` / `snd`

`x.fst`, `x.snd` により `GoldenInt` の二座標を直接取り出している。

### anonymous constructor notation

```lean
⟨a, b⟩
```

は期待型 `GoldenInt` から constructor を推論して値を構築する Lean の記法である。

### `^ 2`

自然数指数による冪である。座標型が `ℤ` なので、ここでは整数環上の平方となる。

### definitional equality

直後の

```lean
goldenZeroSectorLift_snd
```

が `rfl` だけで証明できるのは、本定義の第二座標が文字通り `x.snd ^ 2` と定義されているからである。

この点は、後段で rewrite lemma として扱いやすい API を作るうえで重要である。

## 冗長・重複箇所

定義本体には冗長性はほぼない。

ただし数学的には第一座標

$$
r^2+rs+s^2
$$

は黄金整数に固有の二次形式として他所でも現れる可能性がある。もしリポジトリ内に同じ二次形式を表す既存定義が存在するなら、それを再利用することで式の重複を減らせる余地がある。

今回確認した standalone 抜粋だけからは、そのような完全一致する既存 helper の有無までは確定できないため、これは最適化候補に留める。

## 最適化候補

### 1. 座標二次形式の名前付け

第一座標を例えば

```lean
def goldenQuadraticForm (r s : ℤ) : ℤ :=
  r ^ 2 + r * s + s ^ 2
```

のように別定義へ切り出す設計は可能である。

そうすれば

```lean
def goldenZeroSectorLift (x : GoldenInt) : GoldenInt :=
  ⟨goldenQuadraticForm x.fst x.snd, x.snd ^ 2⟩
```

と書ける。

ただし現在は一度しか使わない式なら、現状のインライン定義の方が追跡しやすい。リポジトリ全体で同じ二次形式が何度現れるかを確認してから判断すべきである。

### 2. 構造的 API の整備

直後に `goldenZeroSectorLift_snd` が用意されているため、第一座標についても頻繁に rewrite するなら

```lean
theorem goldenZeroSectorLift_fst ...
```

を設ける選択肢がある。

ただし後続コードが `goldenZeroSectorLift_norm` を通じて第一座標をまとめて扱うなら不要である。

### 3. algebraic map としての抽象化

この写像は加法準同型や乗法準同型ではなく二次写像なので、一般の ring hom として抽象化する対象ではない。

むしろ descent 専用の named transformation として現在の `def` を維持する方が自然である。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

しかし今回の `def` 本体だけを見ると必要なのは、

- `GoldenInt` の定義
- 整数型 `ℤ`
- 基本的な加算・乗算・自然数冪

程度であり、高度な Mathlib tactic は使用しない。

従って `import Mathlib` はこの一宣言だけに対しては明らかに広い。

実際のモジュールでは `GoldenInt` 自体を提供する DkMath 内部 import と、その定義が要求する Mathlib import に依存するはずである。正確な最小 import はモジュール単位の依存グラフと Lean ビルドによる確認が必要だが、本作業では Lean ビルドを行っていないため未確認である。

import 最適化を行うなら、`SignedGoldenZeroSectorDescent.lean` 全体で使用する theorem/tactic を基準に縮小すべきであり、この `def` 単独だけを見て import を決めるべきではない。

## Comparator challenge 化の可否

**可能。ただし単独では very small construction challenge である。**

例えば `GoldenInt` の二座標構造だけを与え、target として

```lean
def goldenZeroSectorLift (x : GoldenInt) : GoldenInt :=
  ?_
```

を置き、指定された数学写像

$$
(r,s)\mapsto(r^2+rs+s^2,s^2)
$$

を Lean 構造体として実装させる challenge にできる。

ただし証明探索はほとんどない。

より良い Comparator challenge は、0372〜0374 をまとめて

1. `goldenZeroSectorLift` を定義する
2. 第二座標式を `rfl` で示す
3. `goldenZeroSectorLift_norm` を `ring` で示す

という小さな API 構築問題にする形である。

これなら structure construction、definitional equality、展開、環恒等式まで一続きに評価できる。

## 技術的意味

この定義は zero-sector descent の幾何学的・代数的な核の一つである。

入力座標 $(r,s)$ から

$$
(r,s)
\longmapsto
\bigl(r^2+rs+s^2,s^2\bigr)
$$

と移すことで、fifth-power 座標に現れる quartic factor を黄金整数の norm として読み直せる。

つまり、単なる補助変数の置換ではなく、

$$
\text{quartic integer expression}
\longleftrightarrow
\text{quadratic-order norm}
$$

を接続するための再符号化である。

この再符号化があるため、unit classification と coprime factorization を再び利用でき、zero sector を同型の問題へ戻しつつ measure を下げる無限降下が可能になる。

DkMath の FLT5 証明全体の流れでは、unit 分類編を終えた直後に、この写像が descent の recursive geometry を開始する。

## 次に読むべき宣言

次は **`goldenZeroSectorLift_snd`** である。

宣言種別は `theorem`。

```lean
theorem goldenZeroSectorLift_snd (x : GoldenInt) :
    (goldenZeroSectorLift x).snd = x.snd ^ 2 := rfl
```

これは今回の定義の第二座標を公開 API として固定する最初の projection lemma であり、後続の five-divisibility と norm 差分計算で使用される。