# 0121 — `goldenAdd`

## Lean の型

```lean
def goldenAdd (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst + y.fst, x.snd + y.snd⟩
```

`goldenAdd` は 0118 で導入した `GoldenInt` の二つの座標を成分ごとに加える二項演算である。

`GoldenInt` を

$$
x=a+b\varphi,\qquad y=c+d\varphi
$$

という座標表示で読むと、定義は

$$
goldenAdd(x,y)=(a+c)+(b+d)\varphi
$$

に対応する。

## 数学的主張

この宣言は theorem ではなく定義であり、黄金整数座標系における加法を通常の整数座標の加法として定める。

$$
(a,b)+(c,d)=(a+c,b+d).
$$

この時点ではまだ Lean の型クラス `[Add GoldenInt]` は導入されていない。source では後続に

```lean
instance : Add GoldenInt := ⟨goldenAdd⟩
```

が置かれ、そこで標準記法 `x + y` が `goldenAdd x y` を参照するようになる。

したがって 0121 は、黄金整数環の加法を concrete coordinate operation として固定する primitive API である。

## 証明全体での役割

`GoldenOrder.lean` は `GoldenInt` を単なる整数対から、後続の FLT5 証明で利用できる可換環へ育てる module である。0118 `GoldenInt` が carrier、0119 `goldenZero` が零元候補、0120 `goldenOne` が単位元候補を与え、0121 `goldenAdd` で最初の二項演算が導入される。

直後には

```lean
def goldenNeg ...
def goldenSub ...
def goldenMul ...
def goldenPow ...
```

が続き、その後 `Zero`、`One`、`Add`、`Neg`、`Sub`、`Mul` の typeclass instance と `AddCommGroup`、`CommRing` instance が構築される。

特に後続の

```lean
instance goldenAddCommGroup : AddCommGroup GoldenInt := by
  ...
```

では、`goldenAdd` が実際の加法として使われ、加法結合則、零元、逆元、可換性が各座標の整数算術へ還元される。このため 0121 は単なる convenience wrapper ではなく、黄金整数環の加法構造そのものを固定する定義である。

FLT5 固有の five-adic packet や descent を直接扱わないが、後段の共役、ノルム、整除、Euclidean-domain 構造、単元分類、五乗因子抽出のすべてがこの環構造を利用する。

## 直接依存する定義・補題

直接依存は非常に小さい。

- `GoldenInt` — 入力と出力の型。
- `GoldenInt.fst`, `GoldenInt.snd` — 二つの整数座標への projection。
- 整数加法 `Int` の `+` — 各座標の加法。
- `GoldenInt` の structure constructor — `⟨..., ...⟩` により結果を構築する。

論理的な theorem、FLT5 equation、five-adic lemma、golden norm lemma には直接依存しない。

後続から見た主要な直接利用先は `Add GoldenInt` instance、`goldenSub`、`goldenAddCommGroup`、および座標 simp theorem `golden_fst_add` / `golden_snd_add` である。

## 証明・構築の流れ

proof script は存在しない。定義本体がそのまま計算規則である。

1. `x.fst` と `y.fst` を整数として加える。
2. `x.snd` と `y.snd` を整数として加える。
3. 得られた二つの整数を `GoldenInt` constructor に渡す。

すなわち

```lean
goldenAdd x y
```

を unfolding すると

```lean
⟨x.fst + y.fst, x.snd + y.snd⟩
```

へ定義簡約される。

後続の `Add GoldenInt` instance 導入後には

```lean
@[simp] theorem golden_fst_add (x y : GoldenInt) :
    (x + y).fst = x.fst + y.fst := rfl

@[simp] theorem golden_snd_add (x y : GoldenInt) :
    (x + y).snd = x.snd + y.snd := rfl
```

が `rfl` で成立する。つまり標準加法記法と raw coordinate definition の間に証明上の隙間がない。

## Lean 固有の処理

### projection による座標演算

`x.fst` / `x.snd` は structure projection であり、`GoldenInt` の内部表現を明示的に取り出す。加法は quotient や coercion を介さず、完全に座標上で計算される。

### 期待型による constructor 推論

返り値型が `GoldenInt` と決まっているため、

```lean
⟨x.fst + y.fst, x.snd + y.snd⟩
```

は `GoldenInt.mk ... ...` と elaboration される。

### definitional equality

`goldenAdd` は opaque theorem ではなく definition なので、座標等式は unfolding と `rfl` で得られる。この性質が後続の `[simp]` 補題と環法則証明を非常に軽くしている。

### raw operation と typeclass operation の分離

source は先に `goldenAdd` を定義し、後で

```lean
instance : Add GoldenInt := ⟨goldenAdd⟩
```

と登録する。これにより typeclass hierarchy を構築する前でも raw operation を参照でき、`goldenSub` や `goldenMul` など explicit API と同じ設計規則を保てる。

### `simp` との相性

`Add` instance 導入後の `golden_fst_add` / `golden_snd_add` は `rfl` であり `[simp]` 属性が付く。したがって後続証明では GoldenInt の加法を整数座標の加法へ自動的に落とせる。

## 冗長・重複箇所

定義本体は最小で、内部冗長性はない。

ただし設計上は、後続の

```lean
instance : Add GoldenInt := ⟨goldenAdd⟩
```

と二段階になっているため、`goldenAdd` と標準 `x + y` は最終的に同一操作を二つの名前で持つ。さらに source 後方には

```lean
@[simp] theorem golden_add_eq (x y : GoldenInt) : goldenAdd x y = x + y := rfl
```

も置かれる。

これは論理的な重複というより、explicit coordinate API と Mathlib typeclass API を橋渡しする意図的な二層構造である。

また `goldenNeg` も座標ごとの演算として定義され、`goldenSub` は

```lean
goldenAdd x (goldenNeg y)
```

で構成される。加法を primitive として一度固定しておくことで subtraction を再度座標展開せずに済む。

## 最適化候補

### 1. `Add` instance へ直接 inline する

最短化だけを狙うなら

```lean
instance : Add GoldenInt :=
  ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
```

と書ける。しかし `goldenSub` や後続の explicit API が typeclass elaboration に依存しやすくなり、primitive coordinate layer の監査性は下がる。

### 2. `GoldenInt` を `ℤ × ℤ` として実装する

pair の標準加法を利用すれば一部の定義は短くできる可能性がある。一方で `fst` / `snd` の意味を domain-specific structure として固定できなくなり、後続の golden-order API の可読性や namespace 設計は弱くなる。

### 3. `AddCommGroup` を先に構築する

加法・零元・負元をまとめて `AddCommGroup GoldenInt` として直接与え、その field から `Add` instance を得る設計も考えられる。ただし現行のように primitive operation を先に定義すると、各 operation の計算規則が明示的で、後続の `rfl` ベース simp API が分かりやすい。

### 4. coordinatewise operation helper を一般化する

例えば二項整数関数を各座標へ適用する generic helper を作ることもできるが、`goldenMul` は座標混合を行うため全操作には一般化できない。`goldenAdd` 一つのためだけなら抽象化コストの方が大きい。

## 必要 Mathlib import と import 最適化候補

standalone source は冒頭で

```lean
import Mathlib
```

を一括 import している。

`goldenAdd` 単独が必要とするのは、既に `GoldenInt` と整数加法が利用可能であることだけである。本宣言自身は `ring`、`simp`、`omega`、number field API、Euclidean-domain API などを使用しない。

したがって本宣言のためだけなら `Mathlib` 全体は明らかに過大であり、Lean core と整数型を提供する非常に小さな import で足りるはずである。

ただし `GoldenOrder.lean` module 全体では後続に `AddCommGroup`、`CommRing`、`Zsqrtd 5`、`NoZeroDivisors`、`IsDomain`、`ring`、`omega`、`norm_num` などが必要になる。module 単位の正確な最小 import 集合は Lean build を行っていないため未検証であり、ここでは最適化候補としてのみ述べる。

## Comparator challenge 化の可否

`goldenAdd` 単独は一行定義なので、証明探索 challenge としては小さい。しかし data-model / API-design Comparator としては良い題材になる。

比較案は次のようになる。

- 現行: raw `goldenAdd` を先に定義し、後で `Add` instance に登録する。
- typeclass-first: `Add GoldenInt` を直接定義し、必要なら `goldenAdd := (· + ·)` と後置する。
- bundled algebra: `AddCommGroup` を直接構築して primitive instances をそこから得る。
- carrier を `ℤ × ℤ` とし、product type の既存加法を利用する。

評価軸は、definitional equality の強さ、`rfl` / `simp` の安定性、後続 `goldenSub` の自然さ、環構造構築の短さ、source auditability、Mathlib typeclass dependency の量である。

## 根拠資料と推測の範囲

形式的根拠は `docs/flt5-theorem-museum` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenOrder.lean` generated section である。そこでは `goldenOne` の直後に `goldenAdd` が置かれ、その後 `goldenNeg`、`goldenSub`、`goldenMul`、`goldenPow` と続く。

対象ブランチには既存の日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし今回、PDF 本文内の `goldenAdd` 対応ページを直接照合していないため、PDF のページ番号・節番号や叙述内容は推測していない。

standalone source 自身は generated artifact で、元 source module として `DkMath/FLT/Five/GoldenOrder.lean` を列挙している。この provenance は source header に基づく。

## 次に読むべき宣言

依存順で次に置かれている未解説宣言は

```lean
def goldenNeg (x : GoldenInt) : GoldenInt := ⟨-x.fst, -x.snd⟩
```

である。

`goldenAdd` が additive composition を導入したのに対し、`goldenNeg` は各座標を符号反転し、加法逆元を与える。これが揃うと次の `goldenSub` は

```lean
goldenAdd x (goldenNeg y)
```

として定義できるため、0122 では黄金整数の additive inverse を読むのが自然である。
