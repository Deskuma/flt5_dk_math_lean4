# 0120 — `goldenOne`

## Lean の型

```lean
def goldenOne : GoldenInt := ⟨1, 0⟩
```

`goldenOne` は 0118 で導入した `GoldenInt` の第一座標を整数 $1$、第二座標を整数 $0$ とした要素である。

$$
goldenOne=(1,0).
$$

`GoldenInt` を $a+b\varphi$ の座標モデルとして読むと、これは

$$
1+0\varphi=1
$$

に対応する。

## 数学的主張

この宣言は theorem ではなく定義であり、黄金整数座標系における乗法単位元の候補を具体的に与える。

この時点ではまだ Lean の型クラス `[One GoldenInt]` 自体は導入されていない。source では後続に

```lean
instance : One GoldenInt := ⟨goldenOne⟩
```

が置かれ、そこで通常の記法 `(1 : GoldenInt)` が `goldenOne` を参照するようになる。

したがって 0120 は「乗法単位元の座標値を定める層」であり、型クラスとして単位元を公開する層とは意図的に分離されている。

## 証明全体での役割

`GoldenOrder.lean` は `GoldenInt` を $\mathbb Z[\varphi]$ の直接座標モデルとして環へ育てていく。0118 が carrier、0119 が零元候補を定め、0120 は乗法単位元候補を定める。

直後には `goldenAdd`、`goldenNeg`、`goldenSub`、`goldenMul`、`goldenPow` が続き、その後 `Zero`、`One`、`Add`、`Neg`、`Sub`、`Mul` の各 instance に接続される。さらに座標ごとの簡約補題と環法則が整備されるため、`goldenOne` は黄金整数環の multiplicative identity を concrete coordinate として固定する最小部品である。

また `goldenPow` の基底ケースは

```lean
| 0 => goldenOne
```

で定義されるため、自然数冪の再帰定義にも直接使われる。この意味で `goldenOne` は単なる記法用定義ではなく、後続の冪演算の計算的基点でもある。

FLT5 固有の five-adic 情報や square-golden packet を直接処理する宣言ではないが、後段の黄金整数整除、ノルム、Euclidean-domain 構造、単元分類、五乗因子抽出を支える algebraic infrastructure の基礎に属する。

## 直接依存する定義・補題

直接依存はほぼ 0118 `GoldenInt` のみである。

- `GoldenInt` — 値を構築する対象型。
- 整数リテラル `1 : ℤ` と `0 : ℤ` — `fst`, `snd` の座標値。
- structure constructor notation `⟨1, 0⟩` — `GoldenInt.mk 1 0` の省略記法。

論理的な補題や tactic には依存しない。FLT5 equation、five-adic packet、square-golden exceptional packet などにも直接依存しない。

後続から見た主要な直接利用先は `goldenPow` の零乗ケースと `One GoldenInt` instance である。

## 証明・構築の流れ

proof script は存在しない。定義本体がそのまま structure constructor application である。

```lean
⟨1, 0⟩
```

Lean は期待型 `GoldenInt` から、これを概念的に

```lean
GoldenInt.mk 1 0
```

と解釈する。

よって unfolding すれば

```lean
goldenOne.fst = 1
goldenOne.snd = 0
```

は定義簡約で得られる。

さらに後続の

```lean
instance : One GoldenInt := ⟨goldenOne⟩
```

導入後は

```lean
(1 : GoldenInt).fst = 1
(1 : GoldenInt).snd = 0
```

も `rfl` ベースの簡約対象となる。source では実際に `golden_fst_one` と `golden_snd_one` が `[simp]` theorem として用意されている。

## Lean 固有の処理

### 期待型による constructor 推論

`⟨1, 0⟩` に `GoldenInt.mk` を明記していないが、返り値型 `GoldenInt` から Lean が constructor を推論する。

### 数値リテラルの elaboration

`1` と `0` は `GoldenInt.fst`, `GoldenInt.snd` の型が `ℤ` であるため整数リテラルとして elaboration される。ここで `1` は `GoldenInt` 自身の `One` instance を必要としていない。座標型 `ℤ` の `OfNat` が使われるからである。

### definitional equality

`goldenOne` の座標値は theorem によって証明されるのではなく、definition unfolding だけで決まる。そのため `rfl`、`simp [goldenOne]`、`dsimp [goldenOne]` などで直接扱える。

### raw definition と typeclass instance の分離

後続の

```lean
instance : One GoldenInt := ⟨goldenOne⟩
```

によって通常の `1` 記法が初めて `GoldenInt` に導入される。concrete implementation と typeclass registration を分離する設計は 0119 `goldenZero` と対になっている。

### 冪の基底ケース

後続 `goldenPow` は

```lean
def goldenPow (x : GoldenInt) : ℕ → GoldenInt
  | 0 => goldenOne
  | n + 1 => goldenMul (goldenPow x n) x
```

と定義される。したがって `goldenOne` は `x^0=1` に対応する recursion anchor として計算にも現れる。

## 冗長・重複箇所

宣言本体は最小であり、内部の冗長性はない。

一方、0119 `goldenZero` とほぼ同じ設計パターンを持つ。

```lean
def goldenZero : GoldenInt := ⟨0, 0⟩
def goldenOne  : GoldenInt := ⟨1, 0⟩
```

この重複は意図的な primitive API symmetry と見るのが自然である。zero/one の concrete coordinate を個別名で公開してから typeclass instance に接続することで、環構造を構築する前の段階でも raw operations を参照できる。

また `One GoldenInt` instance 側へ

```lean
instance : One GoldenInt := ⟨⟨1, 0⟩⟩
```

と直接埋め込めば `goldenOne` は省略可能である。しかしその場合、`goldenPow` の基底ケースや後続証明で concrete unit を名前付きで参照する API が失われる。

## 最適化候補

### 1. `One` instance へ inline する

コード量だけを減らすなら `goldenOne` を削除し、`One GoldenInt` instance に `⟨1,0⟩` を直接埋め込める。ただし `goldenPow` などが typeclass notation に依存するようになり、primitive coordinate layer と algebraic typeclass layer の分離が弱くなる。

### 2. `goldenPow` を標準 `Pow` 導入後に定義する

現行は explicit API として `goldenPow` の零乗に `goldenOne` を使う。先に `One` / `Mul` を導入して標準冪へ寄せれば独自の base case を減らせる可能性がある。ただしこの順序変更は後続 proof の definitional behavior を変える可能性があるため、単純な置換とは限らない。

### 3. zero/one を共通 constructor helper で表す

例えば整数 $a$ を定数埋め込みする

```lean
def goldenOfInt (a : ℤ) : GoldenInt := ⟨a, 0⟩
```

を導入し、`goldenZero := goldenOfInt 0`、`goldenOne := goldenOfInt 1` とする案がある。後で整数埋め込み API を必要とするなら有用だが、現時点の二定義だけなら抽象化の方が重い可能性がある。

### 4. simp API の整理

source には instance 導入後の

```lean
@[simp] theorem golden_fst_one : (1 : GoldenInt).fst = 1 := rfl
@[simp] theorem golden_snd_one : (1 : GoldenInt).snd = 0 := rfl
```

があるため、raw `goldenOne.fst` / `.snd` 専用補題を追加する必要性は低い。既存 simp API を維持する方が重複が少ない。

## 必要 Mathlib import と import 最適化候補

standalone source は冒頭で

```lean
import Mathlib
```

を一括 import している。

`goldenOne` 単独では、既に `GoldenInt` と整数型が利用可能なら新しい Mathlib theorem は不要である。必要なのは structure constructor と整数リテラルだけであり、本宣言のためだけに `Mathlib` 全体を import する必要はない。

ただし `GoldenOrder.lean` module 全体では後続に環構造、整数多項式計算、共役・ノルム、`Zsqrtd 5` への写像、zero-divisor 排除、`simp` / `ring` などが現れるため、module 単位の最小 import は当然これより大きい。

本記事では Lean build を行っていないため、正確な最小 import 集合は未検証である。したがって import 縮小については最適化候補としてのみ述べる。

## Comparator challenge 化の可否

`goldenOne` 単独では一行定義なので challenge としては小さすぎる。しかし `GoldenInt` primitive API の設計比較の一部としては良い Comparator 題材になる。

比較候補は、(a) 現行の raw definition + `One` instance 二段階方式、(b) `One` instance へ直接 inline、(c) `goldenOfInt` のような整数埋め込みを先に導入する方式、(d) 標準 ring structure を先に構築して `(1 : GoldenInt)` のみを使う方式である。

評価軸は、定義簡約の透明性、`goldenPow` の実装の自然さ、typeclass dependency の少なさ、`simp` の安定性、後続 ring-law proof の短さ、監査しやすさである。

## 根拠資料と推測の範囲

形式的根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenOrder.lean` generated section である。そこでは `GoldenInt`、`goldenZero` の直後に `goldenOne` が置かれ、その後 `goldenAdd`、`goldenNeg`、`goldenSub`、`goldenMul`、`goldenPow` と続く。

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在することを確認した。ただし今回は GitHub コネクタから PDF 本文の `goldenOne` 対応ページを直接照合できていないため、ページ番号、節番号、PDF 固有の叙述は推測していない。

`goldenOfInt`、import 最小化、標準冪への統合は最適化候補であり、現行 source の採用事項ではない。

## 次に読むべき宣言

依存順で直後は

```lean
def goldenAdd (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst + y.fst, x.snd + y.snd⟩
```

である。

0119 と 0120 で零元・単位元という distinguished elements が揃い、次は二つの黄金整数を座標ごとに加える最初の二項演算へ進む。したがって次号は `goldenAdd` を読むのが自然である。