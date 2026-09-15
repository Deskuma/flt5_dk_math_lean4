# 0354 — `goldenUnitMeasure`

## 宣言種別

この宣言は **`def`** である。

```lean
/-- Coordinate size used for the elementary unit descent. -/
def goldenUnitMeasure (x : GoldenInt) : ℕ :=
  x.fst.natAbs + x.snd.natAbs
```

定理ではなく、黄金整数の座標に自然数値の「大きさ」を割り当てるための定義である。

## Lean の型

```lean
goldenUnitMeasure (x : GoldenInt) : ℕ
```

入力は黄金整数 `x : GoldenInt`、出力は自然数である。

`GoldenInt` を

$$
x=a+b\varphi
$$

と読み、`x.fst = a`、`x.snd = b` とすると、定義は

$$
\mu(x)=|a|+|b|
$$

である。ただし Lean では整数絶対値を自然数として返す `Int.natAbs` を使っているため、値域は最初から $\mathbb N$ になる。

## 数学的意味

`goldenUnitMeasure` は、黄金整数 $a+b\varphi$ の二つの整数座標に対する $\ell^1$ 型の大きさ

$$
\mu(a,b)=|a|+|b|
$$

を採用している。

これは黄金整数の環ノルム

$$
N(a+b\varphi)=a^2+ab-b^2
$$

とは別物である。環ノルムは unit では $\pm1$ に固定されるため、unit の降下に使う「減少量」としては役に立たない。一方、座標絶対値和は $\varphi$ または $\varphi^{-1}$ を掛けたときに変化し、適切な符号領域では厳密に小さくできる。

前二宣言 0352・0353 はそれぞれ

$$
(a,b)\mapsto(b,a+b),
$$

$$
(a,b)\mapsto(b-a,a)
$$

という座標作用を与えた。本定義はその変換後の座標を自然数の一変数 measure に圧縮する。

## 証明全体での役割

`GoldenUnitClassification` の中心戦略は、黄金整数 unit を $\varphi$ または $\varphi^{-1}$ で動かし、座標 measure を厳密に減少させる有限降下である。

本定義によって

```text
GoldenInt の二座標
      ↓
goldenUnitMeasure : GoldenInt → ℕ
      ↓
自然数上の strict decrease
      ↓
well-founded / strong induction
      ↓
unit の基底ケース
      ↓
符号付き φ の冪としての分類
```

という橋が作られる。

直後の `goldenUnitMeasure_pos` は unit に対してこの measure が正であることを示す。さらに後続の unit descent では、0352・0353 の座標公式を使い、変換後の `goldenUnitMeasure` が元より小さいことを証明する。

したがって本定義は代数的な unit 問題を、Lean が扱いやすい自然数上の well-founded descent へ移すための基準量である。

## 直接依存する定義・補題

本定義自身の直接依存は非常に少ない。

- `GoldenInt` — 黄金整数 $a+b\varphi$ の整数座標型。
- `GoldenInt.fst` — 第一整数座標 $a$。
- `GoldenInt.snd` — 第二整数座標 $b$。
- `Int.natAbs` — 整数の絶対値を自然数として返す関数。
- `Nat` の加法 — 二つの `natAbs` を加えるために使用。

0352 `golden_mul_phi_coords` と 0353 `golden_mul_phiInv_coords` は本定義の構文上の直接依存ではない。しかし **この measure を選ぶ理由** と後続利用を理解するうえでは直接の数学的前段である。

同様に `GoldenUnit` や `goldenNorm` も定義本文には現れない。これらは直後の positivity theorem と降下定理で初めて measure の意味を制約する。

## 構築の流れ

定義本文は一行である。

```lean
x.fst.natAbs + x.snd.natAbs
```

Lean 上では次の処理だけを行う。

1. `x.fst : ℤ` を取り出す。
2. `x.fst.natAbs : ℕ` に変換する。
3. `x.snd : ℤ` を取り出す。
4. `x.snd.natAbs : ℕ` に変換する。
5. 二つの自然数を加える。

証明 tactic、case split、型変換 tactic は存在しない。

この単純さは重要である。後続では measure comparison を最終的に `omega` や整数絶対値に関する補題へ落とすため、測度そのものに複雑な代数構造を持ち込んでいない。

## Lean 固有の処理

### `Int.natAbs` を採用する理由

通常の数学では単に $|a|+|b|$ と書くが、Lean では絶対値の値域をどう選ぶかが重要である。

`Int.natAbs : ℤ → ℕ` を使うことで

```lean
goldenUnitMeasure : GoldenInt → ℕ
```

となり、後続で `Nat.strong_induction_on` や自然数の well-foundedness をそのまま利用できる。

もし整数値絶対値を使って measure を `ℤ` に置けば、非負性から自然数への変換を降下のたびに処理する必要が生じる。本定義はその事務処理を入口で排除している。

### field projection

`x.fst`、`x.snd` は `GoldenInt` の座標 projection であり、抽象的な環表現からではなく、既存の concrete coordinate model を直接利用している。

### reducible な計算定義

`def` なので、必要な箇所では

```lean
simp [goldenUnitMeasure]
```

のように展開できる。実際、直後の `goldenUnitMeasure_pos` でも `simp only [goldenUnitMeasure]` により座標絶対値和へ展開している。

## 冗長・重複箇所

定義そのものには実質的な冗長性はない。

考え得る重複は、プロジェクト内に一般的な「整数二座標の $\ell^1$ measure」が別途存在する場合である。しかし今回確認した `GoldenUnitClassification` の局所コードでは、この目的専用の短い定義として置かれている。

また `GoldenInt` に一般的な size / height API を導入し、そこへ統合する設計も可能ではある。ただし本 measure は unit descent の証明戦略に密接に結び付いており、一般的な黄金整数の「標準的高さ」であるとは正本からは確認できない。したがって現状の局所名は意味上妥当である。

## 最適化候補

現行定義はほぼ最小で、実装上の最適化余地は小さい。

候補を挙げるなら次の程度である。

1. 後続で同じ形が頻出するなら `[simp]` 用の展開補題を別途設ける。
2. unit descent 以外でも同一 measure を広く使うことが判明した場合、`GoldenInt` の一般 API 側へ昇格する。
3. 行列的な座標作用を一般化する場合、$\ell^1$ norm との関係を一般 lemma にまとめる。

ただし 1 は `def` 自体を常時 simp 展開させる必要を意味しない。後続が抽象名 `goldenUnitMeasure` を保持した方が読みやすい箇所もあるため、現状の明示的な `[goldenUnitMeasure]` 展開は制御しやすい。

2・3 は現在の証明を短くする局所最適化ではなく、ライブラリ再設計の候補である。

## 必要 Mathlib import と import 最適化候補

生成 standalone `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本定義単体で必要な外部機能は、実質的には

- `ℤ` / `ℕ`
- `Int.natAbs`
- 自然数加法

だけである。`ring`、`omega`、`nlinarith`、`norm_num` などの tactic は本定義には不要である。

ただし実際の `GoldenUnitClassification` module は前段の `GoldenInt` 定義や unit API を import する必要があるため、**この一宣言だけを見た厳密な最小 Mathlib import と、実モジュール全体の最小 import は同一ではない**。

今回は Lean ビルドを行わないため、具体的な最小 import module 名までは確定しない。少なくとも standalone の `import Mathlib` は本宣言単独には大幅に広い。

## Comparator challenge 化の可否

**可能。難度は初級で、proof challenge より定義設計 challenge に向く。**

例えば

```lean
/-- A natural-valued coordinate measure for descent. -/
def goldenUnitMeasure (x : GoldenInt) : ℕ :=
  ?_
```

として、次の条件を与える。

- `GoldenInt` は整数二座標を持つ。
- measure は符号に依存しない。
- 値域は `ℕ`。
- 後で strict descent / strong induction に使いたい。

期待される最短解は

```lean
x.fst.natAbs + x.snd.natAbs
```

である。

より Comparator 向きにするなら定義そのものを穴にするより、定義を与えたうえで

```lean
example (x : GoldenInt) :
    goldenUnitMeasure x = x.fst.natAbs + x.snd.natAbs := by
  ?_
```

のような展開問題にできる。ただしこれは `rfl` 級であり識別力は低い。

したがって challenge としての価値は「なぜ `Int.natAbs` により自然数 measure を選ぶのか」という設計判断にある。

## 次に読むべき宣言

次は **0355 `goldenUnitMeasure_pos`** を読むべきである。宣言種別は **`theorem`**。

```lean
theorem goldenUnitMeasure_pos {x : GoldenInt} (hx : GoldenUnit x) :
    0 < goldenUnitMeasure x := by
  have hn := goldenNorm_eq_one_or_neg_one_of_unit hx
  simp only [goldenUnitMeasure]
  by_contra h
  have hz : x.fst.natAbs + x.snd.natAbs = 0 := Nat.eq_zero_of_not_pos h
  have haf : x.fst.natAbs = 0 := by omega
  have hbf : x.snd.natAbs = 0 := by omega
  have ha : x.fst = 0 := Int.natAbs_eq_zero.mp haf
  have hb : x.snd = 0 := Int.natAbs_eq_zero.mp hbf
  rcases hn with hn | hn <;> simp [goldenNorm, ha, hb] at hn
```

本定義だけではゼロ元に対して

$$
\mu(0,0)=0
$$

である。0355 は `GoldenUnit x` という条件を加えることで unit がゼロ元ではあり得ないことを環ノルム $\pm1$ から導き、

$$
0<\mu(x)
$$

を保証する。

これにより後続の自然数降下で「measure 0 の unit」という異常な終端を排除し、基底ケースへ進む準備が整う。
