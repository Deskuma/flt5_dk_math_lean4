# 0291 — `GoldenZeroSectorCandidate.product_neg`

## 宣言種別

これは **`theorem`** である。

`GoldenZeroSectorCandidate` に保存された zero-sector の符号付き積等式から、その積が必ず厳密に負であることを取り出す。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- The signed product in every candidate is strictly negative. -/
theorem product_neg (p : GoldenZeroSectorCandidate) :
    p.s * goldenFifthSndFactor p.r p.s < 0 := by
  rw [p.product_eq]
  have ha : (0 : ℤ) < p.a := by exact_mod_cast p.a_pos
  exact mul_neg_of_neg_of_pos (by norm_num) (pow_pos ha 10)
```

数学的には、`p : GoldenZeroSectorCandidate` が保持する

$$
p.s\,H(p.r,p.s)=-5^6p.a^{10},
$$

ここで

$$
H(r,s)=\texttt{goldenFifthSndFactor}(r,s),
$$

および

$$
p.a>0
$$

から

$$
p.s\,H(p.r,p.s)<0
$$

を導く theorem である。

## 数学的意味

0290 `GoldenZeroSectorCandidate` は zero-sector arithmetic から inversion 層へ渡す証明証書として、符号付き積等式

$$
sH(r,s)=-5^6a^{10}
$$

を field `product_eq` に保存している。

本 theorem はその等式の右辺の符号を評価するだけである。

`a_pos` により

$$
a>0
$$

なので、偶数指数 10 に対して

$$
a^{10}>0.
$$

また

$$
-5^6<0.
$$

したがって

$$
-5^6a^{10}<0,
$$

よって `product_eq` を通して

$$
sH(r,s)<0
$$

が得られる。

この theorem は新しい代数恒等式を発見するものではなく、structure に保存された **符号付き exact equation を order information に変換する projection theorem** である。

## 証明全体での役割

0288–0289 では四次因子 $H(r,s)$ の対角化と非負性

$$
H(r,s)\ge 0
$$

が得られた。0290 では zero-sector candidate の全情報が structure にまとめられた。

0291 はその structure を受け取って、まず積全体の符号

$$
sH<0
$$

を確定する。

この情報は直後の 0292 `GoldenZeroSectorCandidate.H_pos` で決定的に使われる。0292 は 0289 の

$$
H\ge 0
$$

と、本 theorem の

$$
sH<0
$$

を組み合わせて $H\neq 0$ を示し、最終的に

$$
H>0
$$

へ強化する。

さらにその後の `s_neg` では、正となった $H$ と負の積から

$$
s<0
$$

が導かれる。したがって 0291 は

$$
\text{signed product equation}
\longrightarrow
sH<0
\longrightarrow
H>0
\longrightarrow
s<0
$$

という zero-sector の符号確定鎖の最初の theorem である。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate`

直前の 0290 で導入された structure。本 theorem では特に次の field を使う。

```lean
product_eq :
  s * goldenFifthSndFactor r s = -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10

a_pos : 0 < a
```

`product_eq` が exact equation を、`a_pos` が右辺の正の tenth-power factor を保証する。

### `goldenFifthSndFactor`

積の第二因子

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4
$$

である。

### `pow_pos`

`ha : 0 < (p.a : ℤ)` から

$$
0<(p.a:\mathbb Z)^{10}
$$

を導く。

### `mul_neg_of_neg_of_pos`

負数と正数の積が負であることを与える order lemma。本証明では

$$
-(5:\mathbb Z)^6<0
$$

と

$$
(p.a:\mathbb Z)^{10}>0
$$

を結合する。

### `exact_mod_cast`

`p.a_pos : 0 < p.a` は自然数上の命題なので、これを整数上の

$$
0<(p.a:\mathbb Z)
$$

へ移すために使う。

### `norm_num`

固定定数

$$
-(5:\mathbb Z)^6<0
$$

を閉じる。

## 証明の流れ

### 1. `product_eq` で左辺を書き換える

```lean
rw [p.product_eq]
```

目標

```lean
p.s * goldenFifthSndFactor p.r p.s < 0
```

は

```lean
-(5 : ℤ) ^ 6 * (p.a : ℤ) ^ 10 < 0
```

へ変わる。

この時点で zero-sector 固有の algebra は structure field の書き換えによって完全に消え、残るのは整数の符号計算だけである。

### 2. `a_pos` を整数へ cast する

```lean
have ha : (0 : ℤ) < p.a := by
  exact_mod_cast p.a_pos
```

`p.a` の field 型は `ℕ` なので、`pow_pos` を整数側で使えるよう正値性を `ℤ` に移す。

### 3. 負 × 正で結論する

```lean
exact mul_neg_of_neg_of_pos (by norm_num) (pow_pos ha 10)
```

`norm_num` が左因子の負性、`pow_pos ha 10` が右因子の正性を証明し、`mul_neg_of_neg_of_pos` が積の負性を返す。

## Lean 固有の処理

本 theorem の Lean 上の中心は **自然数から整数への coercion の整理** である。

structure では `a : ℕ` として保存されている一方、`product_eq` は整数等式なので右辺には `(a : ℤ)` が現れる。そのため `p.a_pos : 0 < p.a` をそのまま `pow_pos` に渡すのではなく、

```lean
have ha : (0 : ℤ) < p.a := by exact_mod_cast p.a_pos
```

という橋渡しを置いている。

また `rw [p.product_eq]` により namespace projection `p.product_eq` を rewrite rule として使う。0290 を flat structure にした利点がここに現れており、長い仮定列を再度引数として渡す必要がない。

証明には `ring` や `nlinarith` は不要である。必要なのは exact rewrite、cast、固定定数評価、order lemma だけである。

## 冗長・重複箇所

証明は非常に短く、明白な冗長性はほとんどない。

`ha` を局所名として置かず、`pow_pos` の中で cast proof を直接構成することも理論上は可能だが、

```lean
have ha : (0 : ℤ) < p.a := by exact_mod_cast p.a_pos
```

と分離した現行形の方が、型境界が明示されて教育的である。

また `norm_num` で $-5^6<0$ を証明している部分は固定値計算なので、別 lemma に切り出す価値は薄い。

## 最適化候補

### 1. cast の局所 helper 化

後続 theorem 群で `p.a_pos`, `p.c_pos`, `p.d_pos` などの `ℕ` 正値性を繰り返し `ℤ` へ移すなら、自然数正値性の cast helper を設ける選択肢はある。

ただし本 theorem 単独では `exact_mod_cast` 一行で済み、抽象化による短縮効果は小さい。

### 2. `simpa` を使った別 proof

`product_eq` を先に局所等式として取り出し、右辺の負性を別 `have` で証明して最後に `simpa [p.product_eq]` とする書き方も可能である。

現行の `rw` は証明状態を直接 arithmetic goal に変えるため、より簡潔である。

### 3. theorem の API 価値

論理的には後続 theorem の内部で `p.product_eq` から毎回直接負性を導ける。しかし `product_neg` を名前付き API として置くことで、以後は zero-sector の具体式 $-5^6a^{10}$ を隠蔽し、単純な order fact として再利用できる。したがって削除よりも現在の theorem 化の方が構造的に有利である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem が直接使う主な機能は、

- `ℕ` と `ℤ` の coercion
- ordered ring 上の `pow_pos`
- `mul_neg_of_neg_of_pos`
- `exact_mod_cast`
- `norm_num`
- 既存 structure `GoldenZeroSectorCandidate`
- 既存定義 `goldenFifthSndFactor`

である。

`ring`, `omega`, `positivity`, `nlinarith` は本 theorem 自体には不要である。

ただしこの作業では Lean build を行わないため、元 module `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` の厳密な最小 import 集合は **未検証** である。`import Mathlib` からの具体的削減先は推測で断定しない。

## Comparator challenge 化の可否

**適している。**

問題としては短いが、

1. structure projection `p.product_eq` を使う。
2. `ℕ` の正値性を `ℤ` へ移す。
3. 冪の正値性を証明する。
4. 負 × 正の符号 lemma で閉じる。

という Lean 固有の小さな要素がまとまっている。

例えば

```lean
theorem challenge (p : GoldenZeroSectorCandidate) :
    p.s * goldenFifthSndFactor p.r p.s < 0 := by
  ...
```

として、`product_eq` と `a_pos` を使える状態で proof hole を埋める形式が良い。

難度は低めだが、`exact_mod_cast` を使う解、より明示的な cast lemma を使う解を比較できるため、Comparator の短問として有用である。

判定は **適する** とする。

## PDF との対応

対象 branch の repository tree には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在する。

GitHub の通常テキスト取得経路および今回試した PDF 直接取得では binary 本文を解析可能な形で取得できなかった。そのため、本 theorem と PDF の具体的ページ・節番号・文言との対応は **未確認** であり、推測しない。

ここでの技術的説明は、対象 branch の `Flt5DkMath/FLT5StandAlone.lean` と直前の theorem museum 文書を主根拠とする。

## 次に読むべき宣言

次は 0292 `GoldenZeroSectorCandidate.H_pos` である。種別は **`theorem`**。

正本では本 theorem の直後に置かれ、0289 `goldenFifthSndFactor_nonneg` と 0291 `product_neg` を組み合わせて

$$
0<goldenFifthSndFactor\ p.r\ p.s
$$

を示す。

すなわち 0291 が積全体の負性を確定し、0292 が四次因子の非負性を厳密な正性へ強化する流れである。
