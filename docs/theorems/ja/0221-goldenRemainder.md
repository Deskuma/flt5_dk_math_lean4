# 0221 — `goldenRemainder`

## Lean の型

```lean
/-- The residual after nearest-lattice normalization. -/
def goldenRemainder (x y : GoldenInt) : GoldenInt :=
  x - goldenMul (goldenQuotient x y) y
```

これは `theorem` ではなく `def` であり、0220 `goldenQuotient` で選んだ黄金整数 quotient を使って、通常の Euclidean division と同じ形の remainder

$$
r=x-qy
$$

を `GoldenInt` 内部に定義する。

## 数学的主張・宣言の意味

`q = goldenQuotient x y` と置けば、本定義は

$$
r=x-qy
$$

そのものである。

ここで `q` は 0219 の有理 quotient coordinates を各座標で最近接整数へ丸めて得た黄金整数である。したがって `goldenRemainder` は単なる差ではなく、**有理商を黄金整数格子へ正規化した後に残る誤差** を表す。

`x/y = A+Bφ` と読めるとき、`q` は概念的に

$$
q=\operatorname{round}(A)+\operatorname{round}(B)\varphi
$$

であり、remainder は

$$
r=x-qy
$$

となる。後続ではこの remainder を `y` で割った相対誤差が、丸め誤差

$$
A-\operatorname{round}(A),\qquad B-\operatorname{round}(B)
$$

に対応することを示し、0214 の golden-norm contraction cell を適用する。

## 証明全体での役割

`GoldenEuclidean.lean` の norm-Euclidean division は、次の流れで構成される。

1. 0216–0218 で `x * conjugate(y)` の整数座標を計算する。
2. 0219 `goldenQuotientCoords` でそれらを `N(y)` で割り、有理 quotient coordinates を得る。
3. 0220 `goldenQuotient` で二座標を最近接整数へ丸める。
4. **0221 `goldenRemainder` で `r = x - qy` を定義する。**
5. `golden_quotient_mul_add_remainder` で

$$
yq+r=x
$$

という Euclidean division identity を証明する。
6. private theorem `goldenRemainder_norm_rat_identity` で `N(r)` を `N(y)` と丸め誤差ノルムの積へ分解する。
7. `golden_remainder_size_lt` で

$$
|N(r)|<|N(y)|
$$

を得る。
8. 最終的に `goldenEuclideanDomain` の `remainder` field に本定義をそのまま登録する。

正本 source では実際に

```lean
noncomputable instance goldenEuclideanDomain : EuclideanDomain GoldenInt where
  quotient := goldenQuotient
  quotient_zero := goldenQuotient_zero
  remainder := goldenRemainder
  quotient_mul_add_remainder_eq := golden_quotient_mul_add_remainder
  ...
```

と使われる。したがって本定義は補助的な差分関数ではなく、完成した Euclidean-domain structure の remainder algorithm そのものである。

## 直接依存する定義・補題

直接依存するのは次の定義・標準構造である。

- `GoldenInt`
- 0220 `goldenQuotient`
- 0124 `goldenMul`
- `Sub GoldenInt` instance

本宣言自体は `def` なので proof script はない。

数学的背景としては、

- 0219 `goldenQuotientCoords`
- 0213 `goldenRat_norm_abs_le_five_sixteen`
- 0214 `goldenRat_norm_abs_lt_one`

が quotient rounding と strict contraction を支える。

依存の概念図は

$$
q=\operatorname{goldenQuotient}(x,y)
\longrightarrow
r=x-qy
\longrightarrow
N(r)=N(y)\,Q(\text{rounding error})
\longrightarrow
|N(r)|<|N(y)|
$$

である。

## 構築の流れ

定義は一行である。

```lean
def goldenRemainder (x y : GoldenInt) : GoldenInt :=
  x - goldenMul (goldenQuotient x y) y
```

1. `goldenQuotient x y` で離散 quotient `q` を得る。
2. `goldenMul q y` で divisor `y` の `q` 倍を計算する。
3. `x - qy` を `GoldenInt` の減算で計算する。
4. 得られた `GoldenInt` を remainder とする。

この定義自体には norm inequality は含まれない。remainder の **構成** と、remainder が本当に Euclidean に小さくなるという **証明** を分離している。

## Lean 固有の処理

### 1. raw multiplication と標準 subtraction の混在

乗法は `goldenMul` を明示的に使う一方、減算は標準記法 `x - ...` を使っている。

これは既存 API が raw coordinate operation と Mathlib 標準 algebra notation の両方を併用しているためである。後続 theorem `golden_quotient_mul_add_remainder` では

```lean
simp [goldenRemainder, golden_mul_eq]
ring
```

と、`golden_mul_eq` を使って raw `goldenMul` を標準 `*` へ接続する。

### 2. remainder も total function

`goldenRemainder x y` は `y ≠ 0` を仮定しない。したがって `goldenRemainder x 0` も定義される。

これは `EuclideanDomain` の `remainder` field が全域関数である設計と整合する。strict decrease theorem の方でのみ `hy : y ≠ 0` を要求する。

### 3. projection simp lemma が後続 proof で直接使われる

`goldenRemainder_norm_rat_identity` では、

```lean
simp only [goldenRemainder, goldenMul, golden_fst_sub, ...]
```

および

```lean
simp only [goldenRemainder, goldenMul, golden_snd_sub, ...]
```

として remainder の第一・第二座標を有理式へ展開する。0130台〜0140台で整備された projection API がここで Euclidean proof の実働部品として回収されている。

## 冗長・重複箇所

数学的には `r = x - qy` という標準的な remainder 定義なので、`goldenRemainder` 専用名を置かず、その都度式を直接書くことも可能である。

しかし専用定義には明確な利点がある。

- EuclideanDomain instance の `remainder` field に直接渡せる。
- 長い norm identity で同じ `x - qy` を繰り返さずに済む。
- quotient algorithm と remainder algorithm の API 境界が明瞭になる。
- 将来 quotient の選び方を変更しても downstream theorem の statement を保ちやすい。

一方、raw `goldenMul` と標準 `*` の混在は軽い API 重複を生んでいる。`goldenRemainder := x - goldenQuotient x y * y` と標準記法だけで定義する案も比較可能である。

## 最適化候補

1. **標準 `*` 記法へ統一する**

```lean
def goldenRemainder (x y : GoldenInt) : GoldenInt :=
  x - goldenQuotient x y * y
```

とすれば、後続で `golden_mul_eq` を明示する場面が減る可能性がある。

2. **quotient / remainder を同時に返す構造を作る**

`GoldenDivisionResult` のような structure に `q`, `r`, identity certificate をまとめれば、後続 proof の再計算を減らせる。ただし API は重くなる。

3. **zero-divisor branch を明示する**

`if y = 0 then x else ...` のような定義も考えられる。しかし現行では quotient 自体が total であり、EuclideanDomain の仕様 theorem を別途証明する方が単純である。

4. **一般 quadratic Euclidean lattice へ抽象化する**

`r = x - qy` 自体は一般的なので、golden-order 固有部分を quotient selection と norm contraction のみに限定する設計が可能である。

5. **remainder norm identity を bundle する**

現在 private theorem になっている `goldenRemainder_norm_rat_identity` は Euclidean proof の魔核に近い。再利用が増えるなら public API 化を検討できる。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 `def` 単独で直接必要なのは主に、

- `GoldenInt`
- subtraction notation / `Sub`
- `goldenMul`
- `goldenQuotient`

であり、tactic や解析 theorem は使用しない。

ただし `GoldenEuclidean.lean` 全体では `round`, `abs_sub_round`, `nlinarith`, `field_simp`, `ring`, `Int.natAbs`, `measure`, `EuclideanDomain` など広い Mathlib API を使う。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 raw `goldenMul` を使う remainder 定義
- B: 標準 `*` のみを使う remainder 定義
- C: quotient / remainder / identity certificate を bundle する設計
- D: zero divisor branch を明示する total division API
- E: 一般 quadratic-order Euclidean division framework の特殊化

比較軸は、

- `golden_quotient_mul_add_remainder` の proof 長
- norm identity proof の展開量
- simp / rewrite burden
- EuclideanDomain instance への接続の自然さ
- raw coordinate API の監査性
- 一般化可能性

である。

A と B の比較は特に小さく明瞭で、raw API と標準 algebra notation のどちらが downstream Euclidean proof を簡潔にするかを測りやすい。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

正本 source では次の並びを確認した。

```lean
def goldenQuotient (x y : GoldenInt) : GoldenInt :=
  ⟨round (goldenQuotientCoords x y).1,
    round (goldenQuotientCoords x y).2⟩

def goldenRemainder (x y : GoldenInt) : GoldenInt :=
  x - goldenMul (goldenQuotient x y) y

theorem goldenQuotient_zero (x : GoldenInt) :
    goldenQuotient x 0 = 0 := by
  ...
```

さらに後続の `goldenRemainder_norm_rat_identity` と `golden_remainder_size_lt` が本定義を直接展開し、最終 `goldenEuclideanDomain` instance の `remainder` field に登録している。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本定義に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0222 `goldenQuotient_zero`** である。

```lean
theorem goldenQuotient_zero (x : GoldenInt) :
    goldenQuotient x 0 = 0 := by
  ext <;> simp [goldenQuotient, goldenQuotientCoords,
    goldenQuotientNumerator, goldenConj, goldenMul, goldenNorm]
```

0220–0221 で quotient / remainder の全域関数が揃ったので、0222 はまず divisor が `0` の場合に quotient が `0` へ正規化されることを保証する。これは最終 `EuclideanDomain` instance の `quotient_zero` field に直接入る仕様 theorem である。
