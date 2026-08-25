# 0220 — `goldenQuotient`

## Lean の型

```lean
/-- The nearest integral golden quotient. -/
def goldenQuotient (x y : GoldenInt) : GoldenInt :=
  ⟨round (goldenQuotientCoords x y).1,
    round (goldenQuotientCoords x y).2⟩
```

これは `theorem` ではなく `def` であり、0219 `goldenQuotientCoords` が与える黄金基底上の有理商座標を、それぞれ最近接整数へ丸めて `GoldenInt` に戻す。

## 数学的主張・宣言の意味

`x=a+bφ`、`y=c+dφ` とする。0219 では、非零 `y` について数学的に

$$
\frac{x}{y}=A+B\varphi
$$

と読める有理座標

$$
(A,B)=\operatorname{goldenQuotientCoords}(x,y)
$$

を構成した。

本定義は

$$
q=\operatorname{round}(A)+\operatorname{round}(B)\varphi
$$

を `GoldenInt` の quotient として採用する。

したがって `goldenQuotient` は厳密な体上の商そのものではなく、黄金整数格子 $\mathbb Z^2$ 上で有理商 $(A,B)\in\mathbb Q^2$ に最も近い格子点を、各座標の最近接整数丸めによって選ぶ離散化操作である。

Mathlib の `round` により各座標について

$$
|A-\operatorname{round}(A)|\le\frac12,
$$

$$
|B-\operatorname{round}(B)|\le\frac12
$$

が得られるため、quotient error は square fundamental cell $[-1/2,1/2]^2$ に入る。

## 証明全体での役割

`GoldenEuclidean.lean` の中心目的は `GoldenInt` に norm-Euclidean division を構成することである。その流れは、

1. `goldenQuotientCoords` で正確な有理商を黄金基底座標にする。
2. **本 `goldenQuotient` で二座標を最近接整数へ丸める。**
3. 0221 `goldenRemainder` で

$$
r=x-qy
$$

を定義する。
4. 丸め誤差が $[-1/2,1/2]^2$ に入ることと、0213–0214 の

$$
|u^2+uv-v^2|<1
$$

を組み合わせる。
5. `golden_remainder_size_lt` で

$$
E(r)<E(y)
$$

という strict Euclidean decrease を得る。
6. 最終的に `goldenEuclideanDomain : EuclideanDomain GoldenInt` の `quotient` field に本定義をそのまま登録する。

正本 source では実際に

```lean
noncomputable instance goldenEuclideanDomain : EuclideanDomain GoldenInt where
  quotient := goldenQuotient
  quotient_zero := goldenQuotient_zero
  remainder := goldenRemainder
  ...
```

と使われるため、本定義は補助関数ではなく完成した Euclidean-domain instance の quotient algorithm そのものである。

## 直接依存する定義・補題

直接依存するのは次の定義・標準 API である。

- `GoldenInt`
- 0219 `goldenQuotientCoords`
- Mathlib の `round : ℚ → ℤ`
- `GoldenInt` の structure constructor

本宣言自体は `def` なので proof script はない。

数学的背景としては、

- 0211 `exists_int_near_rat`
- 0212 `exists_goldenRat_near_int`
- 0213 `goldenRat_norm_abs_le_five_sixteen`
- 0214 `goldenRat_norm_abs_lt_one`

が最近接整数丸めと fundamental-cell contraction を保証する。

依存の概念図は

$$
\operatorname{goldenQuotientCoords}(x,y)=(A,B)\in\mathbb Q^2
\longrightarrow
(\operatorname{round}A,\operatorname{round}B)\in\mathbb Z^2
\longrightarrow
q\in\mathbb Z[\varphi]
$$

である。

## 構築の流れ

定義は二座標を独立に丸めるだけである。

```lean
def goldenQuotient (x y : GoldenInt) : GoldenInt :=
  ⟨round (goldenQuotientCoords x y).1,
    round (goldenQuotientCoords x y).2⟩
```

1. `goldenQuotientCoords x y : GoldenRat` を計算する。
2. `.1` で `1` 基底方向の有理座標を取り出す。
3. `round` で整数へ丸める。
4. `.2` で `φ` 基底方向について同じことを行う。
5. 二整数を `⟨_, _⟩ : GoldenInt` として再構成する。

ここで二座標を同時最適化する格子探索は行っていない。黄金ノルムの fundamental cell estimate が、この単純な coordinatewise rounding だけで strict contraction を得るように設計されている。

## Lean 固有の処理

### 1. `round` の戻り値は整数

`goldenQuotientCoords x y` の各成分は `ℚ` だが、`round` の結果は `ℤ` なので、そのまま `GoldenInt` の `fst` / `snd` field に入る。

### 2. quotient は total function

0219 と同様、本定義にも `y ≠ 0` の仮定はない。したがって `goldenQuotient x 0` も定義される。

これは EuclideanDomain の quotient operation を全域関数として供給するために重要であり、直後の theorem

```lean
theorem goldenQuotient_zero (x : GoldenInt) :
    goldenQuotient x 0 = 0 := by
  ...
```

が zero divisor case の挙動を別途保証する。

### 3. `round` は noncomputable 問題を表面化させない

本 `def` 自体は通常の定義として記述されるが、最終的な EuclideanDomain instance は source 上 `noncomputable instance` として構築される。quotient algorithm の論理的存在・仕様と、計算可能性の属性を分離している。

### 4. projection API が後続 proof にそのまま現れる

`golden_remainder_size_lt` では

```lean
let A := (goldenQuotientCoords x y).1
let B := (goldenQuotientCoords x y).2
have hA : |A - round A| ≤ (1 : ℚ) / 2 := abs_sub_round A
have hB : |B - round B| ≤ (1 : ℚ) / 2 := abs_sub_round B
```

と、本定義の二つの `round` が生む誤差を直接評価する。

## 冗長・重複箇所

0212 `exists_goldenRat_near_int` は既に任意の `GoldenRat` に対して近い整数二座標の存在を証明しているが、本定義はその existential theorem を利用せず、具体的 witness として `round` を直接二回書いている。

これは論理的には軽い重複だが、EuclideanDomain の quotient には具体的関数が必要なので、単なる存在 theorem では足りない。むしろ0212は幾何的事実の説明用、0220は canonical witness の実装用という役割分担である。

また `(goldenQuotientCoords x y).1` と `.2` が後続で頻繁に現れるため、局所変数 `A`,`B` や専用 projection 名を使うと proof readability が上がる可能性がある。

## 最適化候補

1. **専用 rounding helper を定義する**

```lean
def goldenRound (x : GoldenRat) : GoldenInt :=
  ⟨round x.1, round x.2⟩
```

として、`goldenQuotient x y := goldenRound (goldenQuotientCoords x y)` と分離する案がある。

2. **fundamental-cell certificate と quotient を bundle する**

丸めた quotient と同時に二つの `≤ 1/2` certificate を返す構造を作れば、後続 proof で `abs_sub_round` を再取得する必要を減らせる。ただし quotient API が重くなる。

3. **より一般の quadratic lattice rounding へ抽象化する**

二次環一般で「有理 quotient coordinates → 最近接整数格子点」という構造を共通化し、golden case では norm-cell bound のみ特殊化する余地がある。

4. **coordinatewise rounding と真の norm-nearest lattice point を比較する**

現行法は各座標を独立に丸める。黄金ノルムに対して最も小さい remainder norm を与える格子点を直接探索する方式との比較は可能だが、現行法は $5/16<1$ を既に満たすため Euclidean-domain 証明には十分である。

5. **zero denominator branch を明示した quotient と比較する**

`if y = 0 then 0 else ...` とする設計も可能だが、現行の rational division の totality と `goldenQuotient_zero` theorem の分離の方が定義は簡潔である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本定義単独で直接必要なのは主に、

- `ℚ` と `ℤ`
- `round`
- `Prod` projection
- project-local `GoldenInt`, `GoldenRat`, `goldenQuotientCoords`

である。

本 `def` 自身は tactic を使わない。

しかし `GoldenEuclidean.lean` 全体では `abs_sub_round`, `nlinarith`, `field_simp`, `ring`, `Int.natAbs`, `measure`, `EuclideanDomain` などを利用するため、module の最小 import はかなり広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 coordinatewise `round`
- B: `goldenRound : GoldenRat → GoldenInt` helper を介す設計
- C: quotient と rounding-error certificate を bundle する設計
- D: norm-nearest lattice point を探索する方式
- E: 一般 quadratic-order rounding framework の特殊化

比較軸は、

- Euclidean decrease proof の短さ
- quotient 定義の透明性
- downstream `simp` / rewrite の負担
- 計算可能性
- proof certificate の再利用性
- 一般化可能性

である。

特に A と C の比較は、「軽量な quotient 関数」と「証明 certificate を同伴する quotient」の trade-off を測るよい Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

正本 source では、

```lean
def goldenQuotientCoords ...

def goldenQuotient (x y : GoldenInt) : GoldenInt :=
  ⟨round (goldenQuotientCoords x y).1,
    round (goldenQuotientCoords x y).2⟩

def goldenRemainder (x y : GoldenInt) : GoldenInt :=
  x - goldenMul (goldenQuotient x y) y
```

という順序を確認した。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本定義に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0221 `goldenRemainder`** である。

```lean
/-- The residual after nearest-lattice normalization. -/
def goldenRemainder (x y : GoldenInt) : GoldenInt :=
  x - goldenMul (goldenQuotient x y) y
```

0220 で離散 quotient `q` が確定したので、0221 は

$$
r=x-qy
$$

を黄金整数環内部で定義する。ここから quotient/remainder identity と norm contraction を経て、Euclidean-domain の除法仕様が完成していく。