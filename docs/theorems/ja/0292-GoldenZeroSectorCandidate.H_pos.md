# 0292 — `GoldenZeroSectorCandidate.H_pos`

## 宣言種別

これは **`theorem`** である。

0289 `goldenFifthSndFactor_nonneg` で得た四次因子の非負性と、0291 `GoldenZeroSectorCandidate.product_neg` で得た積の厳密な負性を組み合わせ、zero-sector candidate に現れる四次因子が実際には厳密に正であることを示す。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- The quartic factor in a zero-sector candidate is strictly positive. -/
theorem H_pos (p : GoldenZeroSectorCandidate) :
    0 < goldenFifthSndFactor p.r p.s := by
  have hnonneg := goldenFifthSndFactor_nonneg p.r p.s
  have hne : goldenFifthSndFactor p.r p.s ≠ 0 := by
    intro hzero
    have hpneg := p.product_neg
    rw [hzero, mul_zero] at hpneg
    omega
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)
```

数学的に

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s)
$$

と書けば、定理の結論は

$$
H(p.r,p.s)>0
$$

である。

## 数学的意味

0289 により、任意の整数 $r,s$ に対して

$$
H(r,s)\ge 0
$$

が既に証明されている。

一方、0291 により `p : GoldenZeroSectorCandidate` について

$$
p.s\,H(p.r,p.s)<0
$$

である。

ここでもし

$$
H(p.r,p.s)=0
$$

ならば、積は

$$
p.s\cdot 0=0
$$

となり、0291 の厳密な負性に反する。したがって

$$
H(p.r,p.s)\neq0.
$$

非負であり、かつ 0 ではないので、

$$
H(p.r,p.s)>0
$$

が従う。

したがって本 theorem は、一般的な四次形式の非負性を、zero-sector candidate が持つ追加情報によって **厳密な正性へ強化する定理** である。

## 証明全体での役割

zero-sector inversion では、単に絶対値や偶数冪だけを扱うのではなく、元の符号を確定する必要がある。

0288–0292 の流れは

$$
16H=X^4+10X^2s^2+5s^4
$$

から

$$
H\ge0
$$

を得て、さらに candidate の積等式

$$
sH=-5^6a^{10}<0
$$

を使って

$$
H>0
$$

へ進むものである。

この正性は直後の 0293 `GoldenZeroSectorCandidate.s_neg` の符号判定に使われる。積が負で $H$ が正ならば、残る因子 $s$ は必ず負である。

したがって符号確定鎖は

$$
H\ge0
\longrightarrow
sH<0
\longrightarrow
H>0
\longrightarrow
s<0
$$

となる。

さらに後続の `H_eq_tenth` では、本 theorem の `p.H_pos.le` を使って自然数絶対値を符号なしの整数等式へ戻し、

$$
H(p.r,p.s)=p.d^{10}
$$

を得る。よって 0292 は単なる order lemma ではなく、後続の **absolute-value removal** に必要な符号証明でもある。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate`

0290 で導入された structure。本 theorem は candidate の座標 `p.r`, `p.s` を使い、namespace 内の projection theorem `p.product_neg` を利用する。

### `goldenFifthSndFactor_nonneg`

0289 の theorem。

```lean
theorem goldenFifthSndFactor_nonneg (r s : ℤ) :
    0 ≤ goldenFifthSndFactor r s
```

candidate 固有の仮定を一切使わず、四次因子が常に非負であることを与える。

### `GoldenZeroSectorCandidate.product_neg`

直前の 0291。

```lean
theorem product_neg (p : GoldenZeroSectorCandidate) :
    p.s * goldenFifthSndFactor p.r p.s < 0
```

本 theorem では $H=0$ を排除するための矛盾源として使われる。

### `mul_zero`

仮定

```lean
hzero : goldenFifthSndFactor p.r p.s = 0
```

の下で積を 0 に簡約するために使う。

### `omega`

`hpneg : 0 < 0` に相当する不可能な整数不等式を閉じる。

### `lt_of_le_of_ne`

最後に

$$
0\le H,
\qquad
0\neq H
$$

から

$$
0<H
$$

を構成する。

ここで `hne` は `H ≠ 0` の向きなので、`lt_of_le_of_ne` が要求する `0 ≠ H` に合わせるため `Ne.symm hne` が使われる。

## 証明の流れ

### 1. 一般非負性を取得する

```lean
have hnonneg := goldenFifthSndFactor_nonneg p.r p.s
```

これで

```lean
hnonneg : 0 ≤ goldenFifthSndFactor p.r p.s
```

を得る。

この段階ではまだ $H=0$ の可能性が残っている。

### 2. $H=0$ を仮定して排除する

```lean
have hne : goldenFifthSndFactor p.r p.s ≠ 0 := by
  intro hzero
```

ここから反証法で非零性を示す。

### 3. 0291 の負積を取り出す

```lean
have hpneg := p.product_neg
```

`hpneg` は

```lean
p.s * goldenFifthSndFactor p.r p.s < 0
```

である。

### 4. $H=0$ を積へ代入する

```lean
rw [hzero, mul_zero] at hpneg
```

これにより `hpneg` は数学的には

$$
0<0
$$

という矛盾へ変わる。

### 5. `omega` で矛盾を閉じる

```lean
omega
```

これで $H\neq0$ が確立する。

### 6. 非負 + 非零から正へ

```lean
exact lt_of_le_of_ne hnonneg (Ne.symm hne)
```

`hnonneg : 0 ≤ H` と `Ne.symm hne : 0 ≠ H` を結合して `0 < H` を得る。

## Lean 固有の処理

本 theorem では複雑な代数操作は行わない。Lean 固有の要点は、既存 theorem の型を正確に組み合わせることにある。

第一に、0291 は namespace 内の theorem なので

```lean
p.product_neg
```

という projection-style notation で利用できる。これは structure field ではないが、第1引数が `p : GoldenZeroSectorCandidate` であるため dot notation が働く。

第二に、非零性の向きに注意が必要である。

```lean
hne : H ≠ 0
```

を得た後、`lt_of_le_of_ne hnonneg` が必要とするのは `0 ≠ H` なので、

```lean
Ne.symm hne
```

と反転している。

第三に、矛盾部分では `nlinarith` ではなく `omega` を使用している。`rw [hzero, mul_zero]` の後は代数構造が完全に消え、整数上の不可能な線形不等式だけが残るためである。

## 冗長・重複箇所

証明は短く、重大な冗長性はない。

`rw [hzero, mul_zero] at hpneg` の `mul_zero` は `rw [hzero]` 後の simplification で自動的に処理できる可能性があり、例えば `simpa [hzero] using p.product_neg` のような書き方も考えられる。ただし現行形は「因子を 0 にする → 積を 0 にする」という論理が明示され、教育的には分かりやすい。

また `hne` を別の補題として公開する必要性は低い。後続で必要なのは単なる非零性より強い `H_pos` であり、本 theorem がその最適な API になっている。

## 最適化候補

### 1. `hne` の短縮

例えば概念的には

```lean
have hne : goldenFifthSndFactor p.r p.s ≠ 0 := by
  intro h
  have := p.product_neg
  simp [h] at this
```

のように短く書ける可能性がある。

ただし tactic の simplification 挙動への依存が増えるため、現行の `rw` + `omega` は安定性と可読性の点で良い。

### 2. `pos_of_nonneg_of_ne_zero` 系 lemma の探索

Mathlib に同趣旨のより直接的な order lemma が存在する場合、それを使えば最後の

```lean
lt_of_le_of_ne hnonneg (Ne.symm hne)
```

を意図の分かりやすい名前で置き換えられる可能性がある。

ただし本作業では Lean build や API 探索による検証を行っていないため、具体的な置換 lemma 名は断定しない。

### 3. 0291 と統合しない方がよい

`product_neg` と `H_pos` は連続して使われるが、統合は推奨しにくい。0291 は signed product equation の order projection、0292 は global nonnegativity と candidate-specific negativity の接合という異なる役割を持つ。分離された API の方が後続証明で再利用しやすい。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem が直接必要とする機能は主に

- 整数の線形順序
- `lt_of_le_of_ne`
- equality / disequality と `Ne.symm`
- `mul_zero`
- `omega` tactic
- 既存 theorem `goldenFifthSndFactor_nonneg`
- 既存 theorem `GoldenZeroSectorCandidate.product_neg`

である。

`ring`, `nlinarith`, `positivity`, `norm_num`, `exact_mod_cast` は本 theorem 自体には使われていない。

standalone manifest ではこの部分は元 module `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` に属することを確認できる。しかし今回は Lean build を行わないため、`import Mathlib` をどの個別 import 群まで削減できるかは **未検証** であり、具体的な最小 import は断定しない。

## Comparator challenge 化の可否

**適している。**

短い theorem だが、Comparator challenge としては次の論点がある。

1. 既存の一般 theorem `goldenFifthSndFactor_nonneg` を見つける。
2. dot notation で `p.product_neg` を利用する。
3. $H=0$ を仮定すると負積が 0 になることを示す。
4. 非負 + 非零を正性へ変換する。
5. `H ≠ 0` と `0 ≠ H` の向きを処理する。

例えば

```lean
theorem challenge (p : GoldenZeroSectorCandidate) :
    0 < goldenFifthSndFactor p.r p.s := by
  ...
```

として、0289 と 0291 の利用を許可した proof-hole 問題にするとよい。

証明は短いが、order reasoning と API discovery を評価できるため、判定は **適する** とする。

## PDF との対応

対象 branch の repository tree には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在し、それぞれの blob も確認できる。

今回、PDF の raw 直接取得も試したが、利用可能な取得経路では本文を解析可能な PDF として開けなかった。そのため、本 theorem に対応する PDF の具体的ページ・節番号・文言は **未確認** であり、推測しない。

本解説の技術的根拠は、対象 branch の `Flt5DkMath/FLT5StandAlone.lean` にある実宣言、およびその直前・直後の依存宣言である。

## 次に読むべき宣言

次は 0293 `GoldenZeroSectorCandidate.s_neg` である。種別は **`theorem`**。

```lean
/-- The visible zero-sector coordinate has the forced negative sign. -/
theorem s_neg (p : GoldenZeroSectorCandidate) : p.s < 0 := by
  rcases mul_neg_iff.mp p.product_neg with h | h
  · exact (not_lt_of_ge (goldenFifthSndFactor_nonneg p.r p.s) h.2).elim
  · exact h.1
```

0291 で積 $sH$ が負であることが分かり、0292 までで $H$ の符号が非負、実際には正であることが確定した。0293 はその符号情報を使って visible coordinate

$$
p.s<0
$$

を確定する。

これにより後続の

$$
p.s=-5^6p.c^{10}
$$

という absolute-value removal へ進む準備が整う。
