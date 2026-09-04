# 0293 — `GoldenZeroSectorCandidate.s_neg`

## 宣言種別

これは **`theorem`** である。

0291 `GoldenZeroSectorCandidate.product_neg` が与える積の厳密な負性と、0289 `goldenFifthSndFactor_nonneg` が与える四次因子の非負性から、zero-sector candidate の visible coordinate `s` の符号を負に固定する。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- The visible zero-sector coordinate has the forced negative sign. -/
theorem s_neg (p : GoldenZeroSectorCandidate) : p.s < 0 := by
  rcases mul_neg_iff.mp p.product_neg with h | h
  · exact (not_lt_of_ge (goldenFifthSndFactor_nonneg p.r p.s) h.2).elim
  · exact h.1
```

結論はそのまま

$$
p.s<0
$$

である。

ここで

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s)
$$

と書けば、既知の情報は

$$
p.s\,H(p.r,p.s)<0,
\qquad
H(p.r,p.s)\ge0
$$

であり、本 theorem はそこから `p.s < 0` を抽出する。

## 数学的意味

実数・整数の順序では、積が負なら二因子の符号は逆である。Lean の `mul_neg_iff` はこの場合分けを明示的な論理和として返す。

概念的には

$$
ab<0
\iff
(a>0\land b<0)\lor(a<0\land b>0).
$$

ここで

$$
a=p.s,
\qquad
b=H(p.r,p.s)
$$

とする。

第一の可能性

$$
p.s>0,
\qquad
H(p.r,p.s)<0
$$

は、0289 で既に証明済みの

$$
H(p.r,p.s)\ge0
$$

と矛盾する。

したがって残るのは第二の可能性

$$
p.s<0,
\qquad
H(p.r,p.s)>0
$$

だけであり、特に

$$
p.s<0
$$

が従う。

なお直前の 0292 `H_pos` は既に

$$
H(p.r,p.s)>0
$$

まで証明しているが、現行 Lean コードはそれを直接参照せず、より弱い一般定理 0289 `goldenFifthSndFactor_nonneg` だけを使って不要な符号枝を排除している。この点は後述する冗長・最適化候補として重要である。

## 証明全体での役割

zero-sector inversion では絶対値で得られた tenth-power split を、符号付き整数等式へ戻さなければならない。

0290 `GoldenZeroSectorCandidate` は visible coordinate について

$$
|s|=5^6c^{10}
$$

に対応する `s_natAbs_eq` を保持している。しかし絶対値だけでは

$$
s=+5^6c^{10}
$$

なのか

$$
s=-5^6c^{10}
$$

なのか決まらない。

その符号を決定するのが本 theorem である。

前段の符号鎖は

$$
16H=X^4+10X^2s^2+5s^4
\Longrightarrow
H\ge0,
$$

$$
sH=-5^6a^{10}<0,
$$

したがって

$$
s<0
$$

となる。

この符号確定により、後続では `s_natAbs_eq` と組み合わせて absolute-value information を signed equality に戻せる。直後の 0294 `GoldenZeroSectorCandidate.c_pos` はまず $c\neq0$ を確保する段階であり、その後の zero-sector inversion で tenth-power scale を正の量として扱うための準備となる。

したがって 0293 は、**符号を失った自然数絶対値データと、元の整数座標を再接続するための sign-recovery theorem** である。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate`

0290 の `structure`。本 theorem はその整数座標

```lean
p.r : ℤ
p.s : ℤ
```

を使用する。

### `GoldenZeroSectorCandidate.product_neg`

0291 の theorem。

```lean
theorem product_neg (p : GoldenZeroSectorCandidate) :
    p.s * goldenFifthSndFactor p.r p.s < 0
```

本証明の主要入力であり、`p.product_neg` という dot notation で取得する。

### `goldenFifthSndFactor_nonneg`

0289 の theorem。

```lean
theorem goldenFifthSndFactor_nonneg (r s : ℤ) :
    0 ≤ goldenFifthSndFactor r s
```

積が負である場合のうち、四次因子が負になる枝を排除する。

### `mul_neg_iff`

積の負性を二つの符号配置へ分解する order lemma。

現行コードでは

```lean
mul_neg_iff.mp p.product_neg
```

により論理和を得て、`rcases ... with h | h` で二枝に分けている。

### `not_lt_of_ge`

非負性

```lean
0 ≤ goldenFifthSndFactor p.r p.s
```

と、第一枝から得られる負性を矛盾させる。

### `False.elim` / `.elim`

```lean
(not_lt_of_ge (...) h.2).elim
```

では矛盾から任意の結論 `p.s < 0` を得る。Lean では `False.elim` が dot notation 的に `.elim` として使われている。

## 証明の流れ

### 1. 負積を符号の場合分けへ変換する

```lean
rcases mul_neg_iff.mp p.product_neg with h | h
```

0291 の

```lean
p.product_neg :
  p.s * goldenFifthSndFactor p.r p.s < 0
```

を `mul_neg_iff.mp` に通す。

数学的には

$$
(p.s>0\land H<0)
\lor
(p.s<0\land H>0)
$$

という二枝である。

### 2. 第一枝を四次因子の非負性で排除する

```lean
· exact (not_lt_of_ge (goldenFifthSndFactor_nonneg p.r p.s) h.2).elim
```

第一枝では `h.2` が四次因子の厳密な負性を与える。一方 0289 は同じ四次因子が非負であると証明している。

したがって

$$
H\ge0
\quad\text{and}\quad
H<0
$$

となって矛盾する。この枝からは `False.elim` により目標を閉じる。

### 3. 第二枝から `s < 0` を直接取り出す

```lean
· exact h.1
```

第二枝では第一成分がそのまま

```lean
h.1 : p.s < 0
```

なので終了する。

## Lean 固有の処理

本 theorem は代数展開も数値計算も行わず、order API の論理構造だけで証明されている。

第一の要点は、`mul_neg_iff` が積の負性を単一の結論ではなく **論理和** として返すことである。そのため `rcases` を使って二つの符号配置を明示的に処理する。

第二の要点は、`product_neg` が structure field ではなく namespace 内 theorem であっても、第一引数が `p : GoldenZeroSectorCandidate` なので

```lean
p.product_neg
```

と dot notation で呼べることである。

第三の要点は、第一枝で目標 `p.s < 0` を直接構築しないことである。代わりに

```lean
not_lt_of_ge ... h.2
```

で `False` を作り、`.elim` でその不可能な枝を閉じる。

この証明には `ring`, `nlinarith`, `omega`, `positivity`, `norm_num`, `exact_mod_cast` といった tactic は必要ない。

## 冗長・重複箇所

### 0292 `H_pos` との論理的重複

最も目立つ点は、直前の 0292 が既に

```lean
theorem H_pos (p : GoldenZeroSectorCandidate) :
    0 < goldenFifthSndFactor p.r p.s
```

を証明しているにもかかわらず、本 theorem が `p.H_pos` を利用せず、0289 の `goldenFifthSndFactor_nonneg` へ戻っていることである。

数学的には、0292 と 0291 があれば

$$
H>0,
\qquad
sH<0
$$

から直ちに $s<0$ と言える。

ただし現行証明には独立性上の利点がある。本 theorem は 0292 の「strict positivity API」に依存せず、より基礎的な 0289 と 0291 だけで成立する。そのため dependency graph を細く保つという意味では必ずしも悪い重複ではない。

### 二枝のうち一枝は不可能

`mul_neg_iff` の一般形を使うため二枝を処理しているが、この文脈では $H\ge0$ が既知なので、実質的には「右因子が非負で積が負なら左因子は負」という専用 order lemma があれば一段で済む可能性がある。

具体的な Mathlib lemma 名は、この作業では API 探索と Lean build を行っていないため断定しない。

## 最適化候補

### 1. 0292 `H_pos` を使う形

proof dependency を直前の theorem に揃えるなら、`p.H_pos` を利用してより意図の直接的な証明へ変えられる可能性がある。

ただし、利用する正確な order lemma と型が未検証なので、ここでは候補に留める。

### 2. 非負右因子用 lemma の利用

Mathlib に

- `a * b < 0`
- `0 ≤ b`

から `a < 0` を直接返す lemma が存在し、今回の型にそのまま適用できるなら `rcases mul_neg_iff...` を省略できる。

これも最小化候補ではあるが、具体的 lemma 名は未確認である。

### 3. 現行形を維持する価値

Comparator や教材の観点では、現行形は積が負となる二つの符号パターンを可視化するため非常に読みやすい。短さだけを目的に最適化する必要は薄い。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

standalone manifest ではこの宣言を含む領域が元 module

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

に属することを確認できる。

本 theorem 自体が直接必要とする機能は主に

- 整数 `ℤ` の線形順序
- `mul_neg_iff`
- `not_lt_of_ge`
- conjunction / disjunction の分解
- `rcases`
- `False.elim`
- 既存 theorem `GoldenZeroSectorCandidate.product_neg`
- 既存 theorem `goldenFifthSndFactor_nonneg`

である。

`ring`, `nlinarith`, `omega`, `positivity`, `norm_num`, `exact_mod_cast` は本 theorem 自体には不要である。

ただし指定に従って Lean build は行っていないため、`import Mathlib` をどの個別 Mathlib import まで削減できるかは **未検証** であり、最小 import 集合は断定しない。

## Comparator challenge 化の可否

**適している。**

短いが、Comparator challenge として次の能力を評価できる。

1. `p.product_neg` から積の符号情報を取得する。
2. `mul_neg_iff` の論理和を正しく分解する。
3. 0289 の非負性を見つけて不可能な枝を消す。
4. 残った枝から `p.s < 0` を取り出す。
5. 直前の `H_pos` を使う別解と、依存を一段浅くする現行解を比較する。

例えば

```lean
theorem challenge (p : GoldenZeroSectorCandidate) : p.s < 0 := by
  ...
```

として、`product_neg` と `goldenFifthSndFactor_nonneg` の利用を許可する形式が適している。

証明は非常に短いが、order-theoretic API discovery と case analysis が本質なので、判定は **適する** とする。

## PDF との対応

対象 branch の repository tree には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

今回、PDF の raw 直接取得も試みたが、利用可能な取得経路では本文を解析可能な PDF resource として開けなかった。そのため、本 theorem に対応する PDF の具体的ページ・節番号・文言は **未確認** であり、推測しない。

本解説の技術的根拠は、対象 branch の `Flt5DkMath/FLT5StandAlone.lean` にある実宣言と、その直接依存宣言である。

## 次に読むべき宣言

次は 0294 `GoldenZeroSectorCandidate.c_pos` である。種別は **`theorem`**。

正本では `s_neg` の直後に次の docstring とともに置かれている。

```lean
/-- The tenth-power base in the visible coordinate is nonzero. -/
theorem c_pos (p : GoldenZeroSectorCandidate) : 0 < p.c := by
  by_contra hc
  have hc0 : p.c = 0 := Nat.eq_zero_of_not_pos hc
  have hsAbsZero : p.s.natAbs = 0 := by
    simpa [hc0] using p.s_natAbs_eq
  ...
```

0293 で visible coordinate の符号が負に固定された後、0294 では `s_natAbs_eq` と candidate の符号情報を使う後続処理に備え、tenth-power base `c` が 0 ではないこと、すなわち

$$
0<p.c
$$

を確立する段階へ進む。

なお取得できた Lean 正本の検索断片では 0294 の冒頭まで確認できたが、ここでは次宣言の全文を再構成せず、確認できた範囲だけを記載する。
