# 0321 — `GoldenZeroSectorCandidate.B0_pos`

## 宣言種別

これは **`theorem`** である。

0317 `GoldenZeroSectorCandidate.B0` で導入した upper inversion factor の自然数代表 $B_0$ が、実際にゼロではなく正の自然数であることを明示する positivity bridge である。0320 `A0_pos` の upper-factor 側の対称版にあたる。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

theorem B0_pos (p : GoldenZeroSectorCandidate) : 0 < p.B0 := by
  by_contra hpos
  have hzero : p.B0 = 0 := Nat.eq_zero_of_not_pos hpos
  have hcast := p.B0_cast
  rw [hzero] at hcast
  norm_num at hcast
  have hBpos := p.B_pos
  omega
```

型は

```lean
0 < p.B0
```

であり、順序は `ℕ` 上の strict order である。ここで `p.B0 : ℕ` は signed upper inversion factor `zeroSectorB p.r p.s p.d : ℤ` の `natAbs` として定義されている。

## 数学的主張

0317 では

```lean
def B0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorB p.r p.s p.d).natAbs
```

と定義され、0313 `B_pos` により

$$
0<B
$$

が証明済みである。また 0319 `B0_cast` では

$$
(B_0:\mathbb Z)=B
$$

を得ている。

したがって $B_0=0$ を仮定すると、整数へ cast した後も $B=0$ となり、$B>0$ に矛盾する。ゆえに

$$
B_0>0.
$$

本 theorem は、この事実を後続の自然数上の factor arithmetic で直接利用できる named theorem として固定する。

## 証明全体での役割

zero-sector inversion では signed integer factor

$$
A=U-W,\qquad B=U+W
$$

について既に

$$
AB=4Q^5,
$$

$$
B-A=8d^5,
$$

$$
0<A<B
$$

が得られている。

0316–0319 では

$$
A_0=|A|,\qquad B_0=|B|,
$$

$$
(A_0:\mathbb Z)=A,\qquad(B_0:\mathbb Z)=B
$$

という `ℤ` から `ℕ` への bridge を構築した。0320 `A0_pos` と本 0321 `B0_pos` により

$$
0<A_0,\qquad0<B_0
$$

が揃う。

この直後の 0322 `A0_mul_B0` は signed product identity を自然数へ移し、

$$
A_0B_0=4Q^5
$$

を得る。したがって本 theorem は、自然数 factorization phase に入る直前に upper factor の非零性・正性を API として確定する位置にある。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate.B0`

```lean
def B0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorB p.r p.s p.d).natAbs
```

ゴールの対象を定義する。現行 proof はこの定義を直接 `unfold` せず、`B0_cast` を介して扱う。

### `GoldenZeroSectorCandidate.B0_cast`

0319 で証明済みの

```lean
theorem B0_cast (p : GoldenZeroSectorCandidate) :
    (p.B0 : ℤ) = zeroSectorB p.r p.s p.d := by
  exact Int.ofNat_natAbs_of_nonneg p.B_pos.le
```

である。自然数代表 $B_0$ と signed integer factor $B$ を equality で結ぶ。

### `GoldenZeroSectorCandidate.B_pos`

0313 で得た

$$
0<B
$$

である。本 theorem の最後で `have hBpos := p.B_pos` として導入され、$B=0$ との矛盾を閉じる。

### `Nat.eq_zero_of_not_pos`

自然数 $n$ について `¬ 0 < n` なら `n = 0` を返す Mathlib lemma である。本 theorem では contradiction hypothesis から

```lean
have hzero : p.B0 = 0 := Nat.eq_zero_of_not_pos hpos
```

を得る。

## 証明の流れ

1. `by_contra hpos` で `¬ 0 < p.B0` を仮定する。
2. 自然数では非正ならゼロなので、`Nat.eq_zero_of_not_pos hpos` から `p.B0 = 0` を得る。
3. `p.B0_cast` を `hcast` として取得し、$(B_0:\mathbb Z)=B$ を保持する。
4. `rw [hzero] at hcast` により左辺の $B_0$ をゼロへ書き換える。
5. `norm_num at hcast` で `(0 : ℕ)` の `ℤ` cast などを簡約し、実質的に $0=B$ という情報へ正規化する。
6. `p.B_pos` から $0<B$ を取得する。
7. `omega` が $B=0$ と $0<B$ の矛盾を閉じる。

数学的には非常に短い議論だが、Lean では `ℕ` 上の positivity と `ℤ` 上の factor positivity の型境界を明示的に越える必要があるため、この bridge が重要になる。

## Lean 固有の処理

### `by_contra`

自然数の正性を直接構成する代わりに否定を仮定する。`ℕ` では負値がないため、否定仮定を即座に零 equality へ落とせる。

### `rw ... at ...`

```lean
rw [hzero] at hcast
```

はゴールではなく局所仮定 `hcast` の内部のみを書き換える。自然数側で得た `B0 = 0` を、整数側の cast equality に局所輸送している。

### `norm_num`

書き換え後に残る自然数ゼロの整数 cast 等を簡約する。ここで新たな数論的内容を証明しているわけではなく、後段の線形算術 solver に適した形へ正規化している。

### `omega`

最終段階では非線形な fifth power や factorization は既に theorem API の背後に隠れており、必要なのは $B=0$ と $0<B$ の線形順序矛盾だけである。`omega` はこの Presburger arithmetic を閉じる。

## 冗長・重複箇所

0320 `A0_pos` と本 theorem はほぼ完全に対称である。差は

- `A0` ↔ `B0`
- `A0_cast` ↔ `B0_cast`
- `A_pos` ↔ `B_pos`

だけであり、proof script の形は同一である。

従って generic helper を用いて重複を減らすことは理論上可能である。しかし、lower / upper factor の positivity をそれぞれ named theorem として保持すると、後続 proof で dot notation を使いやすく、エラーメッセージも局所化しやすい。API の意味付けとしては現行の重複には合理性がある。

また `have hBpos := p.B_pos` は短縮できる可能性があるが、現行形は「cast から零 equalityを得る段階」と「元の signed positivity を投入する段階」を分離して読みやすくしている。

## 最適化候補

`B0` は `natAbs B` そのもので、既に `B_pos` があるため、Mathlib の `natAbs` positivity / nonzero lemma を直接利用すれば、`B0_cast` を経由せず短い proof にできる可能性がある。概念的には

```lean
  unfold B0
  -- p.B_pos から zeroSectorB ... ≠ 0 を得る
  -- natAbs の正性 lemma を適用
```

という経路である。

ただし本作業では Lean build を行わないため、利用可能な lemma の正確な名称・引数順は **未検証** である。

また現行 API を維持したまま、`B0_cast` と `B_pos` を `omega` に直接渡して `by_contra` 以下を短縮できる可能性もあるが、これも未検証である。

短さだけなら direct `natAbs` proof に分がある可能性がある一方、現行 proof は直前に整備した `B0_cast` を実際に消費するため、自然数代表の correctness bridge を利用する構造が明瞭である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem が直接利用する Mathlib 側の主要要素は

- `Nat.eq_zero_of_not_pos`
- `norm_num` tactic
- `omega` tactic
- `ℕ` から `ℤ` への coercion
- 自然数・整数の順序基盤

である。`B0`, `B0_cast`, `B_pos` は project upstream declarations である。

本 theorem 単体であれば `Mathlib` 全体より狭い import にできる可能性が高く、`Mathlib.Tactic.Omega`、`Mathlib.Tactic.NormNum` と自然数・整数 cast/order 関係の module が候補になる。ただし standalone 全体の dependency closure を含めた **正確な最小 import 集合は Lean build なしには確認していない**。従って import 縮小は未検証候補として扱う。

## Comparator challenge 化の可否

**可能。中級寄りの小型 Lean proof challenge に適する。**

比較候補は

1. 現行の `B0_cast` → contradiction → `norm_num` → `omega` 経路
2. `natAbs` positivity lemma を直接使う経路
3. `B0_cast` を維持しつつ tactic 数を減らす経路
4. 0320 `A0_pos` と共通 helper を作る経路

である。

評価軸としては proof の短さだけでなく、既存 API の再利用、`ℕ` / `ℤ` 境界の明示性、Mathlib lemma への結合度、対称な lower / upper API の可読性、将来の定義変更への耐性を見るのがよい。

## PDF との照合

対象 branch の repository tree には既存の日英 PDF

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

ただし GitHub コネクタの通常の text fetch は binary PDF 本文を返さないため、本実行では 0321 `B0_pos` に対応する具体的ページ・節・式番号を直接確認できていない。従って PDF 上の位置は **未確認** とし、推測していない。

本解説の Lean code、宣言順、`B0_cast` / `B_pos` への依存、直後の `A0_mul_B0` は、最新 branch の `Flt5DkMath/FLT5StandAlone.lean` を正本として確認した。

## 次に読むべき宣言

次の宣言は 0322 `GoldenZeroSectorCandidate.A0_mul_B0`、種別は **`theorem`** である。

Lean 正本では本 theorem の直後に

```lean
/-- Natural product identity inherited from the positive integer factors. -/
theorem A0_mul_B0 (p : GoldenZeroSectorCandidate) :
    p.A0 * p.B0 = 4 * zeroSectorQ p.c ^ 5 := by
  have hprod := p.factor_product
  rw [← p.A0_cast, ← p.B0_cast] at hprod
  exact_mod_cast hprod
```

と続く。

0320–0321 で $A_0,B_0$ の正性が揃い、0322 から signed integer factor identities を自然数 factorization arithmetic として再構成する段階へ進む。
