# 0320 — `GoldenZeroSectorCandidate.A0_pos`

## 宣言種別

これは **`theorem`** である。

0316 `GoldenZeroSectorCandidate.A0` で導入した lower inversion factor の自然数代表 $A_0$ が、実際にゼロではなく正の自然数であることを明示する positivity bridge である。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- The natural representatives are both positive. -/
theorem A0_pos (p : GoldenZeroSectorCandidate) : 0 < p.A0 := by
  by_contra hpos
  have hzero : p.A0 = 0 := Nat.eq_zero_of_not_pos hpos
  have hcast := p.A0_cast
  rw [hzero] at hcast
  norm_num at hcast
  have hApos := p.A_pos
  omega
```

型は

```lean
0 < p.A0
```

であり、順序は `ℕ` 上の strict order である。ここで `p.A0 : ℕ` は signed lower inversion factor `zeroSectorA p.r p.s p.d : ℤ` の `natAbs` として定義されている。

## 数学的主張

0316 で

```lean
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs
```

と定義され、0314 `A_pos` では

$$
0<A
$$

が既に証明されている。また 0318 `A0_cast` により

$$
(A_0:\mathbb Z)=A
$$

が得られている。

したがって、もし $A_0=0$ なら整数への cast 後も $A=0$ となり、$A>0$ に矛盾する。ゆえに

$$
A_0>0.
$$

本 theorem はこの当然だが重要な事実を、後続の自然数算術で直接利用できる形に固定する。

## 証明全体での役割

zero-sector inversion の signed integer phase では、これまでに

$$
AB=4Q^5,
$$

$$
B-A=8d^5,
$$

$$
A+B=2U,
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

という signed / natural 間の橋を構築した。本 0320 は、その自然数代表が単に型変換された値であるだけでなく、後続の数論に必要な **非零の正因子** であることを明示する最初の theorem である。

直後の `B0_pos` と合わせて

$$
0<A_0,\qquad0<B_0
$$

が揃い、その後の `A0_mul_B0`、`B0_eq_A0_add`、互いに素性・可除性・冪分解を自然数世界で扱うための positivity 前提が整う。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate.A0`

```lean
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs
```

ゴールの対象そのものを定義する。ただし現行 proof は `A0` を直接 unfold せず、後述の `A0_cast` を介して扱う。

### `GoldenZeroSectorCandidate.A0_cast`

0318 で証明済みの

```lean
theorem A0_cast (p : GoldenZeroSectorCandidate) :
    (p.A0 : ℤ) = zeroSectorA p.r p.s p.d := by
  exact Int.ofNat_natAbs_of_nonneg p.A_pos.le
```

を `have hcast := p.A0_cast` で取得する。これが自然数 $A_0$ と signed integer factor $A$ の equality bridge である。

### `GoldenZeroSectorCandidate.A_pos`

0314 で得られた

$$
0<A
$$

である。proof の最後で `have hApos := p.A_pos` として導入し、$A=0$ との矛盾を `omega` に解かせる。

### `Nat.eq_zero_of_not_pos`

自然数 $n$ について `¬ 0 < n` なら `n = 0` を返す Mathlib lemma。本 theorem では contradiction hypothesis `hpos` から

```lean
have hzero : p.A0 = 0 := Nat.eq_zero_of_not_pos hpos
```

を構成する。

## 証明または構築の流れ

1. `by_contra hpos` により `¬ 0 < p.A0` を仮定する。
2. 自然数では非正ならゼロなので、`Nat.eq_zero_of_not_pos hpos` から `p.A0 = 0` を得る。
3. `p.A0_cast` を取得し、$(A_0:\mathbb Z)=A$ を保持する。
4. `rw [hzero] at hcast` により cast equality の左辺をゼロへ書き換える。
5. `norm_num at hcast` で自然数ゼロの整数 cast などを正規化し、実質的に $0=A$ という情報にする。
6. `p.A_pos` から $0<A$ を取得する。
7. `omega` が $A=0$ と $A>0$ の矛盾を閉じる。

数学的内容は「正の整数と同一視される自然数は正」という一点だが、Lean では `ℕ` / `ℤ` の型境界を明示的に越えるため、この順序になっている。

## Lean 固有の処理

### `by_contra` と自然数の零化

ゴール `0 < p.A0` を直接示す代わりに否定を仮定する。`ℕ` では負の値が存在しないため、`¬ 0 < p.A0` を `p.A0 = 0` へ変換できる。この離散順序の性質を `Nat.eq_zero_of_not_pos` が担当する。

### 型境界を `A0_cast` で越える

`A0` の `natAbs` 定義を再展開するのではなく、直前に整備した public API `A0_cast` を再利用している。これにより positivity proof が `natAbs` の内部 lemma に直接依存しない。

### `rw ... at ...`

```lean
rw [hzero] at hcast
```

はゴールではなく局所仮定 `hcast` の内部だけを書き換える。自然数側で得た `A0 = 0` を整数 equality に輸送するための局所的処理である。

### `norm_num`

`rw` 後に残る `(0 : ℕ)` の `ℤ` cast などの数値表現を簡約する。ここでは新しい数学を証明するのではなく、`omega` が扱いやすい正規形へ整える役割である。

### `omega`

最終的な Presburger arithmetic の矛盾、すなわち $A=0$ と $0<A$ を自動で閉じる。指数や非線形多項式はこの段階では既に theorem API の背後に隠れており、`omega` が扱うのは線形な順序関係だけである。

## 冗長・重複箇所

直後の `B0_pos` は `A0_pos` とほぼ完全に対称な proof であり、

- `A0` ↔ `B0`
- `A0_cast` ↔ `B0_cast`
- `A_pos` ↔ `B_pos`

だけが異なる。したがってコード上は明確な重複がある。

ただし lower / upper factor を named theorem として別々に保持することは、後続の証明で dot notation を使いやすくし、エラー時にもどちらの positivity が不足しているか判別しやすい。generic helper 化の利益は限定的で、この重複は API の意味付けとして合理的である。

また、`hcast` を `norm_num` した後に `hApos` を別名で導入している点は、より短い tactic proof に縮められる可能性があるが、現行形は証明の論理段階を読みやすく保っている。

## 最適化候補

`A0` が `natAbs A` そのものであり、既に `A_pos` があるため、Mathlib に適合する `natAbs` positivity lemma を直接使えば、より短い proof にできる可能性がある。概念的には

```lean
  unfold A0
  -- `A_pos` から `zeroSectorA ... ≠ 0` を得て
  -- `natAbs` の正性 lemma を適用する
```

という経路である。

ただし本実行では Lean build を行わない条件なので、利用可能な lemma の正確な名称・引数順・必要 import は **未検証** とする。

別案として、現行 API を維持したまま `A0_cast` と `A_pos` から `omega` 一発で閉じられるか、`norm_num` を省けるかも Comparator 向けの最適化候補である。しかしこれも build 未実施のため確定しない。

現行 proof の利点は、直前に導入した `A0_cast` を実際に消費し、自然数代表の correctness bridge が有効であることを示している点にある。短さだけを目的に direct `natAbs` proof へ変える必然性はない。

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
- `ℕ` から `ℤ` への coercion と自然数・整数の順序基盤

である。`GoldenZeroSectorCandidate.A0`, `A0_cast`, `A_pos` は project upstream declarations である。

この theorem 単体なら `Mathlib` 全体より狭い import にできる可能性が高く、特に自然数順序・整数 cast と `Mathlib.Tactic.Omega` / `Mathlib.Tactic.NormNum` に関係する module が候補になる。しかし generated standalone 全体の import closure を含めた **正確な最小 import 集合は Lean build なしには確認していない**。従って具体的な import 縮小は未検証候補とする。

## Comparator challenge 化の可否

**可能。中級寄りの小型 Lean proof challenge に適する。**

比較対象として、

1. 現行の `A0_cast` → contradiction → `norm_num` → `omega` 経路
2. `natAbs` の positivity lemma を直接使う経路
3. `A0_cast` を維持しつつ tactic 数を減らす経路
4. `A0_pos` / `B0_pos` を共通 helper へ抽象化する経路

を並べられる。

評価軸は proof term の短さだけでなく、既存 API の再利用、型境界の明示性、Mathlib lemma への結合度、将来の定義変更への耐性とするのがよい。

## PDF との照合

対象 branch の repository tree には既存の日英 PDF

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

ただし GitHub コネクタは binary PDF 本文を通常の text fetch として返さず、本実行でも公開 raw PDF 本文の取得に成功しなかった。そのため、0320 `A0_pos` に対応する具体的ページ・節・式番号は **未確認** であり、推測していない。

本解説の Lean code、宣言順、`A0_cast` / `A_pos` への依存、直後の `B0_pos` は、最新 branch の `Flt5DkMath/FLT5StandAlone.lean` を正本として確認した。

## 次に読むべき宣言

次の宣言は 0321 `GoldenZeroSectorCandidate.B0_pos`、種別は **`theorem`** である。

Lean 正本では `A0_pos` の直後に

```lean
theorem B0_pos (p : GoldenZeroSectorCandidate) : 0 < p.B0 := by
  by_contra hpos
  have hzero : p.B0 = 0 := Nat.eq_zero_of_not_pos hpos
  have hcast := p.B0_cast
  rw [hzero] at hcast
  norm_num at hcast
  have hBpos := p.B_pos
  omega
```

と続く。

0320 と 0321 で自然数代表の両方について positivity が確定し、その後の自然数 factorization arithmetic へ進む。