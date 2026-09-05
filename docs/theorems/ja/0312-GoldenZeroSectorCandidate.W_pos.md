# 0312 — `GoldenZeroSectorCandidate.W_pos`

## 宣言種別

これは **`theorem`** である。

0311 までで inversion factors `A`,`B` の積・差・和が exact algebraic identities として揃った。本 theorem からは order/positivity phase に入り、まず

$$
W=4d^5>0
$$

を確立する。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- The tenth-power square root contribution is strictly positive. -/
theorem W_pos (p : GoldenZeroSectorCandidate) : 0 < zeroSectorW p.d := by
  unfold zeroSectorW
  have hd : (0 : ℤ) < p.d := by exact_mod_cast p.d_pos
  positivity
```

結論は `ℤ` 上の strict positivity である。

$$
0 < W(d).
$$

`zeroSectorW` の定義は

```lean
def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

すなわち

$$
W(d)=4d^5
$$

である。

## 数学的意味

`GoldenZeroSectorCandidate` は `d_pos : 0 < d` を保持している。従って整数へ埋め込んでも

$$
0<d.
$$

さらに指数 `5` は正なので

$$
d^5>0,
$$

かつ係数 `4` も正であるから

$$
4d^5>0.
$$

したがって

$$
W>0.
$$

本 theorem は新しい数論的内容を導入するものではなく、既に candidate に保存されている `d>0` を inversion coordinate `W` の正値性へ移す order lemma である。

## 証明全体での役割

`W` は

$$
A=U-W,
\qquad
B=U+W
$$

における二因子の半差であり、0310 では

$$
B-A=2W=8d^5
$$

と現れた。

本 theorem により `W>0` が確定するので、後続では `U\ge0` と合わせて

$$
B=U+W>0
$$

を得られる。Lean 正本でも次の宣言 0313 `GoldenZeroSectorCandidate.B_pos` は

```lean
unfold zeroSectorB
linarith [p.U_nonneg, p.W_pos]
```

として本 theorem を直接使用する。

したがって 0312 は exact algebraic phase と factor positivity phase を接続する最初の order bridge である。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate.d_pos`

candidate が保持する

```lean
d_pos : 0 < d
```

である。本 proof の唯一の candidate-specific hypothesis である。

### `zeroSectorW`

```lean
def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

本 theorem はこの定義を展開し、自然数 `d` の正値性を整数式 `4 * (d : ℤ)^5` の正値性へ移す。

### `exact_mod_cast`

`p.d_pos : 0 < p.d` は `ℕ` 上の不等式である一方、`zeroSectorW` の内部では `(p.d : ℤ)` を使う。そのため

```lean
have hd : (0 : ℤ) < p.d := by exact_mod_cast p.d_pos
```

で型境界を越える。

### `positivity`

`hd` を利用して

$$
0<4(d:ℤ)^5
$$

を自動的に閉じる。

## 証明または構築の流れ

1. `unfold zeroSectorW` で目標を

$$
0 < 4 * (p.d : ℤ)^5
$$

へ展開する。
2. `p.d_pos : 0 < p.d` を `exact_mod_cast` により

$$
0 < (p.d : ℤ)
$$

へ移す。
3. `positivity` が正の底の正整数冪と正係数の積を認識する。
4. `0 < zeroSectorW p.d` が閉じる。

## Lean 固有の処理

数学的には `d>0` から `4d^5>0` は即座であるが、Lean では `d : ℕ` と `zeroSectorW d : ℤ` の型差を明示的に越える必要がある。このため `exact_mod_cast` が proof の本質的な Lean-specific step になっている。

一方、冪の正値性や正係数との積については個別に `pow_pos` や `mul_pos` を連鎖せず `positivity` に任せている。これは現行 proof を短く保つ合理的な選択である。

`linarith` や `nlinarith` は不要であり、環恒等式でもないので `ring` も不要である。

## 冗長・重複箇所

proof は 3 行であり局所的な冗長性はほぼない。

類似する positivity lemma が後続に複数存在するため、型 cast を伴う `Nat` から `Int` への正値性移送は繰り返される可能性がある。しかし本 theorem ではその処理は一度だけであり、現時点で専用 helper を導入するほどの重複とは断定できない。

## 最適化候補

`exact_mod_cast` で得る `hd` を明示せず、`positivity` が `p.d_pos` と cast を直接処理できる形が存在する可能性はある。しかし Lean build 禁止条件のため未検証であり、推測に留める。

また `zeroSectorW` の一般 lemma

```lean
theorem zeroSectorW_pos {d : ℕ} (hd : 0 < d) : 0 < zeroSectorW d := ...
```

を candidate 非依存で切り出し、本 theorem を wrapper にする設計も可能である。`GoldenZeroSectorCandidate` の仮定として実際に使うのは `d_pos` だけなので、再利用性の観点では自然な候補である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用している。

本 theorem が直接必要とする機能は少なくとも次である。

- `ℕ` と `ℤ` の cast
- strict order
- 整数の冪と乗算
- `exact_mod_cast`
- `positivity`

`ring`、`omega`、`linarith`、`nlinarith` は本 proof では直接使用しない。

従って `Mathlib` 全体より狭い import に削減できる可能性が高い。ただし正確な最小 import 集合は Lean build を行わない条件のため未確認である。

## Comparator challenge 化の可否

**可能。難度は初級〜初中級。**

数学的内容は単純だが、評価点は Lean の型境界処理にある。

比較候補は次の通り。

- 現行の `exact_mod_cast` + `positivity`。
- `Int.ofNat_pos.mpr` 等の明示的 cast lemma を使う proof。
- `pow_pos` と `mul_pos` を手動で組み立てる proof。
- candidate 非依存の `zeroSectorW_pos` を作り wrapper にする設計。

特に `d_pos : 0 < d` が `ℕ` 上で、目標が `ℤ` 上であることを正しく認識できるかが良い comparator point になる。

## PDF との照合

対象 branch には既存の日英 PDF

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを repository 上で確認した。

ただし GitHub コネクタの通常 text fetch は binary PDF 本文を返さないため、本実行では具体的ページ・節・式番号との直接照合はできていない。その位置については推測しない。

本解説の Lean code、宣言順、直接依存、後続宣言との関係は `Flt5DkMath/FLT5StandAlone.lean` を正本として確認した。

## 次に読むべき宣言

次の宣言は 0313 `GoldenZeroSectorCandidate.B_pos`、種別は **`theorem`** である。

Lean 正本では

```lean
/-- The upper inversion factor is strictly positive. -/
theorem B_pos (p : GoldenZeroSectorCandidate) :
    0 < zeroSectorB p.r p.s p.d := by
  unfold zeroSectorB
  linarith [p.U_nonneg, p.W_pos]
```

と続く。

0312 の `W>0` と 0305 の `U\ge0` を合成し、

$$
B=U+W>0
$$

を得る段階へ進む。