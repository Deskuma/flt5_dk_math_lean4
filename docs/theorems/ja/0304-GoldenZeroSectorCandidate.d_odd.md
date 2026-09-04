# 0304 — `GoldenZeroSectorCandidate.d_odd`

## 宣言種別

これは **`theorem`** である。

0303 `GoldenZeroSectorCandidate.H_odd` で得た quartic second-coordinate factor の奇性と、0297 `GoldenZeroSectorCandidate.H_eq_tenth` で得た exact tenth-power representation を組み合わせ、tenth-power base `d` 自身が奇数であることを示す。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- Consequently the tenth-power base `d` is odd. -/
theorem d_odd (p : GoldenZeroSectorCandidate) : Odd p.d := by
  have hH := p.H_odd
  rw [p.H_eq_tenth] at hH
  have hdZ : Odd (p.d : ℤ) :=
    (Int.odd_pow' (by decide : 10 ≠ 0)).mp hH
  exact_mod_cast hdZ
```

結論は自然数上の parity proposition

```lean
Odd p.d
```

である。

## 数学的意味

0303 により

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s)
$$

は奇数である。また 0297 により

$$
H(r,s)=d^{10}
$$

が成り立つ。したがって

$$
d^{10}\text{ is odd}.
$$

正の指数について、整数の冪が奇数なら底も奇数であるから、

$$
d\text{ is odd}
$$

を得る。

同値な合同式で書けば、

$$
d^{10}\equiv1\pmod2
$$

から

$$
d\equiv1\pmod2
$$

を取り出している。

この theorem は 0303 が quartic factor 側で確定した 2-adic unit 性を、exact power identity を通して base `d` へ降ろす **parity descent** である。

## 証明全体での役割

0301→0302 では prime five に対して

$$
5\nmid H(r,s)
$$

から

$$
5\nmid d
$$

へ情報を降ろした。0303→0304 はそれと平行に prime two に対する情報を降ろす：

$$
H(r,s)\text{ odd}
\Longrightarrow
 d^{10}\text{ odd}
\Longrightarrow
 d\text{ odd}.
$$

したがって 0304 まで到達すると `d` は少なくとも

$$
2\nmid d,\qquad 5\nmid d
$$

を満たすことになる。

これは後続の zero-sector inversion で `d` から作る量、とくに `d^5` や `zeroSectorW p.d` の 2-adic / 5-adic 挙動を制御するための基礎条件になる。0303 が primitive coordinate の偶奇を quartic factor に集約したのに対し、0304 はその結果を後続計算で直接使いやすい base-level invariant に変換している。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate.H_odd`

直前の 0303。型は概念的に

```lean
p.H_odd : Odd (goldenFifthSndFactor p.r p.s)
```

であり、本 theorem の parity 情報の唯一の数学的入力である。

### `GoldenZeroSectorCandidate.H_eq_tenth`

0297。quartic factor を tenth power として exact に同定する：

```lean
p.H_eq_tenth :
  goldenFifthSndFactor p.r p.s = (p.d : ℤ) ^ 10
```

これにより `H_odd` を `(p.d : ℤ)^10` の奇性へ rewrite できる。

### `Int.odd_pow'`

整数冪の奇性を底の奇性と結ぶ Mathlib lemma。本 proof では

```lean
(Int.odd_pow' (by decide : 10 ≠ 0)).mp hH
```

として使われ、指数 `10` が非零であることを与えた上で

```lean
Odd ((p.d : ℤ) ^ 10) → Odd (p.d : ℤ)
```

を得る。

### `exact_mod_cast`

`hdZ : Odd (p.d : ℤ)` から最終目標 `Odd p.d` へ、自然数から整数への cast を越えて命題を移送する。

### `decide`

閉じた命題

```lean
10 ≠ 0
```

を決定手続きで証明する。

## 証明または構築の流れ

1. `have hH := p.H_odd` で quartic factor の奇性を取得する。
2. `rw [p.H_eq_tenth] at hH` により、`hH` を quartic polynomial の奇性から `(p.d : ℤ)^10` の奇性へ変換する。
3. `Int.odd_pow'` の逆向き `.mp` を使い、非零指数 `10` の冪が odd なら底 `(p.d : ℤ)` も odd とする。
4. `exact_mod_cast hdZ` で整数上の oddness を自然数 `p.d` の oddness へ戻し、目標を閉じる。

証明の数学的内容は非常に短く、実装の大半は `ℕ` と `ℤ` の型境界を安全に越える処理である。

## Lean 固有の処理

最も重要な Lean 固有点は、candidate の `d` が `ℕ` である一方、quartic factor `goldenFifthSndFactor p.r p.s` は `ℤ` 上にあることである。

そのため 0297 の identity は

```lean
(p.d : ℤ) ^ 10
```

という cast 済みの形を持つ。`rw [p.H_eq_tenth] at hH` 後の `hH` も整数上の `Odd` 命題になるので、`Int.odd_pow'` を直接適用できる。

しかし theorem の最終結論は

```lean
Odd p.d
```

であり自然数上である。この最後の一段を `exact_mod_cast` が担当する。

また `Int.odd_pow'` は指数が非零であることを要求するため、固定指数 `10` に対して

```lean
by decide : 10 ≠ 0
```

を明示している。紙上の証明では自明として省略されるが、Lean では theorem API の前提として露出している。

## 冗長・重複箇所

この theorem 自体には大きな冗長性はない。4 行の proof は役割が明確に分離されている。

ただし構造上は 0302 `five_not_dvd_d` とよく似ている。どちらも

1. factor 側の性質を取得し、
2. `H_eq_tenth` で `d^10` へ rewrite し、
3. power から base へ性質を降ろす、

という同じ transport pattern を持つ。

この類似はコード重複というより、zero-sector inversion が prime `5` channel と parity `2` channel を並行して処理していることの表れである。現時点の短い theorem を抽象化する利益は小さい。

## 最適化候補

現在の実装は十分に短く、可読性も高い。候補としては `hH` と `hdZ` をさらに inline 化することはできる可能性があるが、推奨度は低い。

例えば概念的には

```lean
have hH := p.H_odd
rw [p.H_eq_tenth] at hH
exact_mod_cast (Int.odd_pow' (by decide : 10 ≠ 0)).mp hH
```

まで縮められる可能性がある。ただし `exact_mod_cast` と elaboration の組み合わせがこの形で安定するかは、本作業では Lean build を行わない条件のため未検証である。

現在の `hdZ` は `ℤ` 上の中間命題を明示し、型境界を読者に見せる教育的価値が高い。そのため theorem museum の観点では現行形の方が適している。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem が直接必要とする機能は少なくとも次の系統である。

- integer parity (`Odd`, `Int.odd_pow'`)
- casts between `ℕ` and `ℤ`
- `exact_mod_cast`
- `decide`
- 依存 theorem `H_odd`, `H_eq_tenth`

ただし本 repository の standalone artifact では source module ごとの最小 import は保持されておらず、本作業では Lean build を行わないため、厳密な最小 import 集合は **未確認** である。

import 最適化を行う場合は、元 source module `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` の実際の import graph を DkMath 側で確認し、`Mathlib` umbrella import を parity / cast / tactic 関連モジュールへ縮小できるかをビルドで検証すべきである。本 museum 作業では変更しない。

## Comparator challenge 化の可否

**可能であり、比較的良い小問候補である。**

理由は、証明が短い一方で次の三点を要求するからである。

1. 既存 theorem `H_odd` と `H_eq_tenth` の再利用。
2. `Int.odd_pow'` の向きと非零指数条件の理解。
3. `Odd (p.d : ℤ)` から `Odd p.d` への cast 処理。

Comparator challenge とするなら、statement と `H_odd` / `H_eq_tenth` を与え、proof body を穴にするのが適切である。単純な `simp` 一発ではなく、rewrite、parity API、cast transport の三段階を要求できる。

難度は初級後半〜中級入口程度で、特に `exact_mod_cast` の用途を学ぶ教材として有効である。

## PDF との照合

対象 branch には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

ただし GitHub コネクタの通常の text fetch は binary PDF 本文を返さないため、本作業では PDF 内の具体的ページ・節・式番号と 0304 を直接照合できていない。したがって PDF 上の位置については推測しない。

本解説の技術的内容、Lean code、依存関係、宣言順は repository 内の `Flt5DkMath/FLT5StandAlone.lean` を正本としている。

## 次に読むべき宣言

次の宣言は 0305 `GoldenZeroSectorCandidate.U_nonneg`、種別は **`theorem`** である。

Lean 正本では `d_odd` の直後に

```lean
/-- The diagonal sum is nonnegative independently of the candidate hypotheses. -/
theorem U_nonneg (p : GoldenZeroSectorCandidate) :
    0 ≤ zeroSectorU p.r p.s := by
  unfold zeroSectorU
  ...
```

と続く。

0304 までで `d` に対する 2-adic / 5-adic base constraints を整えた後、0305 からは zero-sector diagonal quantities `U`, `W`, `X` の符号・恒等式へ進む。ここから後続の difference-of-squares / discriminant factorization に必要な幾何的・代数的量の制御が始まる。
