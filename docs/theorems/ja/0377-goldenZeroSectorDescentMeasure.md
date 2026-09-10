# 0377 `goldenZeroSectorDescentMeasure`

## 宣言種別

`def`

これは theorem ではなく、`GoldenZeroSectorDescentPacket` に自然数値の降下 measure を与える定義である。

## Lean コード

```lean
/-- The positive natural measure decreased by every certified descent step. -/
def goldenZeroSectorDescentMeasure
    (p : GoldenZeroSectorDescentPacket) : ℕ :=
  p.base.snd.natAbs
```

## Lean の型

```lean
goldenZeroSectorDescentMeasure :
  GoldenZeroSectorDescentPacket → ℕ
```

`GoldenZeroSectorDescentPacket` を一つ受け取り、その `base` の第二座標 `snd : ℤ` の絶対値を自然数として返す。

`p.base.snd.natAbs` は整数の絶対値を `ℕ` へ送るので、数学的には

$$
\mu(p)=|p.base.snd|
$$

である。

## 数学的意味

`p.base=(r,s)` と書けば、

$$
\mu(p)=|s|.
$$

0376 `GoldenZeroSectorDescentPacket` では第二座標に

$$
s=5t^5\quad\text{または}\quad s=-5t^5,
\qquad t>0
$$

という形が保存されていた。したがって packet 上では

$$
\mu(p)=5t^5>0
$$

となる。

ただし、この等式自体は今回の `def` の本体には含まれていない。`goldenZeroSectorDescentMeasure` はあくまで `|s|` を measure として選ぶだけであり、正値性は packet の `t_pos` と `snd_eq` を使う後続補題から得られる。

この選択の重要点は、符号付き整数座標 `s : ℤ` をそのまま順序 measure に使わず、`natAbs` により well-founded な自然数順序へ移していることである。

## 証明全体での役割

zero-sector 排除は、同じ不変条件を持つ packet をより小さい packet へ送る infinite descent で閉じる。そのため必要なのは

$$
P\longmapsto P'
$$

とともに

$$
\mu(P')<\mu(P)
$$

を証明できる well-founded measure である。

この定義はその `μ` を固定する。

後続の

```lean
structure GoldenZeroSectorStrictDescent
    (source : GoldenZeroSectorDescentPacket) where
  next : GoldenZeroSectorDescentPacket
  lift_eq : goldenZeroSectorLift source.base = goldenPow next.base 5
  measure_lt :
    goldenZeroSectorDescentMeasure next <
      goldenZeroSectorDescentMeasure source
```

では strict descent の定義そのものに今回の measure が埋め込まれている。

さらに最終的な `goldenZeroSectorDescentPacket_false` では

```lean
induction n using Nat.strong_induction_on
```

を用い、`goldenZeroSectorDescentMeasure q = n` を帰納パラメータとして、`step.measure_lt` からより小さい packet に帰納仮定を適用する。

したがってこの `def` は、代数的な fifth-power re-entry を Lean の well-founded recursion / strong induction へ接続する **順位関数** である。

## 直接依存する定義・補題

直接依存は非常に少ない。

- `GoldenZeroSectorDescentPacket`
  - 入力型。
- `GoldenZeroSectorDescentPacket.base`
  - 現在の `GoldenInt` を取り出す projection。
- `GoldenInt.snd`
  - 第二整数座標。
- `Int.natAbs`
  - `ℤ` の絶対値を `ℕ` として返す。

今回の定義自身は `snd_eq`, `t_pos`, `H_eq`, `five_not_dvd_norm` など packet の証明 field を参照しない。

一方、証明全体の意味上は 0376 の packet 不変量、および後続 `GoldenZeroSectorStrictDescent.measure_lt` と `goldenZeroSectorDescentPacket_false` に直接つながる。

## 定義の流れ

処理は一段だけである。

1. `p.base` で packet の現在の黄金整数を得る。
2. `.snd` で第二座標 `s : ℤ` を得る。
3. `.natAbs` で符号を落とし、`|s| : ℕ` を得る。

すなわち

$$
p\mapsto p.base\mapsto p.base.snd\mapsto |p.base.snd|.
$$

証明 tactic や補助 lemma は必要ない。

## Lean 固有の処理

### `Int.natAbs`

Lean では `p.base.snd : ℤ` なので、そのまま `Nat.strong_induction_on` の添字にはできない。`Int.natAbs` により

```lean
p.base.snd.natAbs : ℕ
```

を得て、標準の自然数 strong induction に接続している。

### structure projection の連鎖

```lean
p.base.snd.natAbs
```

は

```lean
Int.natAbs (GoldenInt.snd p.base)
```

に相当する projection chain である。短く書けるため、measure の定義が algebraic details から独立して見える。

### reducible な `def`

通常の `def` なので、必要な場所では

```lean
[goldenZeroSectorDescentMeasure]
```

を simp / unfold 対象にできる。実際、strict inequality の具体座標計算ではこの定義を展開することになる。

## なぜ第二座標なのか

packet には `base`, `t`, `D` など複数の自然な候補があるが、正本は `|base.snd|` を選んでいる。

これは第二座標が

$$
s=\pm5t^5
$$

という visible fifth-power coordinate であり、quadratic lift と fifth root の反復で直接追跡される量だからである。

`t` を measure にする設計も概念上は考えられるが、現在の strict descent theorem は次 packet の実際の第二座標を比較する形で構築されているため、`|s|` を measure にする方が中間 cast や fifth-root 単調性の補題を減らせる。

`D` は quartic factor の fifth root であり、re-entry の代数情報としては重要だが、最終 well-founded order を直接担う量には選ばれていない。

## 冗長・重複箇所

定義本体には実質的な重複はない。

ただし packet の `snd_eq` から

$$
\mu(p)=5p.t^5
$$

を導く補題を別途用意できるため、後続で `natAbs` と符号分岐を繰り返している箇所があるなら共通化余地がある。

たとえば概念的には

```lean
theorem goldenZeroSectorDescentMeasure_eq
    (p : GoldenZeroSectorDescentPacket) :
    goldenZeroSectorDescentMeasure p = 5 * p.t ^ 5 := ...
```

のような API が候補になる。

ただし正本にこの exact theorem が存在することは今回確認していないため、これは最適化案である。

## 最適化候補

1. **measure の値公式を named lemma 化する。**

   `snd_eq` と `t_pos` を用いて

   $$
   \mu(p)=5t^5
   $$

   を公開すれば、measure の positivity や比較の一部を自然数側だけで処理しやすくなる。

2. **positivity lemma を用意する。**

   packet では `t>0` なので

   $$
   0<\mu(p)
   $$

   が従う。後続で頻出するなら `measure_pos` として切り出す価値がある。

3. **`@[simp]` の付与は慎重に判断する。**

   `goldenZeroSectorDescentMeasure` を常に `natAbs` へ展開すると、abstract な strict-descent statement が座標計算へ早く崩れすぎる可能性がある。現在の named abstraction を保つ設計には意味がある。

4. **一般的な `WellFounded` abstraction への昇格。**

   将来ほかの descent argument と共通化するなら、packet と measure を一般の rank function として扱う層を作ることは可能である。ただし FLT5 単体では `Nat.strong_induction_on` が十分単純で、過抽象化になる可能性が高い。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

今回の `def` 自体が Mathlib 側で直接必要とする中心機能は `Int.natAbs` と基本的な `Nat` / `Int` 型である。ただし入力型 `GoldenZeroSectorDescentPacket` はプロジェクト内の先行定義に依存するため、実際の modular source ではその定義を提供するモジュール import が必要になる。

後続の利用まで含めると `Nat.strong_induction_on`、整数・自然数 cast、順序補題なども必要になるが、それらはこの `def` 単体の最小依存ではない。

厳密な最小 Mathlib import 集合は今回 Lean ビルドを行っていないため確認していない。したがって `import Mathlib` からの具体的な削減先は候補に留める。

## Comparator challenge 化の可否

**可能。小規模な definition / unfolding challenge に向く。**

定義そのものを再現させるだけでは非常に易しいが、抽象 measure と具体座標を往復させる課題にするとよい。

たとえば

```lean
example (p : GoldenZeroSectorDescentPacket) :
    goldenZeroSectorDescentMeasure p = p.base.snd.natAbs := by
  rfl
```

は definitional equality の最小 challenge になる。

さらに packet の `snd_eq` を与えて

$$
\mu(p)=5p.t^5
$$

を証明させれば、`rcases`、整数 `natAbs`、cast、冪、符号分岐を含む実用的な Comparator challenge に発展できる。

また `GoldenZeroSectorStrictDescent.measure_lt` から strong-induction step を再構成させる課題にすれば、この measure が単なる accessor ではなく well-founded descent の rank であることまで評価できる。

## 次に読むべき宣言

次は namespace `GoldenZeroSectorDescentPacket` 内の

```lean
theorem snd_ne_zero (p : GoldenZeroSectorDescentPacket) :
    p.base.snd ≠ 0 := by
  have ht : (0 : ℤ) < p.t := by exact_mod_cast p.t_pos
  rcases p.snd_eq with h | h
  · rw [h]
    exact ne_of_gt (mul_pos (by norm_num) (pow_pos ht 5))
  ...
```

である。

この theorem は `snd_eq` と `t_pos` から、measure の元になっている第二座標が実際に非零であることを取り出す。

0377 が

$$
\mu(p)=|s|
$$

という順位関数を **定義** したのに対し、次の宣言では packet 不変量から

$$
s\ne0
$$

を証明し、後続の平方正値性

$$
s^2>0
$$

へ進む。これは fifth-root re-entry の positivity chain の入口となる。