# 0397 `goldenZeroSectorDescentPacket_false`

## 宣言種別

`theorem`

任意の `GoldenZeroSectorDescentPacket` が存在すると矛盾することを、自然数値 measure に対する強帰納法で閉じる theorem である。

## Lean コード

```lean
/--
There is no infinite chain of certified zero-sector descent packets. `strictDescent`
preserves the packet invariant and supplies a smaller natural measure, so
`Nat.strong_induction_on` applies. The argument uses only the golden lift and
preceding packet lemmas, never the final FLT5 theorem; hence the closure is
non-circular.
-/
theorem goldenZeroSectorDescentPacket_false
    (p : GoldenZeroSectorDescentPacket) : False := by
  have noAt : ∀ n : ℕ, ∀ q : GoldenZeroSectorDescentPacket,
      goldenZeroSectorDescentMeasure q = n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro q hq
        obtain ⟨step⟩ := q.strictDescent
        exact ih (goldenZeroSectorDescentMeasure step.next)
          (by simpa [hq] using step.measure_lt) step.next rfl
  exact noAt (goldenZeroSectorDescentMeasure p) p rfl
```

## Lean の型

```lean
goldenZeroSectorDescentPacket_false :
  (p : GoldenZeroSectorDescentPacket) → False
```

入力は certified zero-sector descent invariant を満たす packet `p` であり、出力は `False` である。

したがって論理的には

$$
\neg\,\mathrm{Nonempty}(\mathrm{GoldenZeroSectorDescentPacket})
$$

に相当する内容を、個々の `p` を受け取る関数形で表している。

## 数学的主張

measure を

$$
\mu(p)=|p.base.snd|\in\mathbb N
$$

とする。0396 `GoldenZeroSectorDescentPacket.strictDescent` により、任意の packet `q` から別の packet `q'` が得られ、

$$
\mu(q')<\mu(q)
$$

が成り立つ。

もし packet `p` が存在すれば、これを反復して

$$
\mu(p)>
\mu(p_1)>
\mu(p_2)>
\mu(p_3)>
\cdots
$$

という自然数の無限降下が生じる。しかし自然数の `<` は well-founded なので、そのような無限降下は存在しない。

この theorem は、その古典的な infinite descent を `Nat.strong_induction_on` で直接形式化している。

## 証明全体での役割

0397 は zero-sector descent サブ証明の **well-founded closure** である。

0387–0394 では第五根の抽出、座標算術、primitive 条件、5 非可除性、第五冪分離、strict measure decrease を証明した。0395 はそれらを格納する descent certificate の型 `GoldenZeroSectorStrictDescent` を定義し、0396 は任意の packet からその certificate が存在することを示した。

0397 では、それらの局所算術を一切再展開しない。必要なのは

```lean
obtain ⟨step⟩ := q.strictDescent
```

と

```lean
step.measure_lt
```

だけである。

したがって依存構造は概念的に

$$
\text{local golden arithmetic}
\longrightarrow
\text{certified strict descent}
\longrightarrow
\text{well-founded contradiction}
$$

と完全に分離されている。

またソースコメントが明示する通り、ここでは最終 FLT5 theorem を仮定して zero-sector を排除しているのではない。先行する golden lift と packet lemma のみで閉じるため、この closure は非循環である。

## 直接依存する定義・補題

主要な直接依存は次である。

- `GoldenZeroSectorDescentPacket`
- `goldenZeroSectorDescentMeasure`
- `GoldenZeroSectorDescentPacket.strictDescent` — 0396
- `GoldenZeroSectorStrictDescent.next` — 0395 の field
- `GoldenZeroSectorStrictDescent.measure_lt` — 0395 の field
- `Nat.strong_induction_on`

特に `goldenZeroSectorDescentMeasure` は

```lean
def goldenZeroSectorDescentMeasure
    (p : GoldenZeroSectorDescentPacket) : ℕ :=
  p.base.snd.natAbs
```

と定義されており、整数座標 `snd` を `natAbs` によって well-founded な自然数へ射影している。

0395 のもう一つの field

```lean
lift_eq :
  goldenZeroSectorLift source.base = goldenPow next.base 5
```

は 0397 の proof term では直接参照されない。これは `strictDescent` が構築する遷移の数学的 provenance を保証する field であり、well-founded closure 自体は `next` と `measure_lt` だけを消費する。

## 証明の流れ

1. 各自然数 `n` に対して、measure がちょうど `n` の packet は存在できないという命題を局所的に用意する。

   ```lean
   have noAt : ∀ n : ℕ, ∀ q : GoldenZeroSectorDescentPacket,
       goldenZeroSectorDescentMeasure q = n → False := by
   ```

2. `n` に対して `Nat.strong_induction_on` を適用する。

   ```lean
   induction n using Nat.strong_induction_on with
   | h n ih =>
   ```

   帰納法の仮定 `ih` は、任意の `m<n` について measure `m` の packet が存在しないことを利用できる形になる。

3. measure `n` の packet `q` と

   ```lean
   hq : goldenZeroSectorDescentMeasure q = n
   ```

   を仮定する。

4. 0396 から strict descent certificate を一つ取り出す。

   ```lean
   obtain ⟨step⟩ := q.strictDescent
   ```

5. `step.measure_lt` は

   $$
   \mu(step.next)<\mu(q)
   $$

   を与える。`hq` を使って右辺を `n` に書き換え、

   $$
   \mu(step.next)<n
   $$

   とする。

6. そのより小さい measure に帰納法の仮定 `ih` を適用する。`step.next` 自身は measure が自分自身と等しいので、最後の引数は `rfl` で閉じる。

7. 最後に初期 packet `p` へ `noAt` を適用する。

   ```lean
   exact noAt (goldenZeroSectorDescentMeasure p) p rfl
   ```

これで `False` が得られる。

## Lean 固有の処理

### `induction n using Nat.strong_induction_on`

通常の `Nat.rec` 型帰納法では「直前の `n-1`」しか直接得られないが、descent step がどれだけ measure を減らすかは 1 とは限らない。

0396 が保証するのは

$$
\mu(next)<\mu(source)
$$

だけなので、任意のより小さい自然数を利用できる strong induction が自然な選択である。

### `obtain ⟨step⟩ := q.strictDescent`

0396 の返り値は

```lean
Nonempty (GoldenZeroSectorStrictDescent q)
```

である。その唯一必要な witness を `obtain` で取り出す。

目標が `False`、すなわち `Prop` であるため、`Nonempty` の elimination で十分であり、計算可能な witness extraction や `Classical.choose` は不要である。

### `simpa [hq] using step.measure_lt`

`step.measure_lt` の右辺は

```lean
goldenZeroSectorDescentMeasure q
```

である。一方 `ih` が要求する境界は `n` なので、`hq` を simplifier に渡して同一視している。

### `rfl`

帰納法の仮定へ `step.next` を渡した最後の equality

```lean
goldenZeroSectorDescentMeasure step.next =
  goldenZeroSectorDescentMeasure step.next
```

は定義的反射性で閉じる。

## 冗長・重複箇所

0397 自体には算術的な重複はほぼない。むしろ、0395–0396 までで arithmetic と descent certificate を十分に抽象化した成果がここに現れている。

若干の構造上の冗長性として、局所命題 `noAt` は

```lean
∀ n, ∀ q, goldenZeroSectorDescentMeasure q = n → False
```

という equality-indexed 形式を取る。このため最後に

```lean
noAt (goldenZeroSectorDescentMeasure p) p rfl
```

と measure をいったん index に持ち上げてから戻している。

これは strong induction を直接書くには分かりやすい一方、より一般的な well-founded relation を使えば equality index を持たずに書ける可能性がある。

また 0395 の `lift_eq` は本 theorem からは見えないが、これは冗長な field とは限らない。0397 は abstract closure 層なので、遷移が正しい第五根由来であることは 0396 が既に証明済みとして隠蔽されるべきだからである。

## 最適化候補

最も有力な一般化は、次のような generic strict-descent impossibility lemma を切り出すことである。

概念的には、型 `α`、measure `μ : α → ℕ`、そして

$$
\forall x:\alpha,\;\exists y:\alpha,\;\mu(y)<\mu(x)
$$

があれば `α` に inhabitant は存在できない、という形である。

例えば API としては概念的に

```lean
theorem false_of_always_exists_smaller
    {α : Type*} (μ : α → ℕ)
    (step : ∀ x : α, Nonempty { y : α // μ y < μ x }))
    (x : α) : False := ...
```

のように抽象化できる。

そうすれば 0397 は 0396 の descent function と measure を渡すだけになる。この一般化は FLT3、FLT5、将来の他指数の descent で同じ closure pattern が現れる場合に特に有効である。

別案として `Nat.lt_wfRel` や `WellFounded` / `measure` 系 API を使えば、数学的には「自然数強帰納法」から「well-founded relation に下降列はない」へ抽象度を一段上げられる。

ただし現状の証明は非常に短く、`Nat.strong_induction_on` により下降原理が明示されているため、FLT5 standalone の可読性という観点では十分に良い実装である。

## 必要 Mathlib import と import 最適化候補

standalone 正本全体は

```lean
import Mathlib
```

を使用している。

0397 が Mathlib 側から直接必要とする中心機能は

- `Nat.strong_induction_on`
- `Nonempty` の Prop elimination
- `simpa`

である。

`GoldenZeroSectorDescentPacket`、`goldenZeroSectorDescentMeasure`、`strictDescent` は DkMath 側の先行定義・定理である。

この theorem 自体は ring、valuation、number field、`nlinarith` などの重い算術 API を直接使用しない。そのため source module を適切に分離するなら、closure theorem 単体の Mathlib 依存はかなり小さくできる可能性がある。

ただし今回は Lean build を行わない条件なので、厳密な最小 import の集合は確認していない。import 最適化を実施する場合は、まず 0396 までを提供する DkMath module を import し、`Nat.strong_induction_on` と tactic `simpa` に必要な Mathlib module だけを追加してビルド検証するのが安全である。

## Comparator challenge 化の可否

**非常に適している。**

0397 は局所数論を知らなくても、与えられた descent API から well-founded contradiction を正しく構成できるかを評価できる。

challenge では次を既知 API として固定できる。

```lean
goldenZeroSectorDescentMeasure : GoldenZeroSectorDescentPacket → ℕ

GoldenZeroSectorDescentPacket.strictDescent :
  (p : GoldenZeroSectorDescentPacket) →
  Nonempty (GoldenZeroSectorStrictDescent p)
```

および certificate の

```lean
next
measure_lt
```

だけを公開し、目標を

```lean
(p : GoldenZeroSectorDescentPacket) → False
```

とする。

評価点は

- strong induction の選択
- strict inequality を induction hypothesis の index へ接続する処理
- `Nonempty` witness の Prop 内 elimination
- equality index `hq` の rewrite
- arithmetic subproof に依存しない abstraction boundary の理解

である。

また比較対象として

1. `Nat.strong_induction_on` を直接使う版
2. generic `WellFounded` / measure lemma を使う版

を用意すれば、証明長だけでなく再利用性・抽象化能力も比較できる。

## 次に読むべき宣言

次は theorem ではなく **`def`** の

```lean
def goldenZeroSectorDescentPacket_of_candidate
    (p : GoldenZeroSectorCandidate) : GoldenZeroSectorDescentPacket where
  base := ⟨p.r, p.s⟩
  t := 5 * p.c ^ 2
  D := p.d ^ 2
  ...
```

である。

0397 により `GoldenZeroSectorDescentPacket` 自体が存在不能であることが閉じた。次の declaration は、元の `GoldenZeroSectorCandidate` があれば、その候補からまさにその不可能な recursive packet を構築できることを示す入口となる。

したがって次の段階は

$$
\text{zero-sector candidate}
\longrightarrow
\text{descent packet}
\longrightarrow
\bot
$$

という、descent closure を元の FLT5 zero-sector candidate へ接続する橋である。
