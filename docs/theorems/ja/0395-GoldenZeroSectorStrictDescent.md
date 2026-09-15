# 0395 `GoldenZeroSectorStrictDescent`

## 宣言種別

`structure`

`GoldenZeroSectorDescentPacket` から 1 回の strict descent を実行した結果を、次の packet・第五冪再入等式・measure の真の減少の 3 要素として束ねる証明データ構造である。

## Lean コード

```lean
/-- One certified re-entry step with strict decrease of the visible coordinate. -/
structure GoldenZeroSectorStrictDescent
    (source : GoldenZeroSectorDescentPacket) where
  next : GoldenZeroSectorDescentPacket
  lift_eq : goldenZeroSectorLift source.base = goldenPow next.base 5
  measure_lt :
    goldenZeroSectorDescentMeasure next <
      goldenZeroSectorDescentMeasure source
```

## Lean の型

概念的には次の依存型である。

```lean
GoldenZeroSectorStrictDescent :
  GoldenZeroSectorDescentPacket → Type
```

ある `source : GoldenZeroSectorDescentPacket` に対して、その要素は

```lean
{
  next : GoldenZeroSectorDescentPacket
  lift_eq : goldenZeroSectorLift source.base = goldenPow next.base 5
  measure_lt :
    goldenZeroSectorDescentMeasure next <
      goldenZeroSectorDescentMeasure source
}
```

という 3 フィールドを保持する。

ここで `next` は単なる `GoldenInt` ではなく、zero-sector descent の再帰不変量をすべて満たした **完全な次世代 packet** である。

## 数学的意味

`source` の基底を

$$
\alpha = source.base
$$

とし、`next.base` を

$$
\gamma = next.base
$$

と書く。この structure は、以下の 2 つの数学的事実を 1 つの certified step として固定する。

まず再入等式

$$
T(\alpha)=\gamma^5,
$$

ただし

$$
T(r,s)=\left(r^2+rs+s^2,\ s^2\right)
$$

である。

次に measure の真の減少

$$
\mu(next)<\mu(source),
$$

ここで

$$
\mu(p)=|p.base.snd|.
$$

したがってこの structure は、同じ zero-sector invariant の世界の中で

$$
source \longmapsto next
$$

という遷移を作りながら、自然数値 measure を必ず減少させることを表す。

## 証明全体での役割

0395 は、直前まで個別に構築してきた 2 本の Beam を 1 つに束ねる境界である。

0394 までで第五根 `gamma` について

$$
\gamma_{\mathrm{snd}}=5u^5,
\qquad
H(\gamma)=v^5,
$$

primitive coordinates、norm の 5 非可除性、正値性など、次の `GoldenZeroSectorDescentPacket` を構成するための invariant が揃った。

一方 0393 では

$$
|\gamma_{\mathrm{snd}}|<|source.base.snd|
$$

が証明済みである。

`GoldenZeroSectorStrictDescent` は、それらを

$$
\text{recursive shape preserved}
\quad+\quad
\text{measure strictly decreases}
$$

という 1 回分の descent certificate にまとめる。

直後の `GoldenZeroSectorDescentPacket.strictDescent` は実際にこの structure の値を構築し、その次の `goldenZeroSectorDescentPacket_false` はこの certificate を `Nat.strong_induction_on` へ渡して無限降下を閉じる。

よって 0395 は、局所的な算術補題群から well-founded descent へ移るための **インターフェース構造体** である。

## 各フィールドの意味

### `next`

```lean
next : GoldenZeroSectorDescentPacket
```

次世代の packet そのものを保存する。

これは

- 第二座標が $5u^5$ 型
- quartic factor が第五冪
- 座標が primitive
- norm が 5 と互いに素

という recursive invariant をまとめて保持する。

### `lift_eq`

```lean
lift_eq : goldenZeroSectorLift source.base = goldenPow next.base 5
```

source の quadratic lift が next の基底の第五冪であることを記録する。

数学的には

$$
T(source.base)=next.base^5.
$$

これは `next` が任意に選ばれた小さい packet ではなく、source の算術構造から正当に生成された re-entry root であることを保証する provenance である。

### `measure_lt`

```lean
measure_lt :
  goldenZeroSectorDescentMeasure next <
    goldenZeroSectorDescentMeasure source
```

自然数 measure の strict decrease を保存する。

定義を展開すれば

$$
|next.base.snd|<|source.base.snd|.
$$

このフィールドがあるため、後続証明は descent の内部算術を再展開せず、well-foundedness だけを使える。

## 直接依存する定義・補題

宣言そのものが直接参照するのは次である。

- `GoldenZeroSectorDescentPacket`
- `goldenZeroSectorLift`
- `goldenPow`
- `goldenZeroSectorDescentMeasure`

ただし、この structure が実際に inhabited であることを示す直後の constructor theorem は、直前の主要結果に依存する。

- `GoldenZeroSectorDescentPacket.exists_lift_eq_fifthPower`
- `GoldenZeroSectorDescentPacket.fifthRoot_power_split`
- `GoldenZeroSectorDescentPacket.fifthRoot_coprime_coords`
- `GoldenZeroSectorDescentPacket.fifthRoot_measure_lt`
- `GoldenZeroSectorDescentPacket.five_not_dvd_D`

したがって 0395 自体は薄い declaration だが、その意味論は 0387–0394 の集約点である。

## 構築の流れ

structure 宣言そのものには proof script はない。Lean は 3 フィールドを持つ constructor を自動生成する。

後続の `strictDescent` では概ね次の順に値が構築される。

1. `exists_lift_eq_fifthPower` から第五根 `gamma` を得る。
2. `fifthRoot_power_split` から正の `u,v` と
   $$
   \gamma.snd=5u^5,
   \qquad
   H(\gamma)=v^5
   $$
   を得る。
3. `fifthRoot_coprime_coords` で primitive 条件を得る。
4. norm の 5 非可除性を回収する。
5. それらから `next : GoldenZeroSectorDescentPacket` を構築する。
6. `hroot` を `lift_eq` に格納する。
7. 0393 `fifthRoot_measure_lt` を `measure_lt` に格納する。

この分離により、算術構築と strong induction closure が明確に切り離されている。

## Lean 固有の処理

`structure ... (source : GoldenZeroSectorDescentPacket)` は parameterized structure であり、`source` は各フィールドから参照できるが独立した field ではない。

このため `GoldenZeroSectorStrictDescent p` は「任意の descent step」ではなく、**特定の source `p` から出る step** の型となる。

また `next` が先に定義されることで、後続の `lift_eq` と `measure_lt` はその field に依存できる。これは dependent record の典型的な使い方である。

後続では

```lean
obtain ⟨step⟩ := q.strictDescent
```

と pattern matching して structure を取り出し、

```lean
step.next
step.measure_lt
```

だけで strong induction を進められる。算術証明を induction 本体から隠蔽できる点が Lean 上の重要な設計効果である。

## 冗長・重複箇所

0395 自体は 3 フィールドだけで、冗長性はほぼない。

検討可能なのは `lift_eq` の必要性である。後続の `goldenZeroSectorDescentPacket_false` が直接使うのは `next` と `measure_lt` だけであり、strong induction closure だけを目的にすれば `lift_eq` は不要に見える。

しかし `lift_eq` は descent step の provenance を保持し、「next が source の quadratic lift の第五根から生成された」という数学的関係を失わないために有益である。したがって削除による短縮よりも、監査可能性と再利用性を優先した設計と評価できる。

また `measure_lt` を別 theorem にせず structure field に保存していることで、後続利用時の引数再構築が不要になっている。この点も実質的な重複削減になっている。

## 最適化候補

現状は十分に小さく、structure 自体の最適化余地は少ない。

候補としては、より一般的な descent framework を導入する場合、

```lean
structure StrictDescentStep (α : Type) (measure : α → ℕ) (source : α) where
  next : α
  measure_lt : measure next < measure source
```

のような汎用 structure を作り、FLT5 固有の `lift_eq` を追加 field または refinement として持たせる設計が考えられる。

ただし現在の証明では domain-specific な `lift_eq` を同じ record に保存することに意味があり、抽象化はコード量を必ずしも減らさない。一般化は、他の指数や他の descent でも同型の pattern が複数回現れた時点で検討するのが自然である。

## 必要 Mathlib import と import 最適化候補

この declaration だけを見る限り、Mathlib の高度な theorem は使用していない。必要なのは、参照される DkMath 側の定義が既に利用可能であることだけである。

standalone 正本全体は `import Mathlib` を前提としているが、この structure 単体の最小 import は今回 Lean build を行わない条件では確定できない。

少なくとも宣言自身は arithmetic tactic、`Finset`、algebraic number theory API などを直接要求しないため、実モジュールを分割するなら、そのモジュールが必要とする import は `GoldenZeroSectorDescentPacket`、`goldenZeroSectorLift`、`goldenPow`、`goldenZeroSectorDescentMeasure` の定義元にほぼ限定できる可能性が高い。

## Comparator challenge 化の可否

**単独では challenge としては弱い。**

0395 は proof を持たない `structure` 宣言であり、Comparator に与えても主な課題は dependent record の型設計を再現することになる。

一方、0395 と直後の `GoldenZeroSectorDescentPacket.strictDescent` をセットにすれば非常に良い challenge になる。

その場合の課題は、既存の 0387–0394 API だけを用いて

```lean
Nonempty (GoldenZeroSectorStrictDescent p)
```

を構築することであり、

- root extraction
- power split
- primitive invariant
- 5-adic invariant
- strict measure decrease
- dependent record construction

をまとめて評価できる。

したがって Comparator 用には **0395 単体より 0395+0396 の constructor challenge** が適している。

## 次に読むべき宣言

次は

```lean
theorem GoldenZeroSectorDescentPacket.strictDescent
    (p : GoldenZeroSectorDescentPacket) :
    Nonempty (GoldenZeroSectorStrictDescent p) := by
  ...
```

である。

0395 が「strict descent step とは何を保持すべきか」を型として定義したのに対し、次の theorem は 0387–0394 の結果を実際に集約してその値を構築する。

流れは

$$
\text{packet arithmetic}
\longrightarrow
\text{strict descent certificate}
\longrightarrow
\text{strong induction closure}
$$

であり、次の宣言はその中央の constructor に当たる。