# 0396 `GoldenZeroSectorDescentPacket.strictDescent`

## 宣言種別

`theorem`

`GoldenZeroSectorDescentPacket` から、0395 で定義された `GoldenZeroSectorStrictDescent` の実体を構築する theorem である。

## Lean コード

```lean
/--
Construct the next descent packet from a fifth root of the quadratic lift. The
new visible coordinate is the root's second coordinate; coprimality, the
fifth-power shape, and the norm condition are preserved, while
`fifthRoot_measure_lt` proves that its `|s|` measure strictly decreases.
-/
theorem GoldenZeroSectorDescentPacket.strictDescent
    (p : GoldenZeroSectorDescentPacket) :
    Nonempty (GoldenZeroSectorStrictDescent p) := by
  obtain ⟨gamma, hroot, hnorm⟩ := p.exists_lift_eq_fifthPower
  obtain ⟨u, v, hu, hv, hsnd, hH⟩ :=
    p.fifthRoot_power_split gamma hroot hnorm
  have hcop := p.fifthRoot_coprime_coords gamma hroot hnorm
  have h5norm : ¬ (5 : ℤ) ∣ goldenNorm gamma := by
    rw [hnorm]
    intro h
    exact p.five_not_dvd_D (by exact_mod_cast h)
  let next : GoldenZeroSectorDescentPacket := {
    base := gamma
    t := u
    D := v
    t_pos := hu
    D_pos := hv
    coprime_coords := hcop
    snd_eq := Or.inl hsnd
    H_eq := hH
    five_not_dvd_norm := h5norm }
  exact ⟨{
    next := next
    lift_eq := hroot
    measure_lt := p.fifthRoot_measure_lt gamma hroot }⟩
```

## Lean の型

```lean
GoldenZeroSectorDescentPacket.strictDescent :
  (p : GoldenZeroSectorDescentPacket) →
  Nonempty (GoldenZeroSectorStrictDescent p)
```

任意の descent packet `p` に対して、そこから出発する strict descent certificate が少なくとも 1 つ存在することを返す。

`Nonempty` を用いるため、この theorem は「次の packet を計算可能な関数として公開する」のではなく、Lean の論理内部でその存在を保証する形になっている。

## 数学的主張

`p.base = α` とする。0387 により quadratic lift の第五根

$$
T(\alpha)=\gamma^5
$$

が存在し、さらに

$$
N(\gamma)=D
$$

が得られる。

0394 により、この第五根の第二座標と quartic factor は

$$
\gamma_{\mathrm{snd}}=5u^5,
\qquad
H(\gamma)=v^5
$$

と再び第五冪型へ分離できる。

そこで

$$
next.base=\gamma,
\qquad
next.t=u,
\qquad
next.D=v
$$

と置くと、`next` は再び `GoldenZeroSectorDescentPacket` になる。

しかも 0393 から

$$
\mu(next)<\mu(p),
$$

すなわち

$$
|\gamma_{\mathrm{snd}}|<|p.base.snd|
$$

が成り立つ。

従って、同じ recursive invariant を保存しながら自然数 measure を真に減少させる 1 ステップが常に存在する。

## 証明全体での役割

0396 は zero-sector descent の局所算術を、well-founded descent が直接利用できる 1 個の object へ圧縮する theorem である。

0387–0394 では個別に

- honest fifth root の存在
- root の第二座標の積恒等式
- quartic factor の正値性
- root の第二座標の正値性
- primitive coordinates
- quartic factor の 5 非可除性
- strict measure decrease
- recursive fifth-power split

を証明してきた。

0396 はこれらを使って

$$
p\longmapsto next
$$

を実際に構築し、0395 の `GoldenZeroSectorStrictDescent p` に格納する。

直後の `goldenZeroSectorDescentPacket_false` は、この theorem だけを入口として `Nat.strong_induction_on` を実行できる。したがって 0396 は **算術層と well-founded induction 層を接続する constructor theorem** である。

## 直接依存する定義・補題

主要な直接依存は次である。

- `GoldenZeroSectorDescentPacket`
- `GoldenZeroSectorStrictDescent`
- `GoldenZeroSectorDescentPacket.exists_lift_eq_fifthPower`
- `GoldenZeroSectorDescentPacket.fifthRoot_power_split`
- `GoldenZeroSectorDescentPacket.fifthRoot_coprime_coords`
- `GoldenZeroSectorDescentPacket.five_not_dvd_D`
- `GoldenZeroSectorDescentPacket.fifthRoot_measure_lt`
- `goldenNorm`

特に依存順としては

$$
0387\to0394
\quad\Longrightarrow\quad
0396
$$

であり、0395 は結果を格納する structure の型を与える。

## 証明の流れ

1. `exists_lift_eq_fifthPower` から

   ```lean
   gamma : GoldenInt
   hroot : goldenZeroSectorLift p.base = goldenPow gamma 5
   hnorm : goldenNorm gamma = (p.D : ℤ)
   ```

   を得る。

2. `fifthRoot_power_split` から正の自然数 `u, v` と

   $$
   \gamma.snd=5u^5,
   \qquad
   H(\gamma)=v^5
   $$

   を得る。

3. `fifthRoot_coprime_coords` により

   $$
   \gcd(|\gamma.fst|,|\gamma.snd|)=1
   $$

   を得る。

4. `hnorm` と source packet の `five_not_dvd_D` から

   $$
   5\nmid N(\gamma)
   $$

   を回収する。

5. `gamma,u,v` とこれらの証明から `next : GoldenZeroSectorDescentPacket` を構築する。

6. `hroot` を `lift_eq` に、0393 `fifthRoot_measure_lt` を `measure_lt` に入れて `GoldenZeroSectorStrictDescent p` を構築する。

7. 最後にそれを `Nonempty` で包んで返す。

## `next` packet の各フィールド

```lean
let next : GoldenZeroSectorDescentPacket := {
  base := gamma
  t := u
  D := v
  t_pos := hu
  D_pos := hv
  coprime_coords := hcop
  snd_eq := Or.inl hsnd
  H_eq := hH
  five_not_dvd_norm := h5norm }
```

ここで重要なのは、`next` が merely smaller な整数組ではなく、source と同じ descent invariant を完全に満たしていることである。

`base := gamma` により第五根そのものを次世代基底にし、`t := u`, `D := v` により 0394 で得た第五冪分離を packet のパラメータへ再符号化する。

`snd_eq := Or.inl hsnd` は `gamma.snd = 5*u^5` の正符号 branch を採用する。0390 で `gamma.snd > 0` が確定しているため、ここでは負符号 branch は不要である。

## Lean 固有の処理

### `obtain`

```lean
obtain ⟨gamma, hroot, hnorm⟩ := p.exists_lift_eq_fifthPower
```

および

```lean
obtain ⟨u, v, hu, hv, hsnd, hH⟩ := ...
```

で existential package を直ちに分解している。これにより後続の record construction が読みやすくなっている。

### `exact_mod_cast`

`hnorm` を rewrite した後、整数可除性

```lean
(5 : ℤ) ∣ (p.D : ℤ)
```

を自然数可除性

```lean
5 ∣ p.D
```

へ移すために使用される。

### `let next`

次 packet を局所定義してから strict descent structure に格納することで、巨大な nested record literal を避けている。

### `Nonempty`

結果を

```lean
Nonempty (GoldenZeroSectorStrictDescent p)
```

として返すため、後続では

```lean
obtain ⟨step⟩ := q.strictDescent
```

だけで witness を取り出せる。

## 冗長・重複箇所

全体として重複は少なく、0396 は既存 API の組立てに徹している。

もっとも明確な重複候補は

```lean
have h5norm : ¬ (5 : ℤ) ∣ goldenNorm gamma := by
  rw [hnorm]
  intro h
  exact p.five_not_dvd_D (by exact_mod_cast h)
```

である。これは `hnorm : goldenNorm gamma = p.D` と `p.five_not_dvd_D` の単純な transport なので、同形の処理が他でも現れるなら

```lean
five_not_dvd_norm_of_norm_eq_D
```

のような helper に切り出せる。

一方 `next` の record literal は、packet invariant の全項目を監査可能にするため明示的であることに価値があり、過度に自動化しない方が証明構造は見やすい。

## 最適化候補

最も自然な最適化候補は、第五根から次 packet を構築する部分を別 constructor に分離することである。

例えば概念的には

```lean
def GoldenZeroSectorDescentPacket.ofFifthRoot
    (p : GoldenZeroSectorDescentPacket)
    (gamma : GoldenInt)
    ... : GoldenZeroSectorDescentPacket := ...
```

を用意すれば、`strictDescent` は root extraction と strict decrease の接続だけに集中できる。

ただし現状の theorem は短く、各 invariant がどの補題から供給されるかが一目で分かる。したがって、同じ constructor pattern が別の descent でも繰り返されるまでは現状の明示形が妥当である。

また `h5norm` は 0392 `fifthRoot_five_not_dvd_H` とは別の性質であり、ここで必要なのは quartic factor ではなく `goldenNorm gamma` の 5 非可除性である。両者を統合し過ぎると依存関係が不透明になるため注意が必要である。

## 必要 Mathlib import と import 最適化候補

standalone 正本全体は

```lean
import Mathlib
```

を使用している。

0396 自身が直接利用する Mathlib 的機能は主に

- `Nonempty`
- existential pattern matching
- `rw`
- `exact_mod_cast`

である。

算術的な重い処理はすべて直前までの DkMath theorem に封じ込められているため、この theorem 単体の import 要求は比較的軽い。

ただし `GoldenZeroSectorDescentPacket`、`GoldenZeroSectorStrictDescent`、第五根関連 theorem の定義元を含む実モジュール依存が必要であり、Lean build を行わない今回の条件では厳密な最小 Mathlib import は確定しない。

import 最適化を行うなら、まず `SignedGoldenZeroSectorDescent` 相当モジュールを DkMath 側の必要依存だけで import し、`exact_mod_cast` に必要な tactic import を追加する形で検証するのが自然である。

## Comparator challenge 化の可否

**非常に適している。**

0395 単体は structure 宣言だけだったが、0396 は既存 API を正しく組み合わせて dependent record を構築する必要がある。

challenge としては、次を前提 API として固定する。

- `exists_lift_eq_fifthPower`
- `fifthRoot_power_split`
- `fifthRoot_coprime_coords`
- `five_not_dvd_D`
- `fifthRoot_measure_lt`

そして目標を

```lean
Nonempty (GoldenZeroSectorStrictDescent p)
```

とする。

評価点は

- existential witness の分解
- invariant の正しい再配置
- `ℕ` / `ℤ` 可除性 transport
- dependent structure construction
- strict measure theorem の再利用

であり、証明探索を必要としつつ局所的に完結している。

Comparator 用 challenge としては **0395+0396 の組** が descent API 設計を評価する良い単位である。

## 次に読むべき宣言

次は

```lean
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

である。

0396 が「任意の packet からより小さい packet が存在する」を certified step として構築したことで、次の theorem では arithmetic の詳細を一切展開せず、自然数 measure に対する strong induction だけで矛盾を閉じられる。

流れは

$$
\text{recursive packet}
\longrightarrow
\text{strictly smaller recursive packet}
\longrightarrow
\text{well-founded contradiction}
$$

となり、次の宣言が zero-sector 無限降下の論理的 closure である。