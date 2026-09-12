# 0399 `goldenZeroSectorCandidate_false`

## 宣言種別

`theorem`

`GoldenZeroSectorCandidate` が存在しないことを、0398 の candidate→descent-packet 変換と 0397 の無限降下閉包を合成して示す定理である。

## Lean コード

```lean
/-- The deterministic candidate emitted by inversion is impossible. -/
theorem goldenZeroSectorCandidate_false
    (p : GoldenZeroSectorCandidate) : False :=
  goldenZeroSectorDescentPacket_false
    (goldenZeroSectorDescentPacket_of_candidate p)
```

## Lean の型

```lean
goldenZeroSectorCandidate_false :
  GoldenZeroSectorCandidate → False
```

すなわち、任意の `p : GoldenZeroSectorCandidate` を仮定すると `False` が得られる。

論理的には

$$
\neg\,\exists p,\; p : \mathrm{GoldenZeroSectorCandidate}
$$

に相当する排除定理である。

## 数学的主張

`GoldenZeroSectorCandidate` は、zero-sector inversion から得られた整数座標と十乗分解、互いに素性、norm 条件などをまとめた certified candidate である。

0398 `goldenZeroSectorDescentPacket_of_candidate` は、その candidate から recursive descent invariant を満たす packet

$$
P(p):=\operatorname{goldenZeroSectorDescentPacket\_of\_candidate}(p)
$$

を構成する。

0397 `goldenZeroSectorDescentPacket_false` は、任意の descent packet $q$ に対して

$$
q : \mathrm{GoldenZeroSectorDescentPacket}
\Longrightarrow
\bot
$$

を示している。

したがって 0399 は単に

$$
p
\longmapsto
P(p)
\longmapsto
\bot
$$

を合成する。

この定理自身では新しい可除性計算、黄金整数環の演算、第五冪分離、measure 評価は一切行わない。それらはすべて 0398 以前で完了している。

## 証明全体での役割

0399 は `SignedGoldenZeroSectorDescent` 部分の **公開された最終排除点** である。

直前までの流れは概略

$$
\mathrm{GoldenZeroSectorCandidate}
\xrightarrow{0398}
\mathrm{GoldenZeroSectorDescentPacket}
\xrightarrow{0397}
\bot
$$

である。

0397 が「recursive invariant を満たす packet は存在できない」という一般的な無限降下閉包を担当し、0398 が「実際の inversion candidate はその invariant に入る」ことを担当した。0399 はこの二つの API を接続し、元の candidate 型そのものを消去する。

この分離は重要である。無限降下の well-foundedness と、candidate から packet への算術的 transport が別々に証明されているため、最終排除は一行の合成で済む。

## 直接依存する定義・補題

直接依存は非常に少ない。

- `GoldenZeroSectorCandidate`
- `goldenZeroSectorDescentPacket_of_candidate` — 0398
- `GoldenZeroSectorDescentPacket`
- `goldenZeroSectorDescentPacket_false` — 0397

証明本体が直接使用しているのは実質的に後二つの関数適用だけである。

0399 は間接的には 0397・0398 が依存する zero-sector inversion、fifth-power re-entry、coprimality、power split、strict descent、`Nat.strong_induction_on` の全チェーンを受け継ぐが、それらを再展開はしない。

## 証明の流れ

証明は term-style で完結している。

1. `p : GoldenZeroSectorCandidate` を受け取る。
2. 0398 を適用して

   ```lean
   goldenZeroSectorDescentPacket_of_candidate p
   ```

   を得る。型は `GoldenZeroSectorDescentPacket`。
3. その packet を 0397

   ```lean
   goldenZeroSectorDescentPacket_false
   ```

   に渡す。
4. 戻り値は `False` なので goal がそのまま閉じる。

Lean の elaboration を型として書けば

```lean
goldenZeroSectorDescentPacket_of_candidate p
  : GoldenZeroSectorDescentPacket
```

および

```lean
goldenZeroSectorDescentPacket_false
  : GoldenZeroSectorDescentPacket → False
```

ゆえに関数合成が成立する、というだけである。

## Lean 固有の処理

### tactic block を使わない term proof

この theorem は

```lean
:=
  goldenZeroSectorDescentPacket_false
    (goldenZeroSectorDescentPacket_of_candidate p)
```

という直接の proof term である。

`by`、`exact`、`rw`、`simp` などは不要で、Curry–Howard 対応の最も素直な形で

$$
A\to B,\quad B\to\bot
\quad\Rightarrow\quad
A\to\bot
$$

を表している。

### implicit argument や coercion がない

0397・0398 の境界で target/source type が正確に一致しているため、cast、`simpa`、型注釈、namespace 補助は不要である。これは前段の API 設計がうまく揃っていることを示す。

### `False` を返す設計

結論を `¬ ...` という外側の否定ではなく、candidate `p` を引数に取って `False` を返す theorem にしているため、後続の receiver 側では candidate を得た時点で直接消去できる。

## 冗長・重複箇所

0399 自体には実質的な冗長性はない。二つの既存宣言の最小合成になっている。

あえて別表現にするなら

```lean
theorem goldenZeroSectorCandidate_false
    (p : GoldenZeroSectorCandidate) : False := by
  exact goldenZeroSectorDescentPacket_false
    (goldenZeroSectorDescentPacket_of_candidate p)
```

とも書けるが、現在の term-style の方が短く、依存関係も明確である。

また一般的な関数合成 `Function.comp` を用いることも理論上可能だが、この一箇所のために抽象化するとかえって読みづらい。

## 最適化候補

### 1. 現状維持が最有力

コードサイズ・可読性・依存の透明性の面で、現在の実装はほぼ最小である。局所的な最適化余地はない。

### 2. API 名の対称性

将来 descent 層を再利用する場合、

```lean
candidateToPacket
packetFalse
candidateFalse
```

のような一般化された interface を用意する設計は考えられる。ただし現状の名前は数学的対象を明示しており、FLT5 の監査用途ではむしろ有利である。

### 3. 汎用 contradiction bridge

多数の同型パターンが現れるなら

```lean
(A → B) → (B → False) → A → False
```

型の helper を用意できるが、これは単なる関数合成なので、0399 を短くする目的だけでは価値がない。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は現在

```lean
import Mathlib
```

を使用している。

ただし 0399 の proof term 自身は、特殊な Mathlib theorem・tactic・typeclass を直接使用していない。必要なのは `GoldenZeroSectorCandidate`、0398、0397 がすでに環境に存在することだけである。

したがって theorem 単体の観点では **追加の specialized Mathlib import は不要** と考えられる。実際の source module を最小 import 化する場合には、0397・0398 およびそれらの型を提供する先行 local module の import が必要になる。

今回は Lean build を行わない条件なので、`Mathlib` をどの個別 module まで縮小できるかという厳密な最小 import 集合は未確認である。

## Comparator challenge 化の可否

**可能だが、単独 challenge としては難度が低い。**

最小 challenge は

```lean
variable {Candidate Packet : Type}
variable (toPacket : Candidate → Packet)
variable (packetFalse : Packet → False)

example (p : Candidate) : False :=
  packetFalse (toPacket p)
```

程度まで抽象化できる。

これは Lean の関数適用・型整合性を見るには有効だが、FLT5 の数論的能力を測る challenge にはならない。

Comparator 用には 0398 と 0399 を一体化し、candidate の field から packet を構築して最後に contradiction へ渡すところまで課題化する方が適切である。その場合は structure construction、整数/自然数 cast、冪の正規化、符号付き可除性 transport まで含まれ、実装比較として意味のある難度になる。

## 次に読むべき宣言

次は **0400 `GoldenZeroSectorArithmeticExclusion`**、種別は `abbrev` である。

```lean
abbrev GoldenZeroSectorArithmeticExclusion : Prop :=
  ∀ (r s : ℤ) (a b : ℕ),
    0 < a →
    0 < b →
    Nat.Coprime a b →
    ¬ 5 ∣ b →
    (goldenNorm ⟨r, s⟩ = (b : ℤ) ∨ goldenNorm ⟨r, s⟩ = -(b : ℤ)) →
    s * goldenFifthSndFactor r s = -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10 →
    Nat.Coprime r.natAbs s.natAbs →
    (∃ c d : ℕ,
      s.natAbs = 5 ^ 6 * c ^ 10 ∧
      (goldenFifthSndFactor r s).natAbs = d ^ 10) →
    False
```

0399 で concrete `GoldenZeroSectorCandidate` の不可能性が閉じた後、0400 からは `SignedGoldenClosure` 層へ移り、その算術内容を receiver interface として公開する。