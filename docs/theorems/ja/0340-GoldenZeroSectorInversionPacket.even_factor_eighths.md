# 0340 — `GoldenZeroSectorInversionPacket.even_factor_eighths`

## 宣言種別

この宣言は **`theorem`** である。

```lean
/-- After removing eight, the two even-branch factors have opposite parity. -/
theorem GoldenZeroSectorInversionPacket.even_factor_eighths
    (p : GoldenZeroSectorInversionPacket) (hc : Even p.source.c) :
    ∃ A1 B1 : ℕ,
      p.source.A0 = 8 * A1 ∧ p.source.B0 = 8 * B1 ∧
      ((Odd A1 ∧ Even B1) ∨ (Even A1 ∧ Odd B1)) := by
  rcases p.eight_dvd_factors hc with ⟨h8A, h8B⟩
  rcases h8A with ⟨A1, hA⟩
  rcases h8B with ⟨B1, hB⟩
  have hdiff : B1 = A1 + p.source.d ^ 5 := by
    apply Nat.mul_left_cancel (show 0 < 8 by norm_num)
    calc
      8 * B1 = p.source.B0 := hB.symm
      _ = p.source.A0 + 8 * p.source.d ^ 5 := p.factor_difference
      _ = 8 * (A1 + p.source.d ^ 5) := by rw [hA]; ring
  have hdOdd : Odd (p.source.d ^ 5) := p.source.d_odd.pow
  rcases Nat.even_or_odd A1 with hAeven | hAodd
  · have hBodd : Odd B1 := by rw [hdiff]; exact hAeven.add_odd hdOdd
    exact ⟨A1, B1, hA, hB, Or.inr ⟨hAeven, hBodd⟩⟩
  · have hBeven : Even B1 := by rw [hdiff]; exact hAodd.add_odd hdOdd
    exact ⟨A1, B1, hA, hB, Or.inl ⟨hAodd, hBeven⟩⟩
```

## Lean の型

本体の型は

```lean
(p : GoldenZeroSectorInversionPacket) →
Even p.source.c →
∃ A1 B1 : ℕ,
  p.source.A0 = 8 * A1 ∧
  p.source.B0 = 8 * B1 ∧
  ((Odd A1 ∧ Even B1) ∨ (Even A1 ∧ Odd B1))
```

である。

すなわち even-`c` branch では、0339 で得た $8\mid A_0$ と $8\mid B_0$ を実際の quotient `A1`, `B1` として取り出したあと、その二つが必ず opposite parity を持つことまで保証する。

## 数学的主張

0339 から

$$
A_0=8A_1,
\qquad
B_0=8B_1
$$

と書ける。

一方、反転 packet の差分関係 `p.factor_difference` は

$$
B_0=A_0+8d^5
$$

という形である。上の二式を代入し、正の共通因子 8 を消去すると

$$
B_1=A_1+d^5
$$

を得る。

`p.source.d_odd` により $d$ は奇数なので、第五冪 $d^5$ も奇数である。したがって $A_1$ と $B_1=A_1+d^5$ は必ず逆の parity を持つ。

よって

$$
(\operatorname{Odd}(A_1)\land\operatorname{Even}(B_1))
\lor
(\operatorname{Even}(A_1)\land\operatorname{Odd}(B_1))
$$

が成立する。

## FLT5 証明全体での役割

この theorem は **even-`c` branch を exact factorization の二つの枝へ分ける分岐点** である。

0339 `GoldenZeroSectorInversionPacket.eight_dvd_factors` は `A0`,`B0` が双方とも 8 を含むことだけを示した。今回、その 8 を除いた quotient に parity 情報を付与する。

この opposite parity が直後の `nonempty_even_factorData` で使われ、

- `A1` odd / `B1` even の場合は `B1 = 2 * B2` とさらに 2 を右側から取り出す
- `A1` even / `B1` odd の場合は `A1 = 2 * A2` と左側から取り出す

という二つの exact fifth-power branch へ進む。

最終的には `GoldenZeroSectorFactorData.evenLeftLow` と `.evenRightLow` の constructor に対応する。

流れは

```text
c even
  │
  ▼
8 ∣ A0, 8 ∣ B0
  │
  ▼
A0 = 8*A1, B0 = 8*B1
  │
  ▼
B1 = A1 + d^5
  │
  ▼
d^5 odd
  │
  ▼
A1, B1 have opposite parity
  │
  ├── A1 odd,  B1 even
  └── A1 even, B1 odd
```

である。

## 直接依存する定義・補題

### `GoldenZeroSectorInversionPacket.eight_dvd_factors`

0339 の theorem。仮定 `Even p.source.c` から

```lean
8 ∣ p.source.A0 ∧ 8 ∣ p.source.B0
```

を供給する。今回の `A1`,`B1` は、この可除性 witness から直接取り出される。

### `p.factor_difference`

反転因子の exact difference

```lean
p.source.B0 = p.source.A0 + 8 * p.source.d ^ 5
```

を供給する。8 を消去した quotient equation

```lean
B1 = A1 + p.source.d ^ 5
```

の唯一の算術的核心である。

### `p.source.d_odd`

`d` が奇数であることを供給する。`.pow` によって第五冪も奇数であることを得る。

### `Nat.mul_left_cancel`

`8 * B1 = 8 * (...)` から共通因子 8 を消去するために用いる。Lean では自然数乗法の cancellation に正性を明示している。

### `Nat.even_or_odd`

`A1` の parity を完全に二分する。二つの branch はそれぞれ `B1` の parity を一意に決める。

### `Even.add_odd`, `Odd.add_odd`

偶数と奇数、奇数と奇数の和の parity を処理する。

### `ring`

`A0 = 8*A1` を `factor_difference` に代入した後、

```lean
8 * A1 + 8 * d^5 = 8 * (A1 + d^5)
```

という多項式正規化を閉じる。

## 証明または構築の流れ

### 1. 8 の可除性を quotient に変換する

```lean
rcases p.eight_dvd_factors hc with ⟨h8A, h8B⟩
rcases h8A with ⟨A1, hA⟩
rcases h8B with ⟨B1, hB⟩
```

により

```lean
hA : p.source.A0 = 8 * A1
hB : p.source.B0 = 8 * B1
```

を得る。

### 2. quotient 間の差分式を得る

`p.factor_difference` に `hA`, `hB` を代入して

$$
8B_1=8(A_1+d^5)
$$

を作り、`Nat.mul_left_cancel` で 8 を消去して

$$
B_1=A_1+d^5
$$

を得る。

### 3. `d^5` の奇性を取得する

```lean
have hdOdd : Odd (p.source.d ^ 5) := p.source.d_odd.pow
```

とし、第五冪でも parity が保存されることを利用する。

### 4. `A1` の parity を場合分けする

```lean
rcases Nat.even_or_odd A1 with hAeven | hAodd
```

で完全な二分を行う。

### 5. `B1` の反対 parity を導く

`A1` が偶数なら

$$
B_1=A_1+d^5
$$

は奇数、`A1` が奇数なら `B1` は偶数である。

### 6. existential packet を返す

同じ `A1`,`B1` と factor equations を保持したまま、対応する disjunction branch を返す。

## Lean 固有の処理

### 可除性 witness の直接展開

Lean の `a ∣ b` は existential witness を持つため、`rcases h8A with ⟨A1, hA⟩` により quotient をそのまま後続計算へ取り込める。ここでは抽象的な「8 で割った値」ではなく、証明付きの具体的 `A1`,`B1` が生成される。

### cancellation の正性証明

```lean
apply Nat.mul_left_cancel (show 0 < 8 by norm_num)
```

では、自然数上で左因子 8 を消去できることを Lean に明示している。

### parity の型としての分岐

`Nat.even_or_odd A1` は単なる数値判定ではなく、`Even A1 ∨ Odd A1` の proof object を生成する。その proof object を `.add_odd` に直接渡して `B1` の parity proof を構築している。

### `rw [hdiff]` による parity transport

`B1` の parity は直接計算せず、exact equality `hdiff` で `B1` を `A1 + d^5` に書き換えてから既存の parity lemma を適用する。このため arithmetic と parity reasoning が分離されている。

## 冗長・重複箇所

二つの parity branch は完全な鏡像で、

```lean
have hBodd ...
have hBeven ...
```

の部分だけが異なる。

ただし、出力型そのものが disjunction

```lean
(Odd A1 ∧ Even B1) ∨ (Even A1 ∧ Odd B1)
```

であるため、現在の明示的な二 branch は構造をよく反映しており、不自然な重複ではない。

また `hA`, `hB` を一度取得してから `hdiff` を作る手順も、後続で両式をそのまま返すため必要である。

## 最適化候補

1. `B1 = A1 + odd` なら `A1` と `B1` は opposite parity、という一般補題を用意すれば最後の `Nat.even_or_odd` 以下を短縮できる。類似の parity split が他所にもあるなら価値がある。

2. `Nat.mul_left_cancel` と `calc` で quotient equation を作る部分は十分明確であり、過度な自動化より現在の形が proof audit には適している。

3. 出力を disjunction ではなく専用 inductive branch label と dependent data に直接変換する設計も可能だが、この theorem は arithmetic layer と `GoldenZeroSectorFactorData` construction layer の間の境界として単純な existential + disjunction を保つ利点がある。

4. `ring` はこの一箇所だけなら妥当である。単純な distributivity rewrite へ置き換えることもできるが、可読性が必ずしも向上するとは限らない。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

今回の theorem が直接利用する主要な機能は

- `Nat` の divisibility と multiplication cancellation
- `Even` / `Odd`
- `Nat.even_or_odd`
- parity の加法補題と冪補題
- `norm_num`
- `ring`

である。

したがって理論上は `Mathlib` 全体より小さい import 集合へ縮小できる可能性が高い。ただし、この museum 作業では Lean ビルドを行わないため、正確な最小 import の組合せは確認していない。個別 module 名を断定するのは避ける。

また元の source module は standalone manifest 上では `DkMath/FLT/Five/SignedGoldenZeroSectorFactorization.lean` に対応している。

## Comparator challenge 化の可否

**適している。**

特に challenge として独立させやすい核心は次である。

> 自然数 $A_0,B_0,d,A_1,B_1$ が
> $A_0=8A_1$、$B_0=8B_1$、$B_0=A_0+8d^5$ を満たし、$d$ が奇数なら、$A_1$ と $B_1$ は opposite parity であることを示せ。

これは FLT5 固有の golden-order machinery をほぼ取り除いても成立する、小さく checkable な arithmetic/parity problem である。

Comparator では、

- 8 の cancellation をどう行うか
- `Odd (d^5)` をどう得るか
- parity split を明示するか一般補題で閉じるか

を比較できる。

## 次に読むべき宣言

次は

```lean
private theorem nonempty_even_factorData
    (p : GoldenZeroSectorInversionPacket) (hc : Even p.source.c) :
    Nonempty (GoldenZeroSectorFactorData p) := by
```

である。

今回得た opposite parity を用いて even branch をさらに

- `A1` odd / `B1` even
- `A1` even / `B1` odd

へ分解し、偶数側から追加の因子 2 を抽出する。そして coprime fifth-power splitting を適用して `GoldenZeroSectorFactorData.evenLeftLow` または `.evenRightLow` を実際に構築する。

したがって 0340 は、0339 の「8 が両方に入る」という粗い二進情報と、次の exact fifth-power certificate construction を接続する parity splitter である。
