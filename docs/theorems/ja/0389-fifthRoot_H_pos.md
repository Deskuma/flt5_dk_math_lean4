# 0389 `GoldenZeroSectorDescentPacket.fifthRoot_H_pos`

## 宣言種別

`theorem`

`GoldenZeroSectorDescentPacket` namespace 内に置かれた、第五根 `gamma` の quartic factor が厳密に正であることを示す補題である。

## Lean コード

```lean
theorem fifthRoot_H_pos
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5) :
    0 < goldenFifthSndFactor gamma.fst gamma.snd := by
  have hEq := p.fifthRoot_snd_factor_eq gamma hroot
  have hsSq : 0 < p.base.snd ^ 2 := sq_pos_of_ne_zero p.snd_ne_zero
  have hnonneg := goldenFifthSndFactor_nonneg gamma.fst gamma.snd
  have hne : goldenFifthSndFactor gamma.fst gamma.snd ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hEq
    omega
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)
```

## Lean の型

概念的には次の型である。

```lean
GoldenZeroSectorDescentPacket.fifthRoot_H_pos :
  (p : GoldenZeroSectorDescentPacket) →
  (gamma : GoldenInt) →
  goldenZeroSectorLift p.base = goldenPow gamma 5 →
  0 < goldenFifthSndFactor gamma.fst gamma.snd
```

入力は descent packet `p`、黄金整数 `gamma`、そして quadratic lift が `gamma^5` に一致する証明 `hroot` である。出力は `gamma` に付随する quartic factor の整数上の厳密正値性である。

## 数学的主張

`gamma=(a,b)`、`p.base=(r,s)` と書く。

0388 `fifthRoot_snd_factor_eq` により

$$
s^2 = 5bH(a,b)
$$

が成立する。ここで

$$
H(a,b)
 = a^4+2a^3b+4a^2b^2+3ab^3+b^4.
$$

一方、packet の `snd_ne_zero` により $s\neq0$ なので

$$
s^2>0.
$$

また一般補題 `goldenFifthSndFactor_nonneg` により

$$
H(a,b)\ge0
$$

である。

もし $H(a,b)=0$ なら、積恒等式は

$$
s^2=5b\cdot0=0
$$

となり $s^2>0$ に矛盾する。したがって

$$
H(a,b)\neq0.
$$

非負性と非零性を合わせて

$$
H(a,b)>0
$$

を得る。

## 証明全体での役割

0387 `exists_lift_eq_fifthPower` で quadratic lift が純粋な第五冪

$$
T(r,s)=\gamma^5
$$

として表された。0388 はその第二座標を取り出して

$$
s^2=5bH(a,b)
$$

という整数積恒等式へ戻した。

0389 はこの積恒等式から `H(a,b)` の符号を確定する段階である。これは単なる補助的な positivity ではなく、次の `fifthRoot_snd_pos` で $b>0$ を導くために必要である。実際、

$$
s^2>0,
\qquad
H(a,b)>0,
\qquad
s^2=5bH(a,b)
$$

が揃えば $b>0$ が従う。

その後の descent では `gamma.snd.natAbs` を新しい measure として扱うため、第二座標の正符号を確定しておくことが重要である。したがって本 theorem は、第五根の algebraic existence から well-founded descent に必要な order information を抽出する中間橋である。

## 直接依存する定義・補題

直接使われる主な宣言は次の通りである。

- `GoldenZeroSectorDescentPacket`
- `GoldenInt`
- `goldenZeroSectorLift`
- `goldenPow`
- `goldenFifthSndFactor`
- `GoldenZeroSectorDescentPacket.fifthRoot_snd_factor_eq`
- `GoldenZeroSectorDescentPacket.snd_ne_zero`
- `goldenFifthSndFactor_nonneg`
- `sq_pos_of_ne_zero`
- `lt_of_le_of_ne`
- `Ne.symm`

特に直前の 0388 が与える

```lean
p.base.snd ^ 2 =
  5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd
```

が主要入力である。

一般補題 `goldenFifthSndFactor_nonneg` は、quartic factor の恒等式

$$
16H(r,s)
 = X^4+10X^2s^2+5s^4,
\qquad X=2r+s
$$

から、右辺が平方・偶数冪の非負和であることを用いて $H(r,s)\ge0$ を保証している。

## 証明・構築の流れ

1. 0388 の積恒等式を取得する。

   ```lean
   have hEq := p.fifthRoot_snd_factor_eq gamma hroot
   ```

2. packet の第二座標が非零であることから、その平方が正であることを得る。

   ```lean
   have hsSq : 0 < p.base.snd ^ 2 := sq_pos_of_ne_zero p.snd_ne_zero
   ```

3. quartic factor の一般的な非負性を取得する。

   ```lean
   have hnonneg := goldenFifthSndFactor_nonneg gamma.fst gamma.snd
   ```

4. quartic factor が 0 だと仮定する。

   ```lean
   have hne : goldenFifthSndFactor gamma.fst gamma.snd ≠ 0 := by
     intro hzero
   ```

5. `hEq` の quartic factor を 0 に書き換える。

   ```lean
   rw [hzero, mul_zero] at hEq
   ```

   これで `hEq` は実質的に `p.base.snd ^ 2 = 0` となる。

6. `hsSq : 0 < p.base.snd ^ 2` と矛盾させる。

   ```lean
   omega
   ```

7. `H≥0` と `H≠0` を組み合わせ、`H>0` を得る。

   ```lean
   exact lt_of_le_of_ne hnonneg (Ne.symm hne)
   ```

## Lean 固有の処理

### `sq_pos_of_ne_zero`

数学では $s\neq0\Rightarrow s^2>0$ は自明だが、Lean ではこの order fact を明示的な補題 `sq_pos_of_ne_zero` で取り出している。

`p.snd_ne_zero` は packet invariant `s=\pm5t^5` と `t>0` から既に証明済みなので、本 theorem ではその API を再利用している。

### `rw [hzero, mul_zero] at hEq`

`hzero : H=0` を積恒等式へ代入し、右辺を 0 まで正規化する。quartic polynomial 自体を展開する必要はない。

### `omega`

ここでの `omega` は polynomial arithmetic を解いているのではなく、既に得られている

```lean
hsSq : 0 < p.base.snd ^ 2
hEq  : p.base.snd ^ 2 = 0
```

という整数の線形 order contradiction を閉じている。

### `lt_of_le_of_ne`

Lean の `lt_of_le_of_ne` は `a ≤ b` と `a ≠ b` の向きに注意が必要である。ここでは `hnonneg : 0 ≤ H` と `Ne.symm hne : 0 ≠ H` を与え、`0 < H` を得ている。

## 冗長・重複箇所

本 theorem は短く、数学的重複は少ない。ただし `hsSq` は `hne` を示す内部ブロックでしか使わないため、局所化できる。

また `H≥0` と積恒等式から `H≠0` を示すパターンは、後続で同様の positivity bridge が増えるなら helper 化の余地がある。ただし現時点では抽象化するほどの重複は確認できない。

`hEq` を 0 に書き換えた後に `omega` を使う代わりに、`hsSq.ne'` などを用いてより直接的に contradiction を構成できる可能性もあるが、実際の型が期待通り簡約されるかは Lean build を行っていないため未確認である。

## 最適化候補

### 1. 非零性証明の簡潔化

例えば概念的には

```lean
have hne : goldenFifthSndFactor gamma.fst gamma.snd ≠ 0 := by
  intro hzero
  rw [hzero, mul_zero] at hEq
  exact (ne_of_gt hsSq) hEq
```

に近い形へできる可能性がある。ただし `hEq` の向きや簡約結果に応じて `hEq.symm` が必要になる可能性があり、未検証である。

### 2. quartic positivity API の強化

現在は一般補題が `H≥0`、本 theorem が packet-specific に `H>0` を示している。`H=0` の分類を一般定理として得られるなら、より構造的に strict positivity を導ける可能性がある。しかし現在の証明目的には既存の短い contradiction が十分である。

### 3. order chain の整理

0389 `fifthRoot_H_pos` と 0390 `fifthRoot_snd_pos` は連続して積恒等式から因子の符号を確定する。将来的に descent API を整理するなら、

```lean
0 < gamma.snd ∧
0 < goldenFifthSndFactor gamma.fst gamma.snd
```

をまとめて返す補題を追加する設計も考えられる。ただし個別 lemma の方が再利用性は高い。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は現在

```lean
import Mathlib
```

を使用している。

本 theorem 自体が必要とする Mathlib 機能は主として、整数の順序・平方の正値性、基本 rewrite、`omega` tactic である。したがって standalone 全体より小さい import へ縮小できる可能性は高い。

候補としては整数 order/algebra と `Mathlib.Tactic.Omega` 周辺が中心になると考えられるが、`GoldenInt`、packet、quartic 非負性などのプロジェクト内依存がさらにどの Mathlib module を transitively 要求するかは、この実行では Lean build を行わないため厳密には確認していない。

したがって **現時点で確認できる必要 import は `Mathlib`、最小 import は未確定** とする。

## Comparator challenge 化の可否

**可。特に小規模 challenge に向いている。**

challenge の核は、次の既知情報だけを与えて strict positivity を復元させる形にできる。

```lean
hEq : s ^ 2 = 5 * b * H
hs0 : s ≠ 0
hnonneg : 0 ≤ H
⊢ 0 < H
```

必要な発想は、

1. `s≠0` から `s^2>0`
2. `H=0` を仮定すると積恒等式から `s^2=0`
3. 矛盾により `H≠0`
4. `H≥0` と合わせて `H>0`

という短い order/divisibility-independent reasoning である。

FLT5 固有の定義を残した challenge と、抽象整数変数だけに落とした micro challenge の両方が作れる。Comparator 用には後者の方が proof-search の純粋比較に適している。

## 次に読むべき宣言

次は **0390 `GoldenZeroSectorDescentPacket.fifthRoot_snd_pos`** である。宣言種別は `theorem`。

```lean
theorem fifthRoot_snd_pos
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5) :
    0 < gamma.snd := by
  have hEq := p.fifthRoot_snd_factor_eq gamma hroot
  have hsSq : 0 < p.base.snd ^ 2 := sq_pos_of_ne_zero p.snd_ne_zero
  have hH := p.fifthRoot_H_pos gamma hroot
  nlinarith
```

0388 の

$$
s^2=5bH(a,b)
$$

と今回の

$$
H(a,b)>0
$$

を使い、

$$
b>0
$$

を確定する。これにより第五根の第二座標は `natAbs` を外して正の整数量として扱えるようになり、後続の strict measure decrease へ進む。
