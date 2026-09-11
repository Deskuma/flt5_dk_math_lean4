# 0390 `GoldenZeroSectorDescentPacket.fifthRoot_snd_pos`

## 宣言種別

`theorem`

`GoldenZeroSectorDescentPacket` namespace 内に置かれた、第五根 `gamma` の第二座標が厳密に正であることを示す補題である。

## Lean コード

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

## Lean の型

概念的には次の型である。

```lean
GoldenZeroSectorDescentPacket.fifthRoot_snd_pos :
  (p : GoldenZeroSectorDescentPacket) →
  (gamma : GoldenInt) →
  goldenZeroSectorLift p.base = goldenPow gamma 5 →
  0 < gamma.snd
```

入力は descent packet `p`、黄金整数 `gamma`、および quadratic lift が `gamma^5` に一致する証明 `hroot` である。出力は `gamma` の第二座標 `gamma.snd : ℤ` の厳密正値性である。

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

また packet の `snd_ne_zero` から

$$
s\neq0,
$$

したがって

$$
s^2>0
$$

である。

さらに直前の 0389 `fifthRoot_H_pos` により

$$
H(a,b)>0
$$

が既に得られている。

よって

$$
0<s^2=5bH(a,b)
$$

であり、$5>0$ かつ $H(a,b)>0$ なので

$$
b>0
$$

でなければならない。これが Lean の結論 `0 < gamma.snd` である。

## 証明全体での役割

0387 `exists_lift_eq_fifthPower` は quadratic lift を

$$
T(r,s)=\gamma^5
$$

という純粋な第五冪へ変換した。0388 はその第二座標を射影して

$$
s^2=5bH(a,b)
$$

を得た。0389 はこの積の quartic factor について

$$
H(a,b)>0
$$

を確定した。

0390 は残る因子 $b=\gamma_{\mathrm{snd}}$ の符号を確定する段階である。これにより第五根 `gamma` の第二座標を単なる整数ではなく正の整数方向の量として扱える。

後続の descent では `gamma.fst.natAbs` と `gamma.snd.natAbs` の coprimality、第二座標に対する五進分解、さらに新しい descent packet の構築と strict measure decrease が必要になる。ここで `gamma.snd>0` が得られていると

$$
|\gamma_{\mathrm{snd}}|=\gamma_{\mathrm{snd}}
$$

として符号を除去できるため、整数環上の fifth-power factorization を自然数の well-founded measure へ戻す際の重要な order bridge になる。

## 直接依存する定義・補題

直接使われる主な宣言は次の通りである。

- `GoldenZeroSectorDescentPacket`
- `GoldenInt`
- `goldenZeroSectorLift`
- `goldenPow`
- `GoldenZeroSectorDescentPacket.fifthRoot_snd_factor_eq`
- `GoldenZeroSectorDescentPacket.snd_ne_zero`
- `GoldenZeroSectorDescentPacket.fifthRoot_H_pos`
- `sq_pos_of_ne_zero`
- `nlinarith`

主要な二つの入力は

```lean
p.fifthRoot_snd_factor_eq gamma hroot
```

が与える

```lean
p.base.snd ^ 2 =
  5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd
```

と、0389 が与える

```lean
0 < goldenFifthSndFactor gamma.fst gamma.snd
```

である。

## 証明・構築の流れ

1. 0388 の第二座標積恒等式を取得する。

   ```lean
   have hEq := p.fifthRoot_snd_factor_eq gamma hroot
   ```

2. packet の第二座標が非零であることから平方の正値性を得る。

   ```lean
   have hsSq : 0 < p.base.snd ^ 2 := sq_pos_of_ne_zero p.snd_ne_zero
   ```

3. 0389 から quartic factor の厳密正値性を取得する。

   ```lean
   have hH := p.fifthRoot_H_pos gamma hroot
   ```

4. 次の三情報を `nlinarith` に渡す。

   $$
   s^2=5bH,
   \qquad
   s^2>0,
   \qquad
   H>0.
   $$

5. $b\le0$ なら右辺 $5bH\le0$ となり左辺の正値性に反するため、`0 < gamma.snd` を得る。

   ```lean
   nlinarith
   ```

## Lean 固有の処理

### `sq_pos_of_ne_zero`

`p.snd_ne_zero` は `p.base.snd ≠ 0` を与える。Lean では整数の平方が正であることを

```lean
sq_pos_of_ne_zero p.snd_ne_zero
```

で明示的に取り出している。

### `nlinarith`

本 theorem の数学的内容は因子の符号判定だが、式

```lean
p.base.snd ^ 2 =
  5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd
```

には積が含まれるため、線形算術の `linarith` ではなく nonlinear arithmetic tactic の `nlinarith` が使われている。

ここで `nlinarith` は quartic polynomial を展開する必要はない。`goldenFifthSndFactor gamma.fst gamma.snd` は一つの整数式として扱われ、その正値性 `hH` と積恒等式 `hEq`、平方の正値性 `hsSq` だけから結論を導く。

### packet API の再利用

`s≠0` の由来や quartic factor の非負性を本 theorem 内で再証明していない。`snd_ne_zero` と 0389 を経由して、既に構築された packet invariant と positivity API をそのまま利用している。

## 冗長・重複箇所

本 theorem は 4 行の証明で、冗長性は非常に少ない。

`hEq` と `hH` は直前二 theorem から取得する API 呼び出しであり、意図的な段階分離である。0388・0389・0390 を一つの長い theorem に統合すれば行数は減るが、

- 第二座標積恒等式
- quartic factor の正値性
- fifth root 第二座標の正値性

を個別に再利用できなくなるため、現在の分割には明確な設計上の価値がある。

一方、`hsSq` は 0389 でも同じ形で構築されている。これが後続にも頻出するなら

```lean
p.snd_sq_pos
```

のような packet helper を追加する余地はある。ただし現時点でそれが十分な重複量かは確認できない。

## 最適化候補

### 1. 符号推論の構造化

`nlinarith` は短く強力だが、数学的構造をより明示するなら、正積

$$
0 < 5H(a,b)
$$

を作り、積 $b(5H)$ の正値性から `b>0` を取り出す証明も考えられる。

例えば `mul_pos_iff` や `mul_pos` 系補題を使うことで nonlinear tactic への依存を減らせる可能性がある。ただし正確な最短 Lean コードは、この実行では Lean build を行わないため未確認である。

### 2. 0388–0390 の positivity packet 化

後続で二つの positivity fact を同時に必要とする箇所が多いなら、

```lean
0 < gamma.snd ∧
0 < goldenFifthSndFactor gamma.fst gamma.snd
```

を返す補助定理を追加できる。ただし既存の単目的 lemma の方が依存関係を細かく保てるため、置換ではなく補助 API とする方が自然である。

### 3. `natAbs` bridge の追加

後続で `gamma.snd.natAbs` を自然数 measure として頻繁に使うなら、本 theorem から

```lean
(gamma.snd.natAbs : ℤ) = gamma.snd
```

あるいは対応する自然数・整数 cast lemma を導出する helper を用意すると、符号除去の rewrite を集約できる可能性がある。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は現在

```lean
import Mathlib
```

を使用している。

本 theorem 自体が直接必要とする Mathlib 側の機能は、整数の順序、平方の正値性 `sq_pos_of_ne_zero`、および nonlinear arithmetic tactic `nlinarith` である。

したがって import を縮小する場合、代数・順序の基礎 module と `Mathlib.Tactic` / `Mathlib.Tactic.Nlinarith` 周辺が候補となる。ただし `GoldenInt`、`GoldenZeroSectorDescentPacket`、および直前 theorem 群が transitively 要求する Mathlib module まで含めた厳密な最小 import は、Lean build を行わない条件のため確認していない。

したがって **現在確認できる必要 import は `Mathlib`、最小 import は未確定** とする。

## Comparator challenge 化の可否

**可。小規模な符号推論 challenge として非常に適している。**

FLT5 固有定義を除去すれば、核は次の形になる。

```lean
(hEq : s ^ 2 = 5 * b * H)
(hs0 : s ≠ 0)
(hH : 0 < H)
⊢ 0 < b
```

challenge の要点は

1. `s≠0` から `s^2>0` を作る
2. $5>0$ と `H>0` を認識する
3. 積恒等式から `b>0` を導く

ことである。

`nlinarith` を許可する版では tactic selection の比較になり、`nlinarith` を禁止して `mul_pos_iff` 等だけで解かせる版では符号構造の明示的 reasoning の比較になる。Comparator 用には両版を用意する価値がある。

## 次に読むべき宣言

次は **0391 `GoldenZeroSectorDescentPacket.fifthRoot_coprime_coords`** である。宣言種別は `theorem`。

Lean 正本では次の形で始まる。

```lean
theorem fifthRoot_coprime_coords
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5)
    (hnorm : goldenNorm gamma = (p.D : ℤ)) :
    Nat.Coprime gamma.fst.natAbs gamma.snd.natAbs := by
  by_contra hcop
  ...
```

0390 までで第五根 `gamma` の第二座標の符号が確定した。0391 ではさらに `goldenNorm gamma = D` を使い、`gamma` 自身の二座標

$$
\gamma=(a,b)
$$

について

$$
\gcd(|a|,|b|)=1
$$

を証明する段階へ進む。これは `gamma` を新しい primitive descent data として再利用するための核心条件である。
