# 0393 `GoldenZeroSectorDescentPacket.fifthRoot_measure_lt`

## 宣言種別

`theorem`

`GoldenZeroSectorDescentPacket` namespace 内で、0387 以降に構成した第五根 `gamma : GoldenInt` の第二座標の絶対値が、元の descent packet の第二座標の絶対値より真に小さいことを示す strict-descent 補題である。

## Lean コード

```lean
theorem fifthRoot_measure_lt
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5) :
    gamma.snd.natAbs < p.base.snd.natAbs := by
  have hn : 0 < gamma.snd := p.fifthRoot_snd_pos gamma hroot
  have hH : 0 < goldenFifthSndFactor gamma.fst gamma.snd :=
    p.fifthRoot_H_pos gamma hroot
  have hEq := p.fifthRoot_snd_factor_eq gamma hroot
  have hdiag := sixteen_mul_goldenFifthSndFactor_eq gamma.fst gamma.snd
  have hbound :
      5 * gamma.snd ^ 4 ≤
        16 * goldenFifthSndFactor gamma.fst gamma.snd := by
    calc
      5 * gamma.snd ^ 4 ≤
          zeroSectorX gamma.fst gamma.snd ^ 4 +
            10 * zeroSectorX gamma.fst gamma.snd ^ 2 * gamma.snd ^ 2 +
            5 * gamma.snd ^ 4 := by
        have hx : 0 ≤ zeroSectorX gamma.fst gamma.snd ^ 4 := by positivity
        have hcross : 0 ≤
            10 * zeroSectorX gamma.fst gamma.snd ^ 2 * gamma.snd ^ 2 := by
          positivity
        linarith
      _ = 16 * goldenFifthSndFactor gamma.fst gamma.snd := hdiag.symm
  have hn4 : gamma.snd ≤ gamma.snd ^ 4 := by
    have hn0 : 0 ≤ gamma.snd := hn.le
    have hn1 : 0 ≤ gamma.snd - 1 := by omega
    have hquad : 0 ≤ gamma.snd ^ 2 + gamma.snd + 1 := by positivity
    have hnonneg : 0 ≤
        gamma.snd * (gamma.snd - 1) *
          (gamma.snd ^ 2 + gamma.snd + 1) :=
      mul_nonneg (mul_nonneg hn0 hn1) hquad
    nlinarith
  have hn_lt_fiveH :
      gamma.snd < 5 * goldenFifthSndFactor gamma.fst gamma.snd := by
    nlinarith
  apply Int.natAbs_lt_iff_sq_lt.mpr
  nlinarith
```

## Lean の型

概念的には次の型である。

```lean
GoldenZeroSectorDescentPacket.fifthRoot_measure_lt :
  (p : GoldenZeroSectorDescentPacket) →
  (gamma : GoldenInt) →
  goldenZeroSectorLift p.base = goldenPow gamma 5 →
  gamma.snd.natAbs < p.base.snd.natAbs
```

入力は descent packet `p`、黄金整数 `gamma`、および quadratic lift が `gamma` の第五冪であるという

```lean
hroot : goldenZeroSectorLift p.base = goldenPow gamma 5
```

である。出力は自然数上の strict inequality

$$
|\gamma_{\mathrm{snd}}| < |p.base.snd|.
$$

以下、

$$
a=\gamma_{\mathrm{fst}},\qquad
b=\gamma_{\mathrm{snd}},\qquad
s=p.base.snd,
$$

$$
H(a,b)=\operatorname{goldenFifthSndFactor}(a,b)
$$

と書く。

## 数学的主張

0388 `fifthRoot_snd_factor_eq` から

$$
s^2=5bH(a,b)
$$

を持つ。また 0389 と 0390 により

$$
H(a,b)>0,
\qquad
b>0.
$$

ここで既存の対角化恒等式

$$
16H(a,b)
=
X(a,b)^4+10X(a,b)^2b^2+5b^4
$$

を使う。ただし `X(a,b)` は `zeroSectorX a b` である。

右辺の最初の二項は非負なので

$$
5b^4\le16H(a,b).
$$

さらに $b$ は正の整数であるから

$$
b\le b^4.
$$

これらと $H(a,b)>0$ を合わせると

$$
b<5H(a,b).
$$

したがって $b>0$ を掛けて

$$
b^2<5bH(a,b)=s^2.
$$

整数では

$$
b^2<s^2
\quad\Longleftrightarrow\quad
|b|<|s|,
$$

なので、最終的に

$$
|b|<|s|
$$

を得る。

## 証明全体での役割

この theorem は zero-sector descent の **well-foundedness を与える中心不等式** である。

0387 では

$$
T(r,s)=\gamma^5
$$

という第五根を取り出し、0388–0392 ではその `gamma=(a,b)` に対して

$$
s^2=5bH(a,b),
$$

$$
H(a,b)>0,
$$

$$
b>0,
$$

$$
\gcd(|a|,|b|)=1,
$$

$$
5\nmid H(a,b)
$$

という次世代 packet に必要な invariant を順に回収した。

しかし invariant を保存するだけでは無限降下にはならない。再構成した次 packet が元 packet より **必ず小さい** ことを示す必要がある。

0393 はその減少量を

```lean
gamma.snd.natAbs
```

で測り、

```lean
gamma.snd.natAbs < p.base.snd.natAbs
```

を与える。したがって第五根を次 packet の base に再利用したとき、自然数値 measure が真に減少する。

これは後続の recursive packet construction と strong/well-founded descent を正当化する決定的な theorem である。

## 直接依存する定義・補題

主要な直接依存は次の通りである。

- `GoldenZeroSectorDescentPacket`
- `GoldenInt`
- `goldenZeroSectorLift`
- `goldenPow`
- `goldenFifthSndFactor`
- `zeroSectorX`
- `GoldenZeroSectorDescentPacket.fifthRoot_snd_pos`
- `GoldenZeroSectorDescentPacket.fifthRoot_H_pos`
- `GoldenZeroSectorDescentPacket.fifthRoot_snd_factor_eq`
- `sixteen_mul_goldenFifthSndFactor_eq`
- `Int.natAbs_lt_iff_sq_lt`
- `mul_nonneg`
- `positivity`
- `linarith`
- `nlinarith`
- `omega`

特に代数的な主エンジンは

```lean
theorem sixteen_mul_goldenFifthSndFactor_eq (r s : ℤ) :
    16 * goldenFifthSndFactor r s =
      zeroSectorX r s ^ 4 +
        10 * zeroSectorX r s ^ 2 * s ^ 2 +
        5 * s ^ 4 := by
  ...
```

である。この恒等式が quartic factor に明示的な正の下界を与える。

## 証明・構築の流れ

1. 0390 から

   ```lean
   hn : 0 < gamma.snd
   ```

   を取得する。

2. 0389 から

   ```lean
   hH : 0 < goldenFifthSndFactor gamma.fst gamma.snd
   ```

   を取得する。

3. 0388 の積恒等式

   ```lean
   hEq : p.base.snd ^ 2 =
     5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd
   ```

   を取得する。

4. `sixteen_mul_goldenFifthSndFactor_eq` の対角化恒等式を取得する。

5. `positivity` で

   $$
   X^4\ge0,
   \qquad
   10X^2b^2\ge0
   $$

   を証明し、`linarith` により

   $$
   5b^4\le16H
   $$

   を得る。

6. $b>0$ から $b\ge1$ を `omega` で取り、

   $$
   b(b-1)(b^2+b+1)\ge0
   $$

   を構成する。この積は

   $$
   b^4-b
   $$

   に等しいため、`nlinarith` で

   $$
   b\le b^4
   $$

   を得る。

7. $5b^4\le16H$、$b\le b^4$、$H>0$ から `nlinarith` で

   $$
   b<5H
   $$

   を得る。

8. 最終目標

   ```lean
   gamma.snd.natAbs < p.base.snd.natAbs
   ```

   を

   ```lean
   Int.natAbs_lt_iff_sq_lt.mpr
   ```

   で平方比較へ変換する。

9. $b>0$、$b<5H$、および $s^2=5bH$ から `nlinarith` で

   $$
   b^2<s^2
   $$

   を示して終了する。

## Lean 固有の処理

### `positivity` による非負性の自動処理

対角化恒等式から下界を取り出す際、

```lean
have hx : 0 ≤ zeroSectorX ... ^ 4 := by positivity
have hcross : 0 ≤ 10 * zeroSectorX ... ^ 2 * gamma.snd ^ 2 := by
  positivity
```

としている。

数学的には偶数冪なので自明だが、Lean ではこの非負性を tactic で明示し、その後 `linarith` に渡している。

### `b ≤ b^4` を因数分解で作る

整数上で $b>0$ なら $b\ge1$ である。しかし `nlinarith` に $b>0$ だけを渡しても、整数離散性から $b\ge1$ を自動で利用するとは限らない。そのため

```lean
have hn1 : 0 ≤ gamma.snd - 1 := by omega
```

で整数性を使っている。

さらに

```lean
gamma.snd * (gamma.snd - 1) *
  (gamma.snd ^ 2 + gamma.snd + 1)
```

の非負性を作ることで、恒等式

$$
b(b-1)(b^2+b+1)=b^4-b
$$

を `nlinarith` に認識させている。

### `linarith` と `nlinarith` の役割分担

`hbound` の最初の比較は、各非負項を既に仮定として与えているため線形結合だけで済み `linarith` が使われる。

一方、`hn4` や最終比較では冪・積を含むので `nlinarith` が使われる。

### `Int.natAbs_lt_iff_sq_lt`

最終目標は `Nat` 上の絶対値比較だが、主要な代数恒等式は `ℤ` 上にある。そこで

```lean
apply Int.natAbs_lt_iff_sq_lt.mpr
```

により

```lean
gamma.snd.natAbs < p.base.snd.natAbs
```

を整数平方の比較へ戻している。

これにより途中で `natAbs` の cast を大量に扱わず、最後まで整数環のまま計算できる。

## 冗長・重複箇所

証明は strict descent の核心なので、単純な API wrapper より長い。ただしいくつか局所 helper 化できる部分がある。

### 1. 正整数の `x ≤ x^4`

```lean
have hn4 : gamma.snd ≤ gamma.snd ^ 4 := by
  ...
```

は FLT5 固有ではない一般的な整数不等式である。同種の冪比較が他にも現れるなら、一般補題へ切り出せる。

### 2. 対角化恒等式からの quartic lower bound

```lean
5 * b ^ 4 ≤ 16 * H(a,b)
```

も `sixteen_mul_goldenFifthSndFactor_eq` の直接 corollary である。zero-sector 系で複数回必要なら

```lean
theorem five_mul_s_pow_four_le_sixteen_mul_goldenFifthSndFactor ...
```

のような専用 API にできる。

### 3. positivity fact の局所展開

`hx` と `hcross` は読みやすいが、`positivity` を直接 calc branch で使う形に圧縮できる。ただし現在の形は証明意図が明瞭なので、短縮が必ずしも改善とは限らない。

## 最適化候補

### 1. lower-bound helper の追加

対角化恒等式から

$$
5s^4\le16H(r,s)
$$

を抽出する一般補題を先に置けば、本 theorem の最も長い `hbound` block を隠蔽できる。

これは algebraic identity と descent argument の責務分離として自然である。

### 2. positive integer power monotonicity の利用

Mathlib に直接適合する既存補題が確認できるなら、手書きの

```lean
b * (b - 1) * (b^2 + b + 1) ≥ 0
```

を置き換えられる可能性がある。

ただし本作業では Lean build や API 探索による最小化検証を行っていないため、具体的な置換補題名は未確認である。

### 3. measure lemma の抽象化

証明の数学的入力は実質的に

$$
s^2=5bH,
\qquad
b>0,
\qquad
H>0,
\qquad
5b^4\le16H
$$

だけである。

したがって黄金整数固有の名前を含まない一般的不等式補題へ切り出し、0393 をその適用だけにする設計も可能である。Comparator や再利用性の観点では特に有効である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は現在

```lean
import Mathlib
```

を使用している。

0393 が直接利用する Mathlib 機能は主に以下である。

- 整数順序と冪
- `Int.natAbs_lt_iff_sq_lt`
- `mul_nonneg`
- `positivity`
- `linarith`
- `nlinarith`
- `omega`

`GoldenZeroSectorDescentPacket`、`goldenFifthSndFactor`、`zeroSectorX`、対角化恒等式、および 0388–0390 はプロジェクト内部の先行宣言である。

理論上は `Mathlib` 全体を import せず、整数・order・power と tactic 群に必要なモジュールまで縮小できる可能性が高い。

ただし本作業では Lean build を実行していないため、**厳密な最小 import 集合は未確認** である。

## Comparator challenge 化の可否

**非常に適している。**

0393 は短い API wrapper ではなく、複数の先行 invariant と quartic diagonalization を組み合わせて well-founded decrease を作る substantive な proof challenge である。

challenge では例えば次を与える。

```lean
hroot
p.fifthRoot_snd_factor_eq gamma hroot
p.fifthRoot_H_pos gamma hroot
p.fifthRoot_snd_pos gamma hroot
sixteen_mul_goldenFifthSndFactor_eq gamma.fst gamma.snd
```

そして目標

```lean
gamma.snd.natAbs < p.base.snd.natAbs
```

を再構成させる。

評価点は次の通りである。

1. 対角化恒等式から $5b^4\le16H$ を抽出できるか。
2. 整数の正値性から $b\le b^4$ を安全に処理できるか。
3. $b<5H$ を経由して $b^2<s^2$ を作れるか。
4. `Int.natAbs_lt_iff_sq_lt` で absolute-value measure へ正しく戻せるか。
5. `linarith`、`nlinarith`、`omega`、`positivity` の役割を混同せずに使えるか。

特に「保存される algebraic invariant」と「真に減少する well-founded measure」を接続するため、FLT5 descent の理解を測る challenge として質が高い。

## 次に読むべき宣言

次は **0394 `GoldenZeroSectorDescentPacket.fifthRoot_power_split`** を読むべきである。宣言種別は `theorem`。

正本では 0393 の直後に置かれ、冒頭は次の形である。

```lean
theorem fifthRoot_power_split
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5)
    (hnorm : goldenNorm gamma = (p.D : ℤ)) :
    ∃ u v : ℕ,
      0 < u ∧ 0 < v ∧
      ...
```

0393 が **measure の strict decrease** を確立したのに対し、0394 は第五根側の積

$$
b\,H(a,b)
$$

を coprimality と 5-adic 条件のもとで再び冪へ分離し、次世代 descent packet の recursive shape を復元する段階である。

したがって 0393 は「小さくなること」、0394 は「同じ形へ戻ること」を担当し、この二つが揃って strict infinite descent の再帰ステップになる。
