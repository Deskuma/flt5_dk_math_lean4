# 0388 `GoldenZeroSectorDescentPacket.fifthRoot_snd_factor_eq`

## 宣言種別

`theorem`

`GoldenZeroSectorDescentPacket` namespace 内に置かれた、0387 で得た純粋な第五冪 re-entry を第二座標へ射影し、次の descent に必要な積分解へ変換する定理である。

## Lean コード

```lean
theorem fifthRoot_snd_factor_eq
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5) :
    p.base.snd ^ 2 =
      5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd := by
  have h := congrArg (fun x : GoldenInt => x.snd) hroot
  change (goldenZeroSectorLift p.base).snd =
    (goldenPow gamma 5).snd at h
  rw [goldenZeroSectorLift_snd, goldenPow_five_snd,
    goldenFifthSndPoly_eq] at h
  exact h
```

## Lean の型

概念的には次の型である。

```lean
GoldenZeroSectorDescentPacket.fifthRoot_snd_factor_eq :
  (p : GoldenZeroSectorDescentPacket) →
  (gamma : GoldenInt) →
  goldenZeroSectorLift p.base = goldenPow gamma 5 →
  p.base.snd ^ 2 =
    5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd
```

入力は descent packet `p`、黄金整数 `gamma`、そして quadratic lift が `gamma` の第五冪に等しいという証明 `hroot` である。出力は整数環 `ℤ` 上の積恒等式である。

## 数学的主張

`p.base=(r,s)`、`gamma=(a,b)` と書く。

quadratic lift は第二座標について

$$
\operatorname{goldenZeroSectorLift}(r,s)_{\mathrm{snd}}=s^2
$$

を満たす。

一方、黄金整数の第五冪の第二座標は

$$
(\gamma^5)_{\mathrm{snd}}
 = \operatorname{goldenFifthSndPoly}(a,b)
 = 5b\,H(a,b)
$$

であり、ここで

$$
H(a,b)
 = a^4+2a^3b+4a^2b^2+3ab^3+b^4
$$

である。

したがって仮定

$$
\operatorname{goldenZeroSectorLift}(r,s)=\gamma^5
$$

の第二座標を比較するだけで

$$
s^2=5bH(a,b)
$$

を得る。

Lean の結論はこれをそのまま

```lean
p.base.snd ^ 2 =
  5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd
```

と表している。

## 証明全体での役割

0387 `exists_lift_eq_fifthPower` では unit-sector ambiguity を除去して

$$
\operatorname{goldenZeroSectorLift}(p.base)=\gamma^5
$$

という pure fifth-power representation を得た。しかし、その等式はまだ `GoldenInt` 全体の等式であり、そのままでは descent measure を比較するための整数因子分解として使いにくい。

0388 はこの等式から第二座標だけを抽出し、

$$
s^2=5bH(a,b)
$$

という整数積分解へ落とす。

この変換により後続では、

- `H(a,b)` の正値性
- `b` と `H(a,b)` の互いに素性
- `5bH(a,b)` が平方であることを用いた冪分離
- 新しい fifth-power parameter の構成
- 元の measure より小さい packet の構成

へ進める。

したがって本定理は、黄金整数環で得た第五冪構造を、整数算術による strict descent に再接続する **座標射影の橋** である。

## 直接依存する定義・補題

直接使われている主な宣言は次の通りである。

- `GoldenZeroSectorDescentPacket`
- `GoldenInt`
- `goldenZeroSectorLift`
- `goldenPow`
- `goldenZeroSectorLift_snd`
- `goldenPow_five_snd`
- `goldenFifthSndPoly_eq`
- `goldenFifthSndFactor`

特に Lean 正本では次の恒等式が既に証明されている。

```lean
theorem goldenZeroSectorLift_snd (x : GoldenInt) :
    (goldenZeroSectorLift x).snd = x.snd ^ 2 := rfl
```

```lean
theorem goldenPow_five_snd (gamma : GoldenInt) :
    (goldenPow gamma 5).snd =
      goldenFifthSndPoly gamma.fst gamma.snd := by
  ...
```

```lean
theorem goldenFifthSndPoly_eq (r s : ℤ) :
    goldenFifthSndPoly r s =
      5 * s * goldenFifthSndFactor r s := by
  ...
```

そのため 0388 自体には新しい多項式展開はない。

## 証明・構築の流れ

1. `hroot` の両辺へ第二座標射影を適用する。

   ```lean
   have h := congrArg (fun x : GoldenInt => x.snd) hroot
   ```

   これにより概念的に

   $$
   T(r,s)_{\mathrm{snd}}=(\gamma^5)_{\mathrm{snd}}
   $$

   を得る。

2. `change` で射影後の等式を、後続の rewrite が認識しやすい表現へ固定する。

   ```lean
   change (goldenZeroSectorLift p.base).snd =
     (goldenPow gamma 5).snd at h
   ```

3. 三つの既存恒等式で両辺を順に書き換える。

   ```lean
   rw [goldenZeroSectorLift_snd, goldenPow_five_snd,
     goldenFifthSndPoly_eq] at h
   ```

   左辺は `p.base.snd ^ 2`、右辺は

   ```lean
   5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd
   ```

   になる。

4. 書き換え済みの `h` が目標と完全一致するので、そのまま返す。

   ```lean
   exact h
   ```

## Lean 固有の処理

### `congrArg` による座標射影

`hroot` は `GoldenInt` の等式である。必要なのは第二座標だけなので、

```lean
congrArg (fun x : GoldenInt => x.snd) hroot
```

によって等式保存性を使って射影している。

これは構造体等式から必要な観測量だけを取り出す Lean で典型的な方法である。

### `change` による definitional presentation の調整

`congrArg` 直後の型は Lean の elaboration により projection が別の見え方をする可能性がある。ここでは

```lean
change (goldenZeroSectorLift p.base).snd =
  (goldenPow gamma 5).snd at h
```

と明示し、その後の rewrite chain を安定させている。

数学的内容を追加する処理ではなく、表現をそろえるための Lean 固有の工程である。

### 既証明 polynomial identity の再利用

第五冪の第二座標をその場で `ring` 展開せず、`goldenPow_five_snd` と `goldenFifthSndPoly_eq` を経由している。これは証明重複を避け、座標公式の正本を一箇所へ集約する設計になっている。

## 冗長・重複箇所

本 theorem 自体は非常に短く、数学的な重複はほぼない。

ただし `congrArg` の直後の `change` は、projection の definitional reduction や simp lemma の整備状況によっては不要にできる可能性がある。

例えば環境によっては、

```lean
have h := congrArg GoldenInt.snd hroot
simpa [goldenZeroSectorLift_snd, goldenPow_five_snd,
  goldenFifthSndPoly_eq] using h
```

に近い形へ圧縮できる可能性がある。ただし `GoldenInt.snd` の projection 名や simp-normal form に依存するので、Lean build を行っていない今回の作業では成立を確認していない。

## 最適化候補

### 1. 射影 helper の共通化

今後 `fst` / `snd` projection を第五冪等式から何度も取り出すなら、

```lean
theorem goldenEq_snd {x y : GoldenInt} (h : x = y) : x.snd = y.snd :=
  congrArg (fun z => z.snd) h
```

のような helper は書ける。ただし `congrArg` 一行より抽象化の方が重くなるため、現状では必須ではない。

### 2. `goldenPow_five_snd` の factorized 版

現在は

$$
(\gamma^5)_{\mathrm{snd}}
\to \operatorname{goldenFifthSndPoly}
\to 5bH(a,b)
$$

と二段階 rewrite している。

頻出するなら

```lean
theorem goldenPow_five_snd_factorized (gamma : GoldenInt) :
    (goldenPow gamma 5).snd =
      5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd := ...
```

を用意すると、この theorem をさらに読みやすくできる。

ただし `goldenFifthSndPoly` を中間 API として残す現在の設計にも、展開式と factorized form を分離できる利点がある。

## 必要 Mathlib import と import 最適化候補

リポジトリの standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用している。

0388 の証明本文で直接必要な Mathlib 機能は主として、

- equality congruence `congrArg`
- structure projection
- `rw`
- `change`

であり、重い number-theory tactic はこの theorem 自体では使っていない。

したがって単独 theorem だけを見れば `Mathlib` 全体は過剰である可能性が高い。しかし実際の source module は `GoldenInt`、黄金整数演算、第五冪座標公式、zero-sector lift など多数のローカル宣言へ依存する。正確な最小 import は import graph と build による検証が必要であり、今回は Lean build を行わない条件なので未確認である。

import 最適化を行う場合は、0388 単独ではなく `SignedGoldenZeroSectorDescent.lean` の module 単位で調べるのが妥当である。

## Comparator challenge 化の可否

**可能。** ただし challenge としては小型である。

最小化した課題は次の形にできる。

```lean
-- given
hroot : goldenZeroSectorLift base = goldenPow gamma 5

-- prove
base.snd ^ 2 =
  5 * gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd
```

必要な API を

- `goldenZeroSectorLift_snd`
- `goldenPow_five_snd`
- `goldenFifthSndPoly_eq`

だけに制限すれば、Comparator は

1. 構造体等式を座標へ射影できるか
2. `congrArg` / projection を適切に選べるか
3. rewrite chain を最短で構成できるか

を評価できる。

数学的発見力より Lean API selection と proof compression を測る challenge に向いている。

## 次に読むべき宣言

次は `GoldenZeroSectorDescentPacket.fifthRoot_H_pos` を読むべきである。

```lean
theorem fifthRoot_H_pos
    (p : GoldenZeroSectorDescentPacket) (gamma : GoldenInt)
    (hroot : goldenZeroSectorLift p.base = goldenPow gamma 5) :
    0 < goldenFifthSndFactor gamma.fst gamma.snd := by
  have hEq := p.fifthRoot_snd_factor_eq gamma hroot
  have hsSq : 0 < p.base.snd ^ 2 :=
    sq_pos_of_ne_zero p.snd_ne_zero
  ...
```

0388 で得た

$$
s^2=5bH(a,b)
$$

と、既に証明済みの `p.snd_ne_zero` から左辺が正であることを使い、後続は quartic factor

$$
H(a,b)>0
$$

を引き出す。

したがって 0388 が **積恒等式の抽出**、次の宣言が **その積からの正値性抽出** という依存順になっている。