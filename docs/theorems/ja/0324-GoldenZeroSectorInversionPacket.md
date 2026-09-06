# 0324 — `GoldenZeroSectorInversionPacket`

## 宣言種別

これは theorem ではなく **`structure`** である。

0314–0323 まで `GoldenZeroSectorCandidate` 上で個別に証明してきた符号条件、所有関係、積・差恒等式、平方再構成、自然数代表の正性などを、一つの certified packet として束ねる宣言である。

## Lean の型

```lean
/--
Certified output of zero-sector inversion.  It keeps the complete source candidate
and all signs, ownership, factor identities, and positivity facts needed downstream.
-/
structure GoldenZeroSectorInversionPacket where
  source : GoldenZeroSectorCandidate
  H_pos : 0 < goldenFifthSndFactor source.r source.s
  s_neg : source.s < 0
  c_pos : 0 < source.c
  d_pos : 0 < source.d
  s_eq : source.s = -((5 : ℤ) ^ 6 * (source.c : ℤ) ^ 10)
  H_eq : goldenFifthSndFactor source.r source.s = (source.d : ℤ) ^ 10
  a_eq : source.a = source.c * source.d
  coprime_c_d : Nat.Coprime source.c source.d
  five_not_dvd_d : ¬ 5 ∣ source.d
  d_odd : Odd source.d
  discriminant_eq :
    zeroSectorU source.r source.s ^ 2 - zeroSectorW source.d ^ 2 =
      20 * source.s ^ 4
  factor_product :
    source.A0 * source.B0 = 4 * zeroSectorQ source.c ^ 5
  factor_difference :
    source.B0 = source.A0 + 8 * source.d ^ 5
  factor_sum :
    zeroSectorA source.r source.s source.d +
        zeroSectorB source.r source.s source.d =
      2 * zeroSectorU source.r source.s
  square_reconstruction :
    zeroSectorU source.r source.s - 5 * source.s ^ 2 =
      zeroSectorX source.r source.s ^ 2
  W_pos : 0 < zeroSectorW source.d
  A_pos : 0 < zeroSectorA source.r source.s source.d
  A_lt_B :
    zeroSectorA source.r source.s source.d <
      zeroSectorB source.r source.s source.d
  B_pos : 0 < zeroSectorB source.r source.s source.d
  A0_cast : (source.A0 : ℤ) = zeroSectorA source.r source.s source.d
  B0_cast : (source.B0 : ℤ) = zeroSectorB source.r source.s source.d
  A0_pos : 0 < source.A0
  B0_pos : 0 < source.B0
```

型としては `GoldenZeroSectorInversionPacket : Type` であり、1つの `GoldenZeroSectorCandidate` と、その candidate について既に確立済みの証明項を保持する dependent record である。

## 数学的意味

`source` を零セクター反転から得られた候補とする。本 structure はその候補に対し、下流で必要となる情報をまとめて保存する。

主要な内容は次の通りである。

- $H>0$, $s<0$, $c>0$, $d>0$ という符号条件
- $s=-5^6c^{10}$, $H=d^{10}$, $a=cd$ という所有・再パラメータ化
- $\gcd(c,d)=1$, $5\nmid d$, $d$ が奇数という算術条件
- discriminant identity

$$
U^2-W^2=20s^4
$$

- 正の自然数因子 $A_0,B_0$ に対する

$$
A_0B_0=4Q^5
$$

および

$$
B_0=A_0+8d^5
$$

- signed factors についての和、平方再構成、正性、順序
- `A0`, `B0` と signed factors の cast 同一視

つまり本 structure は「零セクター反転が成功した」ことを単一の命題で言うのではなく、その成功結果を後続の factorization が直接消費できる API として保存する。

## 証明全体での役割

ここが `GoldenZeroSectorCandidate` phase と factorization phase の境界である。

0314–0323 では candidate 上の個別 theorem として

$$
0<A<B,
$$

$$
A_0B_0=4Q^5,
$$

$$
B_0=A_0+8d^5
$$

などを整備した。本 structure はそれらを field として固定し、以後の証明で同じ chain を再実行しないようにする。

直後の `goldenZeroSectorInversionPacket` が任意の `GoldenZeroSectorCandidate` からこの structure を構築し、その後の `SignedGoldenZeroSectorFactorization` では `GoldenZeroSectorInversionPacket` を入力として、共通奇素因子排除、二進 branch 分類、fifth-power splitting へ進む。

したがって本宣言は数学的な新恒等式を追加するものではなく、**証明済み不変量を module 境界でパッケージ化する設計上の重要点** である。

## 直接依存する定義・補題

本 structure 自体には proof script はないが、各 field の型が上流 API を固定する。

### `GoldenZeroSectorCandidate`

`source` field の型であり、本 packet の全ての field が `source.r`, `source.s`, `source.c`, `source.d`, `source.A0`, `source.B0` などに依存する。

### 上流の主要 theorem 群

直後の constructor `goldenZeroSectorInversionPacket` では、field が次の theorem から埋められる。

- `p.H_pos`
- `p.s_neg`
- `p.c_pos`
- `p.d_pos`
- `p.s_eq_neg_five_pow_mul_tenth`
- `p.H_eq_tenth`
- `p.a_eq_c_mul_d`
- `p.coprime_c_d`
- `p.five_not_dvd_d`
- `p.d_odd`
- `p.discriminant_eq`
- `p.A0_mul_B0`
- `p.B0_eq_A0_add`
- `p.factor_sum`
- `p.square_reconstruction`
- `p.W_pos`
- `p.A_pos`
- `p.A_lt_B`
- `p.B_pos`
- `p.A0_cast`
- `p.B0_cast`
- `p.A0_pos`
- `p.B0_pos`

この対応から、本 structure が上流の theorem museum の集約点であることが分かる。

## 構築の流れ

structure 宣言自身は「証明」ではなく record schema の定義なので tactic proof は存在しない。

論理的な構築順は次の通りである。

1. `source : GoldenZeroSectorCandidate` を保持する。
2. source の符号情報を保持する。
3. $s,H,a$ の再パラメータ化を保持する。
4. $c,d$ の互いに素性、5 非可除性、奇性を保持する。
5. discriminant・積・差・和・平方再構成を保持する。
6. signed factors の正性と順序を保持する。
7. `A0`,`B0` の cast equation と自然数正性を保持する。

これにより downstream は `p.factor_product`, `p.factor_difference`, `p.coprime_c_d` のように field projection だけで必要事実を取得できる。

## Lean 固有の処理

### dependent field

各 field の型が前の `source` field に依存する。たとえば

```lean
factor_product :
  source.A0 * source.B0 = 4 * zeroSectorQ source.c ^ 5
```

は packet 内の同じ `source` に結び付いている。そのため別 candidate の証明を誤って混ぜることが型によって防がれる。

### proof as data

Lean では theorem の証明項も通常の field として structure に格納できる。本宣言では符号条件や等式が単なるコメントではなく、後続 theorem が利用可能な値として保持される。

### namespace 境界の API 固定

直後に `end DkMath.FLT.Five` があり、次の generated source `SignedGoldenZeroSectorFactorization.lean` が packet を入力として始まる。したがってこの structure は実装上もファイル間インターフェースとして働いている。

## 冗長・重複箇所

structure は上流 theorem を多数 field として再掲しているため、見た目には重複が多い。しかしこれは意図的な API materialization である。

特に `A_pos`, `B_pos`, `A_lt_B`, `A0_pos`, `B0_pos` は相互に一部導出可能に見えるが、下流が再証明なしに直接参照できる利点がある。

一方、packet が肥大化すると上流 theorem を追加するたび constructor 更新が必要になるため、保守コストは増える。この trade-off は明確である。

## 最適化候補

候補は3つある。

1. field を意味領域ごとの小 structure に分け、packet がそれらを合成する。
2. 容易に再導出できる field を削り、最小 invariant set のみ保持する。
3. 現行のように downstream 利便性を優先し、冗長でも完成済み API を保持する。

現状は 3 の設計であり、factorization module が多くの field projection を直接使うため合理的である。

たとえば `A_pos` と `A0_cast` から `A0_pos` は再構築可能だが、毎回同じ bridge proof を繰り返すより packet に保存する方が downstream proof は短くなる。

どこまで縮約可能かは downstream 全体を Lean build で確認しなければ断定できないため、上記は **未検証の設計候補** である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用する。

本 structure 宣言自体が直接必要とする機能は比較的基本的で、主に

- `structure`
- `Nat`, `Int`
- `Nat.Coprime`
- `Odd`
- divisibility `∣`
- order relation `<`
- power `^`

である。

ただし field 型に project 内の多数の既存定義・theorem が現れ、その依存閉包は大きい。正確な最小 Mathlib import 集合は本実行では Lean build を行っていないため **未確認** である。

## Comparator challenge 化の可否

**単体の theorem proof challenge としては不向きだが、API 設計 Comparator としては非常に良い。**

比較対象としては

1. 現行の flat structure
2. signs / arithmetic / factor identities / cast facts に分割した nested structure
3. 最小 invariant set のみを保存する lean packet
4. theorem を field にせず source から typeclass/namespace theorem として都度導出する設計

が考えられる。

評価軸は

- downstream proof の短さ
- field 重複量
- constructor 保守コスト
- source candidate との依存関係の明瞭さ
- module boundary としての安定性

である。

## PDF との照合

対象 branch には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

ただし GitHub コネクタは binary PDF 本文を text として返さず、本実行では raw PDF の取得も成功しなかった。そのため具体的ページ・節・式番号との直接照合は **未確認** であり、推測していない。

本解説の技術的内容は、対象 branch の最新 `Flt5DkMath/FLT5StandAlone.lean` にある structure 宣言と、その直後の constructor および下流 factorization code を正本としている。

## 次に読むべき宣言

次は **0325 `goldenZeroSectorInversionPacket`** である。

種別は theorem ではなく **`def`** である。

```lean
def goldenZeroSectorInversionPacket (p : GoldenZeroSectorCandidate) :
    GoldenZeroSectorInversionPacket where
  source := p
  H_pos := p.H_pos
  s_neg := p.s_neg
  ...
  A0_pos := p.A0_pos
  B0_pos := p.B0_pos
```

0324 が packet の schema を定義したのに対し、0325 は任意の `GoldenZeroSectorCandidate` からその packet を決定的に構築し、上流 theorem 群を各 field に実際に充填する宣言である。