# 0316 — `GoldenZeroSectorCandidate.A0`

## 宣言種別

これは **`def`** である。

0314 `GoldenZeroSectorCandidate.A_pos` と 0315 `GoldenZeroSectorCandidate.A_lt_B` までで、lower inversion factor

$$
A=U-W
$$

は整数上で

$$
0<A<B
$$

を満たすことが確立された。本定義は、この正の整数因子 $A$ を後続の自然数算術で扱うために、その自然数代表

$$
A_0=|A|\in\mathbb N
$$

として取り出す境界定義である。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- Natural representative of the positive lower factor. -/
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs
```

型は

```lean
GoldenZeroSectorCandidate → ℕ
```

である。

入力 candidate `p` に保持された `r : ℤ`, `s : ℤ`, `d : ℕ` を使って整数 factor

```lean
zeroSectorA p.r p.s p.d : ℤ
```

を作り、その `Int.natAbs` を返す。

## 数学的意味

`zeroSectorA` は

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d
```

であり、したがって

$$
A=U-W.
$$

本定義は

$$
A_0:=|A|.
$$

を Lean の `ℕ` 値として実装している。

ただし、ここで重要なのは、数学的には直前ですでに $A>0$ が証明されていることである。よって後続 theorem `A0_cast` によって

$$
(A_0:\mathbb Z)=A
$$

が復元される。本定義だけを見ると符号情報を `natAbs` が消しているように見えるが、実際の証明設計では `A_pos` がその符号情報を別 theorem として保持しており、自然数側への移送時に再結合される。

## 証明全体での役割

0309–0315 までの zero-sector inversion は主として `ℤ` 上で進んでいた。そこでは

$$
AB=4Q^5,
$$

$$
B-A=8d^5,
$$

$$
0<A<B
$$

という signed factor data が構築された。

一方、後続の exact factor splitting、coprimality、二進付値分岐、fifth-power ownership は主に `ℕ` 上で記述される。そのため signed integer factor を自然数へ移す必要がある。

`A0` はその最初の境界である。直後に対応する `B0` が定義され、その後

```lean
theorem A0_cast ...
theorem B0_cast ...
theorem A0_pos ...
theorem B0_pos ...
theorem A0_mul_B0 ...
theorem B0_eq_A0_add ...
```

が続く。

したがって本定義は、**整数上の inversion factorization を自然数上の factor arithmetic へ移送する bridge object** である。

## 直接依存する定義・補題

### `zeroSectorA`

本定義が直接呼び出す project 側定義である。

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d
```

`A0` はその整数値に対して `natAbs` を取る。

### `Int.natAbs`

Lean / Mathlib の整数から自然数への絶対値写像である。

$$
\operatorname{natAbs}:\mathbb Z\to\mathbb N.
$$

正負どちらの整数にも total に定義できるため、`A0` 自体の定義には `A_pos` の証明引数を必要としない。

### `GoldenZeroSectorCandidate.A_pos`

本 `def` の式展開には直接使われないが、後続の `A0_cast` で不可欠な semantic dependency である。

```lean
theorem A0_cast (p : GoldenZeroSectorCandidate) :
    (p.A0 : ℤ) = zeroSectorA p.r p.s p.d := by
  exact Int.ofNat_natAbs_of_nonneg p.A_pos.le
```

この theorem により、`natAbs` で得た自然数代表が元の正の整数 factor と正確に一致することが保証される。

## 構築の流れ

1. candidate `p` から `r`, `s`, `d` を読む。
2. `zeroSectorA p.r p.s p.d : ℤ` を評価し、lower inversion factor $A$ を得る。
3. `Int.natAbs` を適用して自然数 $A_0$ を得る。
4. 本定義そのものはここで終了する。
5. 後続の `A0_cast` が `A_pos` を用いて $(A_0:ℤ)=A$ を証明する。
6. `A0_pos`、`A0_mul_B0`、factorization packet が自然数算術を引き継ぐ。

## Lean 固有の処理

### 証明依存型にせず total function として定義する

`A>0` が既に分かっているため、例えば positivity proof を引数に取る subtype 的な設計も可能ではある。しかし現行実装は

```lean
Int.natAbs
```

を使うことで、任意の整数に対して total な `ℕ` 値を返す単純な `def` としている。

これにより定義は proof-irrelevant な算術データだけを返し、正当性は後続 theorem `A0_cast` に分離される。

### `ℤ` / `ℕ` 境界の明示

FLT5 の signed algebraic identity は `ℤ` で扱いやすい一方、因数分解や `Nat.Coprime`、奇偶性、冪の分配は `ℕ` 側で扱う部分が多い。本 `def` はその型境界を明示している。

### dot notation

後続では

```lean
p.A0
```

と書ける。namespace 内で candidate を第1引数に取る `def` として定義しているため、自然な object-style API が得られている。

## 冗長・重複箇所

定義自体は一行であり、実装上の冗長性はほぼない。

ただし概念的には、すでに `A_pos : 0 < A` があるため、`natAbs` は「符号を忘れる一般演算」を用いてから `A0_cast` で正性を使って元へ戻す二段構成になっている。

これは一見すると回り道だが、Lean では非常に実用的である。`Int.toNat` を使う設計も候補になり得るが、負値での挙動や cast lemma の使いやすさが変わるため、現行 `natAbs` は signed-to-natural bridge として意味が明確である。

## 最適化候補

本定義そのものにはほぼ最適化余地がない。

候補を挙げるなら、`A0` と次の `B0` が完全に対称なので、抽象的な helper

```lean
def positiveIntRepresentative (z : ℤ) : ℕ := z.natAbs
```

を導入して共有する案はある。しかし単なる `natAbs` の別名となるだけで、API 層を一つ増やすため利益は小さい。

また、`Nat` subtype や `PNat` 的な「正の自然数」型を返す設計にすれば `A0_pos` をデータに埋め込める可能性がある。しかし後続コード全体の型が複雑になり、既存の `Nat.Coprime`、冪、可除性 API との接続コストが増える。

したがって現行の

```lean
ℤ --natAbs--> ℕ
```

と positivity theorem を分離する設計は、簡潔さと後続 Mathlib API の利用しやすさの両面で合理的である。

これら代替案は本実行では Lean build を行わないため **未検証の設計候補** とする。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 `def` が直接必要とする Mathlib 側機能は非常に小さく、中心は

- `Int.natAbs`
- `ℤ`, `ℕ` の基本型

だけである。

一方、`zeroSectorA` は project 内定義であり、その upstream definitions まで含めた module 単位の最小 import は本 `def` 単独からは決められない。

したがって `import Mathlib` をより狭い import へ縮小できる可能性は高いが、正確な最小 import 集合は Lean build 禁止条件のため未確認である。

## Comparator challenge 化の可否

**可能。ただし theorem proving より API / representation design 比較向け。難度は初級。**

比較課題としては次が適している。

- `Int.natAbs` を使う現行設計。
- `Int.toNat` を使う設計。
- positivity proof を持つ subtype を返す設計。
- `A0` を raw data として定義し、正当性を `A0_cast` に分離する設計。
- signed arithmetic を最後まで `ℤ` に残し、自然数へ移さない設計。

特に「定義を total に保ち、意味上の正当性を theorem へ分離する」という Lean API 設計の比較教材として有用である。

## PDF との照合

対象 branch には既存の日英 PDF

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを repository 上で確認した。

ただし GitHub コネクタの通常 text fetch は binary PDF 本文を返さないため、本実行では具体的ページ・節・式番号との直接照合はできていない。その位置については推測しない。

本解説の Lean code、宣言順、直接依存、後続宣言との関係は最新 branch の `Flt5DkMath/FLT5StandAlone.lean` を正本として確認した。

## 次に読むべき宣言

次の宣言は 0317 `GoldenZeroSectorCandidate.B0`、種別は **`def`** である。

```lean
/-- Natural representative of the positive upper factor. -/
def B0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorB p.r p.s p.d).natAbs
```

0316 が lower factor $A$ を $A_0$ へ移したのに対応して、0317 は upper factor $B$ を

$$
B_0=|B|\in\mathbb N
$$

へ移す。二つが揃った後、0318 `A0_cast` から自然数 factor identity の再構築へ進む。