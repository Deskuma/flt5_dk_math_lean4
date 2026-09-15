# 0317 — `GoldenZeroSectorCandidate.B0`

## 宣言種別

これは **`def`** である。

0316 `GoldenZeroSectorCandidate.A0` が lower inversion factor $A$ の自然数代表を導入したのに対し、本定義は upper inversion factor $B$ の自然数代表を導入する。

直前までに

$$
0<A<B
$$

が整数上で確立されているため、特に $B>0$ である。本定義はこの正の整数 factor を

$$
B_0=|B|\in\mathbb N
$$

として自然数算術へ移す境界定義である。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- Natural representative of the positive upper factor. -/
def B0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorB p.r p.s p.d).natAbs
```

型は

```lean
GoldenZeroSectorCandidate → ℕ
```

である。

candidate `p` に保持された

```lean
p.r : ℤ
p.s : ℤ
p.d : ℕ
```

を用いて

```lean
zeroSectorB p.r p.s p.d : ℤ
```

を作り、その `Int.natAbs` を返す。

## 数学的意味

`zeroSectorB` は upstream で

```lean
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

と定義されている。したがって

$$
B=U+W.
$$

本定義はこの signed integer factor の自然数代表

$$
B_0:=|B|
$$

を実装する。

ただし証明の現在位置ではすでに `B_pos` により

$$
B>0
$$

が証明済みである。したがって後続の `B0_cast` では、単なる絶対値ではなく元の整数 factor そのものが復元される：

$$
(B_0:\mathbb Z)=B.
$$

このため `B0` は符号情報を捨てて意味を弱める定義ではなく、**符号情報を `B_pos` 側に保持したまま、算術 carrier だけを `ℤ` から `ℕ` へ移す定義** と見るのが正確である。

## 証明全体での役割

zero-sector inversion の signed phase では、すでに

$$
AB=4Q^5,
$$

$$
B-A=8d^5,
$$

$$
A+B=2U,
$$

$$
0<A<B
$$

という情報が `ℤ` 上で整備されている。

0316 `A0` と本 0317 `B0` は、その二つの正因子を自然数へ移す対になった bridge definitions である。

この後、`A0_cast` と `B0_cast` が

$$
(A_0:\mathbb Z)=A,
$$

$$
(B_0:\mathbb Z)=B
$$

を証明し、さらに positivity、積、差の等式が `ℕ` 側へ持ち上げ直される。その結果、後続の coprimality、二進付値、exact factor splitting、fifth-power ownership を Mathlib の `Nat` API で扱えるようになる。

したがって `B0` は単独で新しい数学的制約を導く定義ではないが、**signed inversion data を自然数 factorization machinery へ接続するための不可欠な型変換境界** である。

## 直接依存する定義・補題

### `zeroSectorB`

本定義が直接呼び出す project 側定義である。

```lean
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

従って `B0` の raw value は $|U+W|$ である。

### `Int.natAbs`

Lean / Mathlib が提供する整数から自然数への絶対値写像である。

$$
\operatorname{natAbs}:\mathbb Z\to\mathbb N.
$$

任意の整数に対する total function なので、本 `def` 自体には positivity proof を引数として渡す必要がない。

### `GoldenZeroSectorCandidate.B_pos`

本定義の body には現れないが、`B0` の意味を「正の整数 factor の自然数版」と解釈し、後続の `B0_cast` で元の整数値へ戻すための semantic dependency である。

既に

```lean
theorem B_pos (p : GoldenZeroSectorCandidate) :
    0 < zeroSectorB p.r p.s p.d := by
  unfold zeroSectorB
  linarith [p.U_nonneg, p.W_pos]
```

が確立されている。

### `GoldenZeroSectorCandidate.A0`

Lean の定義依存として `B0` が `A0` を呼ぶわけではないが、proof architecture 上では完全な対をなす直前の definition である。

```lean
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs
```

この二つが揃うことで signed pair $(A,B)$ が natural pair $(A_0,B_0)$ へ移される。

## 構築の流れ

1. candidate `p` から `r`, `s`, `d` を読む。
2. `zeroSectorB p.r p.s p.d : ℤ` により upper inversion factor $B$ を得る。
3. `Int.natAbs` を適用し、$B_0\in\mathbb N$ を定義する。
4. 本 `def` 自体は証明を要求せずここで終了する。
5. 後続 `B0_cast` が既存の `B_pos` を利用して $(B_0:ℤ)=B$ を回収する。
6. `A0` / `B0` の双方が整数 factor と一致することを得た後、積・差・順序などの signed identities を自然数側へ輸送する。

## Lean 固有の処理

### `natAbs` による total な carrier conversion

`B>0` が既に証明されているため、positive integer 専用 subtype を返す設計も可能である。しかし現行コードは `Int.natAbs` を使うことで

```lean
GoldenZeroSectorCandidate → ℕ
```

という単純な total function にしている。

これにより raw data と correctness proof が分離され、後続では通常の `Nat` API を直接利用できる。

### correctness を後続 theorem に分離

`B0` 自体には `B_pos` が現れない。これは正性を無視しているのではなく、

- data construction: `B0`
- semantic recovery: `B0_cast`

へ役割を分けているためである。

Lean ではこの分離により定義が簡潔になり、proof term を data に埋め込む必要がなくなる。

### `ℤ` / `ℕ` の境界

`zeroSectorB` は subtraction を含む inversion framework と共通の signed world に属するため `ℤ` が自然である。一方、後続の gcd、coprimality、divisibility、power decomposition は `ℕ` の Mathlib API と相性がよい。

`B0` はその型境界を明示する。

### dot notation

namespace `GoldenZeroSectorCandidate` の中で candidate を第1引数として定義しているため、後続では

```lean
p.B0
```

と書ける。

## 冗長・重複箇所

実装は一行であり、局所的な冗長性はない。

ただし `A0` と `B0` は構造的に完全に対称であり、

```lean
(z : ℤ).natAbs
```

を適用する点だけ見れば重複している。

しかしこの重複は lower / upper factor を API 上で明確に区別するための名前付けでもある。単一 helper に抽象化してもコード量はほとんど減らず、後続 theorem 名 `A0_cast`, `B0_cast`, `A0_pos`, `B0_pos` との対応が見えにくくなる可能性がある。

従ってここでの対称な二定義は、単なる不要重複というより **数学的な二因子構造を API にそのまま反映した意図的重複** と評価できる。

## 最適化候補

本 `def` 自体には実質的な最適化余地はほとんどない。

考えられる代替案としては、`A0` / `B0` 共通 helper

```lean
def naturalRepresentative (z : ℤ) : ℕ := z.natAbs
```

を置く方法がある。しかしこれは `Int.natAbs` の薄い別名にすぎず、抽象化コストに対して利益が小さい。

別案として positive-natural subtype を返し、`B0_pos` 相当を data に持たせることも可能である。ただしその場合、後続で `Nat.Coprime`、冪、可除性など標準 `ℕ` API を使うたびに projection や coercion が増える可能性がある。

また `Int.toNat` を使う案も考えられるが、negative input に対する意味が `natAbs` と異なる。現行証明は positivity を別 theorem に保持しているため `toNat` でも成立する可能性はあるが、cast lemma と downstream simplification の優劣は Lean build を行わない本実行では確認できない。

従って現行の `natAbs` を使った単純な bridge は妥当である。上記はすべて **未検証の設計候補** とする。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本定義が Mathlib 側で直接必要とする中心機能は

- `Int.natAbs`
- `ℤ`, `ℕ` の基本型と coercion infrastructure

である。

`zeroSectorB`、`GoldenZeroSectorCandidate`、その fields は project 内の upstream declarations なので、module 全体として必要な最小 import は本 `def` 単独では確定できない。

従って `import Mathlib` をより狭い import 群へ縮小できる可能性は高いが、具体的な最小 import set は Lean build 禁止条件のため **未確認** である。

## Comparator challenge 化の可否

**可能。theorem proving より representation / API design 比較に向く。難度は初級。**

比較対象としては次が適している。

- `Int.natAbs` を使う現行設計。
- `Int.toNat` を使う設計。
- positivity proof を持つ subtype を返す設計。
- signed factor を `ℤ` のまま保持し、自然数化をさらに遅延する設計。
- `A0` / `B0` を別々に named API として持つ設計と、generic helper に統合する設計。

特に「total な data definition と、その意味を保証する theorem を分離する」という Lean API 設計の教材として適している。

## PDF との照合

対象 branch には既存の日英 PDF

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを repository 上で確認した。

ただし GitHub コネクタの通常 text fetch は binary PDF 本文を返さないため、本実行では具体的ページ・節・式番号との直接照合はできていない。その位置については推測しない。

本解説の Lean code、宣言順、直接依存、`A0` との対称性、後続 `A0_cast` への接続は最新 branch の `Flt5DkMath/FLT5StandAlone.lean` を正本として確認した。

## 次に読むべき宣言

次の宣言は 0318 `GoldenZeroSectorCandidate.A0_cast`、種別は **`theorem`** である。

```lean
/-- Cast equation for the positive lower natural representative. -/
theorem A0_cast (p : GoldenZeroSectorCandidate) :
    (p.A0 : ℤ) = zeroSectorA p.r p.s p.d := by
  exact Int.ofNat_natAbs_of_nonneg p.A_pos.le
```

0316–0317 で自然数代表 $A_0,B_0$ が揃ったため、ここからはそれらを signed factors $A,B$ と正確に同一視する cast bridge の証明へ進む。

0318 はまず lower factor について

$$
(A_0:\mathbb Z)=A
$$

を回収し、その後の対応する `B0_cast` と合わせて、自然数上で exact factor identities を再構築する準備を整える。