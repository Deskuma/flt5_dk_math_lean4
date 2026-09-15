# 0318 — `GoldenZeroSectorCandidate.A0_cast`

## 宣言種別

これは **`theorem`** である。

0316 `GoldenZeroSectorCandidate.A0` で導入した自然数代表 $A_0$ を、0314 `GoldenZeroSectorCandidate.A_pos` で確立済みの正性を使って元の signed inversion factor $A$ と正確に同一視する cast bridge である。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- Cast equation for the positive lower natural representative. -/
theorem A0_cast (p : GoldenZeroSectorCandidate) :
    (p.A0 : ℤ) = zeroSectorA p.r p.s p.d := by
  exact Int.ofNat_natAbs_of_nonneg p.A_pos.le
```

型を依存関係が見える形で読むと、candidate `p` に対して

```lean
(p.A0 : ℤ) = zeroSectorA p.r p.s p.d
```

という整数等式を返す theorem である。

左辺 `p.A0` は `ℕ` なので `: ℤ` に coercion され、右辺 `zeroSectorA ...` は最初から `ℤ` である。

## 数学的主張

0316 で

```lean
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs
```

と定義したため、数学的には

$$
A_0=|A|,
$$

ただし

$$
A=\operatorname{zeroSectorA}(r,s,d)
$$

である。

さらに 0314 `A_pos` により

$$
A>0
$$

が証明済みなので、当然 $A\ge0$ であり、

$$
|A|=A.
$$

従って自然数 $A_0$ を整数へ戻した値は元の lower factor そのものになる：

$$
(A_0:\mathbb Z)=A.
$$

本 theorem はこの極めて基本的な事実を Lean の `ℕ` / `ℤ` 境界で厳密に固定する。

## 証明全体での役割

zero-sector inversion では、まず signed integer world で

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

が構築された。

その後 0316 `A0` と 0317 `B0` で

$$
A_0=|A|,\qquad B_0=|B|
$$

という自然数代表へ移る。

しかし `natAbs` を適用しただけでは、型としては符号情報を失った自然数しか残らない。本 0318 `A0_cast` は、既に証明済みの $A>0$ を再利用して

$$
(A_0:\mathbb Z)=A
$$

を回収することで、自然数側の factorization と整数側の inversion identity を往復可能にする。

直後の `B0_cast` と対になって

$$
(A_0:\mathbb Z)=A,
\qquad
(B_0:\mathbb Z)=B
$$

が揃うと、signed world で得た積・差・順序の情報を自然数へ安全に輸送できる。したがって本 theorem は新しい数論的制約を発見する theorem ではなく、**後続の `Nat` factorization machinery に意味を失わず接続する correctness bridge** である。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate.A0`

左辺の自然数代表を定義する直接依存である。

```lean
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs
```

従って theorem の左辺は定義展開すると

```lean
((zeroSectorA p.r p.s p.d).natAbs : ℤ)
```

になる。

### `GoldenZeroSectorCandidate.A_pos`

本 theorem の semantic core である。

既に

$$
0<A
$$

を保証しており、proof term では

```lean
p.A_pos.le
```

によって

$$
0\le A
$$

へ弱めて利用する。

`A0_cast` に必要なのは strict positivity そのものではなく nonnegativity なので、この `.le` がちょうど Mathlib lemma の要求する形へ変換している。

### `Int.ofNat_natAbs_of_nonneg`

証明を一行で閉じる Mathlib lemma である。

概念的には、整数 $z$ に対し $0\le z$ なら

$$
(\operatorname{natAbs}(z):\mathbb Z)=z
$$

を与える。

本 theorem では $z=\operatorname{zeroSectorA}(p.r,p.s,p.d)$ を代入している。

### `zeroSectorA`

右辺の signed lower factor を与える project 側定義である。`A0_cast` 自身はその内部式を展開しないため、ここでは $A$ の具体的多項式構造には依存しない。

## 証明の流れ

1. ゴールは

   ```lean
   (p.A0 : ℤ) = zeroSectorA p.r p.s p.d
   ```

   である。
2. `p.A0` は definitionally

   ```lean
   (zeroSectorA p.r p.s p.d).natAbs
   ```

   である。
3. 0314 `A_pos` から

   ```lean
   p.A_pos.le
   ```

   により

   ```lean
   0 ≤ zeroSectorA p.r p.s p.d
   ```

   を得る。
4. `Int.ofNat_natAbs_of_nonneg` にこの nonnegativity proof を渡す。
5. 得られる equality が、`A0` の定義展開後の現在のゴールと一致するため `exact` で終了する。

## Lean 固有の処理

### `ℕ` から `ℤ` への coercion

`A0 : ℕ` に対して

```lean
(p.A0 : ℤ)
```

と明示的 cast を置いている。自然数 factorization と signed integer identities の境界を theorem の型そのものに露出させている点が重要である。

### strict positivity から nonnegativity への弱化

```lean
p.A_pos.le
```

の `.le` は

```lean
0 < A
```

から

```lean
0 ≤ A
```

を作る。Mathlib lemma `Int.ofNat_natAbs_of_nonneg` は nonnegative で十分なので、必要以上に強い仮定を使わない形になっている。

### `A0` を明示的に `unfold` していない

proof は

```lean
exact Int.ofNat_natAbs_of_nonneg p.A_pos.le
```

だけであり、`unfold A0` や `simp [A0]` を書いていない。

これは Lean が expected type と proof term の型を照合する際、`A0` の reducible definition を definitional reduction できるためである。短い proof だが、裏では

```lean
p.A0
```

と

```lean
(zeroSectorA p.r p.s p.d).natAbs
```

が定義的に同一視されている。

### dot notation

`A0`, `A_pos` は candidate を先頭引数に取る namespace API なので、

```lean
p.A0
p.A_pos
```

と書ける。これにより bridge theorem が candidate-centered な API として読みやすくなっている。

## 冗長・重複箇所

本 theorem 自体は一行 proof であり、局所的な冗長性はない。

ただし直後の `B0_cast` は完全に対称で、

```lean
exact Int.ofNat_natAbs_of_nonneg p.B_pos.le
```

となる。従って implementation pattern としては重複している。

しかし `A0_cast` / `B0_cast` という別々の named theorem を持つことで、後続証明では lower / upper factor の意味が明確になる。generic helper に統合すると theorem 名による意味付けが薄れ、利用側で追加の展開が必要になる可能性があるため、この対称重複は API 上は合理的である。

## 最適化候補

現行 proof は既に最小級であり、実質的な最適化余地はほとんどない。

説明性を優先するなら

```lean
  simpa [A0] using
    (Int.ofNat_natAbs_of_nonneg p.A_pos.le)
```

のように `A0` の展開を明示する候補がある。これは definitional reduction への依存を読者に見せる点では分かりやすい一方、現行の `exact` より長い。

また `A0` と `B0` に共通する generic cast lemma を作ることも理論上可能だが、対象整数と positivity proof を毎回渡すだけの薄い wrapper になりやすく、現行二 theorem より API が改善するとは限らない。

従って現時点では **現行の一行 proof を維持するのが最も自然** と評価できる。上記 alternative は Lean build を行わない本実行では未検証である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem が Mathlib 側で直接利用している中心 API は

- `Int.ofNat_natAbs_of_nonneg`
- order relation と `LT.lt.le`
- `ℕ` から `ℤ` への coercion

である。

一方、`GoldenZeroSectorCandidate`, `A0`, `A_pos`, `zeroSectorA` は project 内の upstream declarations である。

この theorem 単独なら `Mathlib` 全体より狭い import で十分である可能性が高い。ただし generated standalone module 全体の依存を保った最小 import set、ならびに `Int.ofNat_natAbs_of_nonneg` を供給する最小 Mathlib module の確定は、Lean build を行わない条件下では確認していない。従って具体的な import 縮小案は **未検証候補** とする。

## Comparator challenge 化の可否

**可能。初級〜中級の Lean bridge theorem challenge に適する。**

比較しやすい観点は次である。

- 現行の `exact Int.ofNat_natAbs_of_nonneg p.A_pos.le`。
- `simpa [A0] using ...` として definition 展開を明示する proof。
- `rw [A0]` などで goal を先に正規化してから lemma を適用する proof。
- generic helper lemma を設けて `A0_cast` / `B0_cast` を共通化する設計。

数学的難度は低いが、**definitional equality、coercion、strict-to-weak order conversion、library lemma selection** を一度に比較できるため Comparator 向けの教材価値は高い。

## PDF との照合

対象 branch には既存の日英 PDF

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを repository 上で確認した。

ただし GitHub コネクタの通常 text fetch は binary PDF 本文を返さないため、本実行では具体的ページ・節・式番号との直接照合はできていない。その対応位置は推測しない。

本解説の Lean code、宣言順、`A0` / `A_pos` への依存、直後の `B0_cast` への接続は、最新 branch の `Flt5DkMath/FLT5StandAlone.lean` を正本として確認した。

## 次に読むべき宣言

次の宣言は 0319 `GoldenZeroSectorCandidate.B0_cast`、種別は **`theorem`** である。

```lean
/-- Cast equation for the positive upper natural representative. -/
theorem B0_cast (p : GoldenZeroSectorCandidate) :
    (p.B0 : ℤ) = zeroSectorB p.r p.s p.d := by
  exact Int.ofNat_natAbs_of_nonneg p.B_pos.le
```

0318 が lower factor について

$$
(A_0:\mathbb Z)=A
$$

を回収したのに対し、0319 は upper factor について

$$
(B_0:\mathbb Z)=B
$$

を回収する。ここまで揃うと、自然数 pair $(A_0,B_0)$ を signed pair $(A,B)$ と完全に対応させた上で、後続の positivity・積・差・coprimality・power splitting へ進める。
