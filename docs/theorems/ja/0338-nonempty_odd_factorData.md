# 0338 — `nonempty_odd_factorData`

## 宣言種別

この宣言は **`private theorem`** である。

```lean
private theorem nonempty_odd_factorData
    (p : GoldenZeroSectorInversionPacket) (hc : Odd p.source.c) :
    Nonempty (GoldenZeroSectorFactorData p) := by
  obtain ⟨A1, B1, hA, hAodd, hB, hBodd⟩ := p.odd_factor_halves hc
  have hcop : Nat.Coprime A1 B1 := by
    apply coprime_of_odd_of_no_common_odd_prime hAodd
    intro q hq hq2 hqA1 hqB1
    apply p.no_common_odd_prime q hq hq2
    · rw [hA]
      exact dvd_mul_of_dvd_right hqA1 2
    · rw [hB]
      exact dvd_mul_of_dvd_right hqB1 2
  have hred : A1 * B1 = zeroSectorQ p.source.c ^ 5 := by
    apply Nat.mul_left_cancel (show 0 < 4 by norm_num)
    calc
      4 * (A1 * B1) = p.source.A0 * p.source.B0 := by
        rw [hA, hB]
        ring
      _ = 4 * zeroSectorQ p.source.c ^ 5 := p.factor_product
  obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := fifth_power_factor_split hcop hred
  have hePos : 0 < e := by
    by_contra he0
    have : e = 0 := Nat.eq_zero_of_not_pos he0
    have hpos := p.A0_pos
    rw [hA, he, this] at hpos
    norm_num at hpos
  have hfPos : 0 < f := by
    by_contra hf0
    have : f = 0 := Nat.eq_zero_of_not_pos hf0
    have hpos := p.B0_pos
    rw [hB, hf, this] at hpos
    norm_num at hpos
  have hef : Nat.Coprime e f := by
    have hpows : Nat.Coprime (e ^ 5) (f ^ 5) := by
      simpa [he, hf] using hcop
    exact (hpows.of_dvd_left (dvd_pow_self e (by decide))).of_dvd_right
      (dvd_pow_self f (by decide))
  have heodd : Odd e := (Nat.odd_pow_iff (by decide)).mp (he ▸ hAodd)
  have hfodd : Odd f := (Nat.odd_pow_iff (by decide)).mp (hf ▸ hBodd)
  have hownership : e * f = zeroSectorQ p.source.c := by
    apply Nat.pow_left_injective (by decide : 5 ≠ 0)
    calc
      (e * f) ^ 5 = e ^ 5 * f ^ 5 := mul_pow e f 5
      _ = A1 * B1 := by rw [← he, ← hf]
      _ = zeroSectorQ p.source.c ^ 5 := hred
  have hdiff : e ^ 5 + 4 * p.source.d ^ 5 = f ^ 5 := by
    have hfactorDifference := p.factor_difference
    rw [hA, hB, he, hf] at hfactorDifference
    omega
  exact ⟨.odd e f hePos hfPos hef (hownership ▸ p.coprime_Q_d)
    heodd hfodd (by rw [hA, he]) (by rw [hB, hf]) hownership hdiff⟩
```

`private` であるため、この定理名は現在のソースファイル外へ通常の公開 API として露出しない。役割は後続の factor packet 構築の内部補助定理である。

## Lean の型

本体の型は

```lean
(p : GoldenZeroSectorInversionPacket) →
Odd p.source.c →
Nonempty (GoldenZeroSectorFactorData p)
```

である。

つまり、零セクター反転 packet `p` において tenth-power base `c` が奇数なら、0334 で定義された dependent inductive

```lean
GoldenZeroSectorFactorData p
```

には少なくとも一つ値が存在する、と述べる。

最終的に構築される値は `.odd ...` constructor であり、単なる存在ではなく、正性・互いに素性・奇性・第五冪分解・ownership・差分方程式をすべて証明付きで埋め込んだ certificate である。

## 数学的主張

仮定は

$$
\operatorname{Odd}(c).
$$

0339 より前段で確立済みの odd branch の二進分解から

$$
A_0=2A_1,\qquad B_0=2B_1,
$$

かつ $A_1,B_1$ が奇数であることを得る。

さらに共通奇素因子が存在しないことから

$$
\gcd(A_1,B_1)=1
$$

を示し、積恒等式

$$
A_0B_0=4Q^5,
\qquad
Q=5^5c^8
$$

を $A_0=2A_1$, $B_0=2B_1$ に代入して

$$
A_1B_1=Q^5
$$

へ簡約する。

互いに素な二因子の積が第五冪なので `fifth_power_factor_split` により

$$
A_1=e^5,
\qquad
B_1=f^5
$$

を得る。

ここから

$$
e>0,\qquad f>0,
$$

$$
\gcd(e,f)=1,
$$

$$
\operatorname{Odd}(e),\qquad \operatorname{Odd}(f),
$$

および

$$
ef=Q
$$

を回収する。

最後に元の factor difference から

$$
e^5+4d^5=f^5
$$

を得て、`GoldenZeroSectorFactorData.odd` constructor の全フィールドを満たす。

## FLT5 証明全体での役割

0334 `GoldenZeroSectorFactorData` は三 branch の exact factor certificate の型を定義しただけであり、その型が実際に inhabit されることは別途示す必要がある。

今回の定理はそのうち **odd-`c` branch の existence constructor** である。

流れは

```text
GoldenZeroSectorInversionPacket
        │
        ├─ c is odd
        │
        ▼
A0 = 2*A1, B0 = 2*B1
        │
        ▼
Coprime A1 B1
        │
        ▼
A1*B1 = Q^5
        │
        ▼
A1 = e^5, B1 = f^5
        │
        ▼
GoldenZeroSectorFactorData.odd
```

である。

0337 `GoldenZeroSectorFactorPacket` は

```lean
factors : GoldenZeroSectorFactorData inversion
```

を要求するため、今回の `Nonempty` theorem は packet の第2フィールドを odd branch で実際に供給するための内部部品となる。

## 直接依存する定義・補題

### `GoldenZeroSectorInversionPacket.odd_factor_halves`

`hc : Odd p.source.c` から

```lean
∃ A1 B1,
  p.source.A0 = 2 * A1 ∧ Odd A1 ∧
  p.source.B0 = 2 * B1 ∧ Odd B1
```

に相当する half-factor data を得る。今回の出発点である。

### `coprime_of_odd_of_no_common_odd_prime`

`A1` が odd であり、`A1,B1` に共通する奇素数が存在しないことから

```lean
Nat.Coprime A1 B1
```

を構築する。

### `GoldenZeroSectorInversionPacket.no_common_odd_prime`

0328 の theorem。`A0,B0` の共通奇素因子を禁止する。

今回 `q ∣ A1`, `q ∣ B1` を `A0=2A1`, `B0=2B1` 経由で `q ∣ A0`, `q ∣ B0` へ持ち上げて矛盾させる。

### `GoldenZeroSectorInversionPacket.factor_product`

$$
A_0B_0=4Q^5
$$

を供給する。

### `fifth_power_factor_split`

互いに素な積が第五冪なら、それぞれが第五冪であることを取り出す既存補題である。

今回

```lean
hcop : Nat.Coprime A1 B1
hred : A1 * B1 = zeroSectorQ p.source.c ^ 5
```

から

```lean
A1 = e ^ 5
B1 = f ^ 5
```

を得る。

### `A0_pos`, `B0_pos`

`e=0` または `f=0` を仮定した際、`A0>0`, `B0>0` と第五冪表示を衝突させて正性を得る。

### `GoldenZeroSectorInversionPacket.coprime_Q_d`

0330 の theorem。

$$
\gcd(Q,d)=1
$$

を `hownership : e*f=Q` で書き換えて

```lean
Nat.Coprime (e * f) p.source.d
```

を得る。

### `GoldenZeroSectorInversionPacket.factor_difference`

$A_0,B_0$ の差分恒等式を、`A0=2e^5`, `B0=2f^5` へ書き換えて

$$
e^5+4d^5=f^5
$$

へ変換する。

## 証明の流れ

### 1. odd half factors を抽出

```lean
obtain ⟨A1, B1, hA, hAodd, hB, hBodd⟩ := p.odd_factor_halves hc
```

により $A_0,B_0$ から因子 2 を一つずつ除く。

### 2. `A1` と `B1` の互いに素性を証明

共通奇素数 $q$ を仮定すると、`A0=2A1`, `B0=2B1` により $q$ は $A_0,B_0$ の双方を割る。

これは `p.no_common_odd_prime` と矛盾するため

```lean
hcop : Nat.Coprime A1 B1
```

が得られる。

### 3. 積を純粋な第五冪へ簡約

`Nat.mul_left_cancel` で係数 4 を消し、

$$
A_1B_1=Q^5
$$

を得る。

### 4. coprime fifth-power split

```lean
obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := fifth_power_factor_split hcop hred
```

によって

```lean
he : A1 = e ^ 5
hf : B1 = f ^ 5
```

に相当する witness を得る。

### 5. `e,f` の正性

もし $e=0$ なら $A_0=2e^5=0$ となり `p.A0_pos` に反する。同様に $f>0$ も示す。

### 6. base level の互いに素性と奇性

`Coprime (e^5) (f^5)` から `dvd_pow_self` を使って `Coprime e f` へ降ろす。

また `Nat.odd_pow_iff` を用いて $e^5,f^5$ の奇性を base の奇性へ戻す。

### 7. ownership `e*f=Q`

双方の第五冪が等しいことを示してから

```lean
Nat.pow_left_injective (by decide : 5 ≠ 0)
```

を使い、

$$
(ef)^5=Q^5
\Longrightarrow
ef=Q
$$

とする。

### 8. branch 固有の差分方程式

`p.factor_difference` を $A_0=2e^5$, $B_0=2f^5$ へ書き換え、`omega` で

$$
e^5+4d^5=f^5
$$

を得る。

### 9. `.odd` certificate を構築

最後に

```lean
GoldenZeroSectorFactorData.odd
```

へすべての witness と proof を詰め、`Nonempty` で包んで返す。

## Lean 固有の処理

### `Nonempty`

結論は

```lean
Nonempty (GoldenZeroSectorFactorData p)
```

であり、具体的 factor data を返しながら API 上は「型が inhabit される」という形に隠蔽する。

これは後続で branch data の存在だけ必要な箇所と、具体的 constructor を直接公開する箇所を分離しやすい。

### `private theorem`

宣言が private なので、同じファイル内部では名前付き補題として使えるが、外部モジュール向けの安定 API ではない。implementation detail として branch 構築を分解する設計である。

### `obtain` と nested existential witness

`fifth_power_factor_split` の戻り値は nested pair / existential 形なので

```lean
obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := ...
```

で一度に分解している。

### equality rewrite による proof transport

```lean
hownership ▸ p.coprime_Q_d
```

は `e*f=Q` を使って

```lean
Nat.Coprime Q d
```

を

```lean
Nat.Coprime (e*f) d
```

へ transport している。

### `by decide`

指数 $5$ が非零であることや `dvd_pow_self` に必要な有限算術条件を decidable computation で閉じている。

### `omega`, `ring`, `norm_num`

証明の構造部分は既存補題で組み立て、係数整理・自然数線形算術・零判定は tactic に委譲している。

## 冗長・重複箇所

`hePos` と `hfPos` はほぼ対称な証明であり、コード形もほぼ同じである。

また `heodd` / `hfodd`、および `A_eq` / `B_eq` の最終 rewrite も左右対称である。

ただし theorem 全体は odd branch の certificate を一回だけ構築する内部補題であり、現状の重複量は限定的である。

`Nat.Coprime e f` の導出は、一度 power-level coprime を作ってから `of_dvd_left` / `of_dvd_right` で base へ落としている。もし Mathlib に「正の指数に対する `Coprime (a^n) (b^n) ↔ Coprime a b`」を直接扱う既存 lemma が適合するなら短縮余地があるが、今回の正本からその最適な lemma 名までは確認できない。

## 最適化候補

### 左右対称な正性証明の helper 化

`A0` / `B0` に対する同型のゼロ排除を局所 helper にまとめれば少し短くできる。ただし private theorem 内だけでしか使わないなら、抽象化コストとの釣り合いは微妙である。

### fifth-power split API の強化

`fifth_power_factor_split` が witness と同時に正性・奇性・base coprimalityまで返すような強い certificate を提供すれば、後半の派生証明を減らせる可能性がある。

一方、その補題を一般用途で保ちたいなら現状の「純粋な第五冪 split」と branch 固有性質の回収を分ける設計の方が再利用性は高い。

### ownership の注入性処理

`(e*f)^5=Q^5` から `e*f=Q` を得る処理は明瞭であり、現在の `Nat.pow_left_injective` は適切である。もし同形処理が他 branch に繰り返されるなら local lemma 化は有効である。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

今回直接使われる Mathlib 側の機能には少なくとも次が含まれる。

- `Nat.Coprime`
- divisibility lemmas (`dvd_mul_of_dvd_right`, `dvd_pow_self`)
- `Nat.eq_zero_of_not_pos`
- `Nat.odd_pow_iff`
- `Nat.pow_left_injective`
- `mul_pow`
- `omega`
- `ring`
- `norm_num`
- `simpa`, `rw`, `obtain`

さらに domain-specific な主要依存は standalone 内の先行宣言であり、元の分割モジュールでは `SignedGoldenZeroSectorFactorization.lean` 周辺に属する。

`import Mathlib` はこの theorem 単体には広すぎる可能性が高い。しかし Lean ビルドを行わない条件なので、具体的な最小 import 列は検証済みとはしない。

## Comparator challenge 化の可否

**非常に適している。難度は中〜高。**

理由は、単純な arithmetic hole filling ではなく、次の複数段階を正しい順序で再構築する必要があるからである。

1. odd half factorization の取得、
2. common odd prime exclusion から coprimality の構築、
3. product identity の係数除去、
4. coprime fifth-power split、
5. positivity / parity / coprimality の base-level 回収、
6. fifth-power injectivity による ownership、
7. difference identity から branch equation、
8. dependent constructor `.odd` の組み立て。

特に良い challenge は theorem statement と主要既存補題だけを与え、`.odd` constructor の全フィールドを自力で埋めさせる形式である。

Comparator は最終 term の構文一致より、同じ `GoldenZeroSectorFactorData p` inhabitant を型検査できるかを重視するのがよい。

## 次に読むべき宣言

次の宣言は

```lean
/-- In the even-`c` branch, both inversion factors contain at least three
factors of two. -/
theorem GoldenZeroSectorInversionPacket.eight_dvd_factors
    (p : GoldenZeroSectorInversionPacket) (hc : Even p.source.c) :
    8 ∣ p.source.A0 ∧ 8 ∣ p.source.B0 := by
```

である。

種別は **`theorem`**。

今回が odd-`c` branch の factor certificate 構築であったのに対し、次は even-`c` branch の入口であり、まず

$$
8\mid A_0,
\qquad
8\mid B_0
$$

という二進付値の下界を確立する。

その後 `even_factor_eighths` を経て `nonempty_even_factorData` へ進み、odd branch と対になる even branch の exact factor certificate 構築へ接続する。