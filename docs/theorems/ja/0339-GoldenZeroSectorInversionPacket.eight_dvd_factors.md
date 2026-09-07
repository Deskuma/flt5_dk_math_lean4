# 0339 — `GoldenZeroSectorInversionPacket.eight_dvd_factors`

## 宣言種別

この宣言は **`theorem`** である。

```lean
/-- In the even-`c` branch, both inversion factors contain at least three
factors of two. -/
theorem GoldenZeroSectorInversionPacket.eight_dvd_factors
    (p : GoldenZeroSectorInversionPacket) (hc : Even p.source.c) :
    8 ∣ p.source.A0 ∧ 8 ∣ p.source.B0 := by
  rcases even_iff_two_dvd.mp hc with ⟨k, hk⟩
  have hs8 : (8 : ℤ) ∣ p.source.s := by
    refine ⟨-((2 : ℤ) ^ 7 * 5 ^ 6 * (k : ℤ) ^ 10), ?_⟩
    rw [p.s_eq, hk]
    push_cast
    ring
  have hsEven : Even p.source.s :=
    even_iff_two_dvd.mpr ((by norm_num : (2 : ℤ) ∣ 8).trans hs8)
  have hrOdd : Odd p.source.r := by
    rw [← Int.natAbs_odd, ← Nat.not_even_iff_odd]
    intro hrEven
    have hsEvenAbs : Even p.source.s.natAbs := hsEven.natAbs
    exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num)
      hrEven.two_dvd hsEvenAbs.two_dvd) p.source.coprime_coords
  rcases hrOdd with ⟨rh, hrh⟩
  rcases hs8 with ⟨st, hst⟩
  let z : ℤ := 2 * rh + 1 + 4 * st
  let u : ℤ := z ^ 2 + 80 * st ^ 2
  let w : ℤ := (p.source.d : ℤ) ^ 5
  have hzOdd : Odd z := by
    dsimp [z]
    exact (odd_two_mul_add_one rh).add_even
      (even_iff_two_dvd.mpr ⟨2 * st, by ring⟩)
  have huOdd : Odd u := by
    dsimp [u]
    exact hzOdd.pow.add_even
      (even_iff_two_dvd.mpr ⟨40 * st ^ 2, by ring⟩)
  have hwOdd : Odd w := by
    exact p.source.d_odd.natCast.pow
  have hAform : zeroSectorA p.source.r p.source.s p.source.d =
      4 * (u - w) := by
    simp only [zeroSectorA, zeroSectorU, zeroSectorX, zeroSectorW, z, u, w]
    rw [hrh, hst]
    ring
  have hBform : zeroSectorB p.source.r p.source.s p.source.d =
      4 * (u + w) := by
    simp only [zeroSectorB, zeroSectorU, zeroSectorX, zeroSectorW, z, u, w]
    rw [hrh, hst]
    ring
  have hEvenSub : Even (u - w) := by
    simp [Int.even_sub', huOdd, hwOdd]
  have hEvenAdd : Even (u + w) := huOdd.add_odd hwOdd
  have h8AZ : (8 : ℤ) ∣ zeroSectorA p.source.r p.source.s p.source.d := by
    rcases even_iff_two_dvd.mp hEvenSub with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hAform, ht]
    ring
  have h8BZ : (8 : ℤ) ∣ zeroSectorB p.source.r p.source.s p.source.d := by
    rcases even_iff_two_dvd.mp hEvenAdd with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [hBform, ht]
    ring
  constructor
  · apply Int.natCast_dvd.mp
    exact h8AZ
  · apply Int.natCast_dvd.mp
    exact h8BZ
```

## Lean の型

本体の型は

```lean
(p : GoldenZeroSectorInversionPacket) →
Even p.source.c →
8 ∣ p.source.A0 ∧ 8 ∣ p.source.B0
```

である。

つまり零セクター反転 packet `p` において tenth-power base `c` が偶数なら、自然数因子 `A0`, `B0` は双方とも少なくとも $2^3$ を含む、と述べる。

## 数学的主張

仮定は

$$
2\mid c.
$$

`p.s_eq` に `c=2k` を代入すると `s` は非常に高い二進因子を持ち、特に

$$
8\mid s
$$

が得られる。

一方 `r` と `|s|` は `p.source.coprime_coords` により互いに素であるため、`s` が偶数なら `r` は奇数でなければならない。

証明ではこの奇偶情報を使って補助量

$$
z=2r_h+1+4s_t,
$$

$$
u=z^2+80s_t^2,
$$

$$
w=d^5
$$

を導入し、`u` と `w` がともに奇数であることを示す。したがって

$$
u-w
$$

と

$$
u+w
$$

はどちらも偶数である。

零セクター因子は

$$
A_0=4(u-w),
$$

$$
B_0=4(u+w)
$$

という形に書けるので、括弧内の追加の因子 2 と外側の因子 4 を合わせて

$$
8\mid A_0,
\qquad
8\mid B_0
$$

が従う。

## FLT5 証明全体での役割

0338 `nonempty_odd_factorData` が odd-`c` branch の exact factor certificate を構築したのに対し、今回の定理は **even-`c` branch の二進付値解析の入口** である。

後続では `A0`, `B0` から共通因子 8 を除き、

```lean
GoldenZeroSectorInversionPacket.even_factor_eighths
```

により残りの二因子が opposite parity を持つことを示す。その後さらに第五冪分解へ進み、`GoldenZeroSectorFactorData.evenLeftLow` / `.evenRightLow` のどちらかを構築する。

流れは

```text
c even
  │
  ▼
8 ∣ s
  │
  ▼
r odd
  │
  ▼
u,w odd
  │
  ▼
u-w and u+w even
  │
  ▼
A0 = 4(u-w), B0 = 4(u+w)
  │
  ▼
8 ∣ A0 and 8 ∣ B0
```

である。

## 直接依存する定義・補題

### `GoldenZeroSectorInversionPacket`

今回の入力 packet。`source` 経由で `r,s,c,d,A0,B0` と、それらの関係式・互いに素性・奇性にアクセスする。

### `p.s_eq`

`source.s` と `c` の関係式を与える。`c=2k` を代入して $8\mid s$ を具体的 witness 付きで示す箇所に使われる。

### `p.source.coprime_coords`

`r` と `|s|` の互いに素性を供給する。`s` が偶数なのに `r` も偶数だと共通因子 2 が生じるため矛盾する。

### `p.source.d_odd`

$d$ の奇性を供給する。これを整数へ cast し第五冪して

```lean
hwOdd : Odd ((p.source.d : ℤ) ^ 5)
```

を得る。

### `zeroSectorA`, `zeroSectorB`, `zeroSectorU`, `zeroSectorX`, `zeroSectorW`

`A0`,`B0` の零セクター表示を展開し、補助量 `z,u,w` を用いた

```lean
4 * (u - w)
4 * (u + w)
```

の形へ正規化するために使う。

### `even_iff_two_dvd`, `Int.natAbs_odd`, `Nat.not_even_iff_odd`

自然数と整数をまたぐ parity / divisibility の変換に使われる。

### `Nat.not_coprime_of_dvd_of_dvd`

`r` と `|s|` がともに 2 で割れるという仮定を、`coprime_coords` と矛盾させる。

### `Int.natCast_dvd`

整数側で得た

```lean
(8 : ℤ) ∣ zeroSectorA ...
(8 : ℤ) ∣ zeroSectorB ...
```

を自然数側の `8 ∣ A0`, `8 ∣ B0` へ戻す最後の橋渡しに使われる。

## 証明の流れ

### 1. `c=2k` を取り出す

```lean
rcases even_iff_two_dvd.mp hc with ⟨k, hk⟩
```

により偶数性を具体的 witness に変換する。

### 2. `8 ∣ s` を示す

`p.s_eq` と `hk` を使って `s` を展開し、明示的 quotient

```lean
-((2 : ℤ) ^ 7 * 5 ^ 6 * (k : ℤ) ^ 10)
```

を与えて `ring` で閉じる。

### 3. `r` の奇性を強制する

`8 ∣ s` から `s` の偶数性を得る。もし `r` も偶数なら、`r` と `|s|` の双方が 2 で割れ、`coprime_coords` に反する。

### 4. odd normal form を作る

`r=2rh+1` と `s=8st` を展開し、`z`, `u`, `w` を導入する。`z` は奇数、そこから `u` も奇数、`d` の奇性から `w` も奇数となる。

### 5. `A0`, `B0` を `4(u±w)` へ変形

`zeroSectorA/B` 以下の定義を `simp only` で展開し、`rw [hrh, hst]` と `ring` により exact polynomial identity を得る。

### 6. `u±w` の偶数性を得る

奇数同士の差・和なので双方とも偶数である。

### 7. 8 の可除性を整数側で構築

`u±w=2t` と書き、

$$
4(u\pm w)=8t
$$

を `ring` で示す。

### 8. 自然数側へ戻す

`Int.natCast_dvd.mp` により整数上の可除性を `A0`,`B0 : ℕ` の可除性へ移す。

## Lean 固有の処理

### 整数と自然数をまたぐ証明

`A0`,`B0` 自体は自然数だが、零セクターの式変形は整数上で行われる。したがって途中では `(8 : ℤ) ∣ ...` を証明し、最後に `Int.natCast_dvd.mp` で自然数へ戻している。

### `rcases` による parity witness の抽出

`Even n` は existential な `n=2k` を内部に持つため、`rcases` で quotient を直接取り出し、その値を後続の polynomial normalization に使っている。

### `let` による式の局所圧縮

`z`, `u`, `w` は証明中の巨大な式を局所的に圧縮するための名前である。特に `zeroSectorA/B` の展開結果を parity の議論と分離する効果がある。

### `simp only` と `ring`

定義展開の範囲を `simp only` で制限し、その後の多項式恒等式だけを `ring` に処理させている。証明探索を広げず、正規化の責務を分離した書き方である。

### `push_cast`

自然数 witness `k` を整数式へ持ち上げた後、cast を正規化して `ring` が扱える形にする。

## 冗長・重複箇所

`h8AZ` と `h8BZ` の構築は完全に対称であり、違いは `u-w` と `u+w`、`hAform` と `hBform` だけである。

また `hzOdd`, `huOdd`, `hwOdd` から `hEvenSub`, `hEvenAdd` を得る部分も「奇数 ± 奇数は偶数」という共通パターンである。

ただし、この対称性を過度に抽象化すると零セクター式の具体的構造が見えにくくなるため、現在の明示的な二本立ても可読性上は妥当である。

## 最適化候補

1. `h8AZ` / `h8BZ` の共通部分を、`hform : X = 4*t` と `Even t` から `8 ∣ X` を返す小補題に抽出できる。

2. `r` の奇性証明は「`s` が偶数かつ `Coprime r |s|` なら `r` は奇数」という局所補題に切り出せる。類似の parity argument が他 branch に現れるなら再利用価値が高い。

3. `z`,`u`,`w` の導入は有効だが、`z` と `u` がこの定理以降も再利用されるなら named definition / local structure として上位に持ち上げる候補がある。現状この定理だけの一時変数なら `let` のままが軽い。

4. `Int.natCast_dvd.mp` を最後に二回使う代わりに、`A0`,`B0` の自然数版の正規形が利用できるなら整数往復を減らせる可能性がある。ただし現在の零セクター定義が整数中心であるため、実際に簡潔になるかは未確認である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

今回直接使われる主要機能は parity API、`Nat.Coprime`、整数 cast、`ring`、`norm_num`、`simp`、`push_cast` である。

元の生成元モジュールは `DkMath/FLT/Five/SignedGoldenZeroSectorFactorization.lean` であることが standalone の generated-source 境界から確認できる。

より狭い Mathlib import へ分解できる可能性は高いが、今回 Lean ビルドは行っていないため、最小 import 集合は **未確認** である。特に `ring`、parity、整数 cast の依存を同時に満たす最小組合せは実ビルドなしには断定しない。

## Comparator challenge 化の可否

**可。中程度から高い適性がある。**

この定理は Comparator challenge として次の二層に分けやすい。

- 数学層: `c` 偶数、`s` の exact formula、`Coprime r |s|`、`d` 奇数から $8\mid A_0,B_0$ を導く。
- Lean 層: `Nat` / `Int` cast、parity witness、`simp only`、`ring`、`Int.natCast_dvd` を適切につなぐ。

特に「自然数の偶数性 → 整数多項式の二進可除性 → 自然数 divisibility へ戻す」という型境界は、同じ数学を異なる Lean 設計で比較する課題として面白い。

一方、`zeroSectorA/B` など前段定義を全部要求すると challenge が局所的すぎる。Comparator 用には必要な exact identities を仮定として渡す縮約版と、実リポジトリ版の二段階にすると扱いやすい。

## 次に読むべき宣言

次は **0340 `GoldenZeroSectorInversionPacket.even_factor_eighths`** である。宣言種別は `theorem`。

```lean
theorem GoldenZeroSectorInversionPacket.even_factor_eighths
    (p : GoldenZeroSectorInversionPacket) (hc : Even p.source.c) :
    ∃ A1 B1 : ℕ,
      p.source.A0 = 8 * A1 ∧ p.source.B0 = 8 * B1 ∧
      ((Odd A1 ∧ Even B1) ∨ (Even A1 ∧ Odd B1)) := by
```

今回得た `8 ∣ A0` と `8 ∣ B0` を使って実際に eighth factors `A1`,`B1` を取り出し、その二つが同じ parity にはならず opposite parity に分岐することを示す。even branch の `evenLeftLow` / `evenRightLow` への分岐を初めて明示する宣言である。
