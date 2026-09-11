# 0382 `five_not_dvd_D`

## 宣言種別

`theorem`

`GoldenZeroSectorDescentPacket` namespace 内で、packet の fifth-power root `D` が 5 で割れないことを示す補題である。

## Lean コード

```lean
theorem five_not_dvd_D (p : GoldenZeroSectorDescentPacket) :
    ¬ 5 ∣ p.D := by
  intro hD
  apply p.five_not_dvd_H
  rw [p.H_eq]
  exact dvd_pow (Int.natCast_dvd.mpr hD) (by decide : 5 ≠ 0)
```

## Lean の型

namespace を展開すると、型は概念的に

```lean
GoldenZeroSectorDescentPacket.five_not_dvd_D :
  (p : GoldenZeroSectorDescentPacket) → ¬ 5 ∣ p.D
```

である。

ここで `p.D : ℕ` なので、結論の

```lean
¬ 5 ∣ p.D
```

は自然数 `ℕ` 上の非可除性である。

一方、直接利用する直前の theorem

```lean
p.five_not_dvd_H :
  ¬ (5 : ℤ) ∣ goldenFifthSndFactor p.base.fst p.base.snd
```

は整数 `ℤ` 上の非可除性である。このため証明途中では

```lean
Int.natCast_dvd.mpr hD
```

によって自然数の可除性を整数へ移送している。

## 数学的主張

`base = (r,s)` と置き、

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s)
$$

と書く。

packet は field `H_eq` によって

$$
H(r,s)=D^5
$$

を保持している。

0381 `five_not_dvd_H` ではすでに

$$
5\nmid H(r,s)
$$

が証明されている。

今回の theorem は、この二つを組み合わせて

$$
5\nmid D
$$

を導く。

反対に $5\mid D$ と仮定すれば、当然

$$
5\mid D^5
$$

である。さらに $H(r,s)=D^5$ なので

$$
5\mid H(r,s)
$$

となり、0381 に矛盾する。

したがって

$$
5\nmid D
$$

である。

## 証明全体での役割

この theorem は、zero-sector descent packet に保存された 5-adic clean property を、quartic factor からその第五根 `D` へ降ろす役割を持つ。

直前までの流れは

$$
5\nmid N(r,s)
\Longrightarrow
5\nmid H(r,s)
\Longrightarrow
5\nmid D
$$

である。

ここで $N(r,s)=\operatorname{goldenNorm}(r,s)$ である。

この `D` の 5 非可除性は後続 `lift_relPrime_conj` で直接利用される。正本では

```lean
have hD5 : Nat.Coprime (p.D ^ 5) 5 :=
  Nat.Coprime.pow_left 5
    ((show Nat.Prime 5 by norm_num).coprime_iff_not_dvd.mpr
      p.five_not_dvd_D).symm
```

という形で、

$$
\gcd(D^5,5)=1
$$

を構成する材料になっている。

さらに `lift_relPrime_conj` では `D^5` と `5\,|s|^4` の coprimality を組み立て、quadratic lift とその共役が nonunit common divisor を持たないことを証明する。その後 fifth-power factorization の unit sector を排除するため、今回の theorem は re-entry 後の coprimality chain における重要な中継点である。

## 直接依存する定義・補題

直接依存するプロジェクト内宣言は次である。

- `GoldenZeroSectorDescentPacket`
- `GoldenZeroSectorDescentPacket.H_eq`
- `GoldenZeroSectorDescentPacket.five_not_dvd_H`
- `goldenFifthSndFactor`

Mathlib / Lean 側で直接使う主要機能は次である。

- `Int.natCast_dvd`
- `dvd_pow`
- `decide`
- `rw`
- `intro`
- `apply`
- `exact`

0380 `H_pos` や 0379 `snd_natAbs_eq` には直接依存しない。この theorem は `H_eq` と `five_not_dvd_H` だけで数学的には閉じている。

## 証明の流れ

1. 結論を否定し、自然数 `D` が 5 で割れると仮定する。

   ```lean
   intro hD
   ```

   すなわち

   $$
   5\mid D
   $$

   を仮定する。

2. 0381 の非可除性 theorem を contradiction target として使う。

   ```lean
   apply p.five_not_dvd_H
   ```

   これにより goal は

   ```lean
   (5 : ℤ) ∣ goldenFifthSndFactor p.base.fst p.base.snd
   ```

   へ変わる。

3. packet の fifth-power identity で quartic factor を書き換える。

   ```lean
   rw [p.H_eq]
   ```

   goal は概念的に

   $$
   5\mid D^5
   $$

   となる。ただし右辺は整数へ cast された `D` の第五冪である。

4. 仮定 `hD : 5 ∣ p.D` を整数可除性へ移す。

   ```lean
   Int.natCast_dvd.mpr hD
   ```

   これにより

   ```lean
   (5 : ℤ) ∣ (p.D : ℤ)
   ```

   を得る。

5. `dvd_pow` によって第五冪へ可除性を持ち上げる。

   ```lean
   dvd_pow (Int.natCast_dvd.mpr hD) (by decide : 5 ≠ 0)
   ```

   よって

   $$
   5\mid (D:\mathbb Z)^5
   $$

   が得られ、`p.five_not_dvd_H` と矛盾する。

## Lean 固有の処理

### `apply p.five_not_dvd_H`

`p.five_not_dvd_H` の型は否定命題

```lean
¬ (5 : ℤ) ∣ goldenFifthSndFactor p.base.fst p.base.snd
```

である。`intro hD` 後の goal は `False` なので、この否定命題を `apply` すると Lean は

```lean
(5 : ℤ) ∣ goldenFifthSndFactor p.base.fst p.base.snd
```

を新しい goal とする。

0381 と同じく、否定命題を contradiction function として直接適用する Lean の典型的な書き方である。

### `rw [p.H_eq]`

`H_eq` は packet の field であり、

```lean
goldenFifthSndFactor p.base.fst p.base.snd = (p.D : ℤ) ^ 5
```

を保持する。

したがって quartic polynomial の定義を展開する必要はなく、抽象化された invariant を一回 rewrite するだけで fifth-power divisibility へ移れる。

### `Int.natCast_dvd.mpr hD`

`hD` は `ℕ` 上の可除性だが、`p.H_eq` の右辺は `ℤ` 上にある。

`Int.natCast_dvd` は自然数の divisibility と整数 cast 後の divisibility を橋渡しする。`.mpr` は同値の右向き、すなわち自然数側から整数側への移送に使われている。

### `dvd_pow`

`dvd_pow` は

$$
a\mid b \Longrightarrow a\mid b^n
$$

という基本的 closure を使う。

ここでは `a = 5`, `b = (p.D : ℤ)`, `n = 5` である。

第二引数

```lean
(by decide : 5 ≠ 0)
```

は指数が 0 でないことの証拠である。指数が正であることを numeral decision procedure で即座に閉じている。

## 冗長・重複箇所

証明は 5 行で完結しており、数学的重複はほぼない。

ただし、FLT5 全体で「`5 ∤ x^5` から `5 ∤ x`」「`5 ∣ x` なら `5 ∣ x^5`」のような prime-power divisibility が繰り返される場合には、5 専用の helper theorem を用意する余地はある。

今回の証明については、`rw [p.H_eq]` と `dvd_pow` の組み合わせが非常に直接的なので、専用 helper を導入するとむしろ依存関係が増える可能性が高い。

また `Int.natCast_dvd.mpr hD` は `Nat` / `Int` 境界がこの一箇所に閉じ込められており、現状の方が型の流れを追いやすい。

## 最適化候補

1. **現状維持が第一候補**

   証明は数学的推論の順序と Lean code がほぼ一致しており、十分に短い。

2. **5-adic clean root lemma の一般化**

   より一般に prime `q` と正の指数 `n` に対して

   $$
   q\nmid x^n \Longrightarrow q\nmid x
   $$

   を packet-independent helper として使う設計も可能である。ただし Mathlib の prime divisibility API で十分表現できるなら、プロジェクト固有 lemma を増やさない方がよい。

3. **`Nat` / `Int` 境界の統一**

   `D` を packet 内で最初から `ℤ` として保持すれば cast は減る。しかし `D_pos : 0 < D`、強い自然数帰納法、power root の正値性など下流の用途を考えると、`D : ℕ` の現在設計には合理性がある。今回一箇所の cast 削減だけを理由に型を変えるべきではない。

4. **named corollary の追加**

   下流で `Nat.Coprime p.D 5` を何度も構成するなら、

   ```lean
   theorem coprime_D_five ... : Nat.Coprime p.D 5 := ...
   ```

   のような API を追加し、`five_not_dvd_D` を divisibility-level primitive theorem と位置づけることは可能である。

## 必要 Mathlib import と import 最適化候補

standalone 正本は `import Mathlib` を使用している。

この theorem 単体で必要になる Mathlib 側の要素は概ね次である。

- 自然数・整数の可除性
- `Int.natCast_dvd`
- `dvd_pow`
- numeral の decidable proof を与える `decide`
- 基本 tactic `rw`, `intro`, `apply`, `exact`

この theorem 自体では `ring`, `ring_nf`, `norm_num`, `omega` のような重い tactic は使わない。

したがって standalone 全体の `import Mathlib` に対して、この宣言だけならかなり小さい import で済む可能性が高い。ただしプロジェクト側の `GoldenZeroSectorDescentPacket`, `goldenFifthSndFactor`, `five_not_dvd_H` に到達する import が別途必要である。

Lean ビルドを行わない条件のため、厳密な最小 Mathlib import 集合は確認していない。具体的な module 名の断定は避ける。

## Comparator challenge 化の可否

**可能。Nat/Int cast と power divisibility を含む小規模 challenge に向く。**

challenge の核は次の三段階である。

1. `5 ∣ D` という `Nat` 側の仮定を受け取る。
2. `H = (D : ℤ)^5` を rewrite する。
3. cast 後の divisibility を `dvd_pow` で第五冪へ持ち上げ、`5 ∤ H` と矛盾させる。

特に Comparator の観点では、単なる `ring` challenge ではなく、

- namespace field projection
- contradiction via negated divisibility
- `Nat → Int` divisibility transport
- power divisibility

を正しく選べるかを見る問題として有用である。

challenge 化する場合は `GoldenZeroSectorDescentPacket` 全体を持ち込まず、

```lean
(hH : H = (D : ℤ) ^ 5)
(hnot : ¬ (5 : ℤ) ∣ H)
```

程度の最小仮定へ縮約すれば、Comparator の API 選択能力を測りやすい。

## 次に読むべき宣言

次は 0383 `coprime_s_H`、種別は `theorem` である。

```lean
theorem coprime_s_H (p : GoldenZeroSectorDescentPacket) :
    Nat.Coprime p.base.snd.natAbs
      (goldenFifthSndFactor p.base.fst p.base.snd).natAbs :=
  coprime_natAbs_goldenFifthSndFactor_of_coprime
    p.base.fst p.base.snd p.coprime_coords
```

これは primitive coordinate condition

$$
\gcd(|r|,|s|)=1
$$

から

$$
\gcd\bigl(|s|,|H(r,s)|\bigr)=1
$$

を直接取り出す theorem である。

0382 までで 5-adic clean property を `D` まで運んだ後、0383 からは `s`, `H`, `D` の間の coprimality chain を組み立てる段階へ入る。