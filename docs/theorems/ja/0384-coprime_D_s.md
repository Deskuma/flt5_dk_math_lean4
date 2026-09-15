# 0384 `coprime_D_s`

## 宣言種別

`theorem`

`GoldenZeroSectorDescentPacket` namespace 内で、packet の fifth root `D` と base の第二座標 `s` の絶対値が互いに素であることを示す補題である。

## Lean コード

```lean
theorem coprime_D_s (p : GoldenZeroSectorDescentPacket) :
    Nat.Coprime p.D p.base.snd.natAbs := by
  have hcop := p.coprime_s_H
  have hHAbs :
      (goldenFifthSndFactor p.base.fst p.base.snd).natAbs = p.D ^ 5 := by
    rw [p.H_eq, Int.natAbs_pow]
    simp
  rw [hHAbs] at hcop
  exact ((Nat.coprime_pow_right_iff (by decide : 0 < 5)
    p.base.snd.natAbs p.D).mp hcop).symm
```

## Lean の型

namespace を展開した概念的な型は

```lean
GoldenZeroSectorDescentPacket.coprime_D_s :
  (p : GoldenZeroSectorDescentPacket) →
    Nat.Coprime p.D p.base.snd.natAbs
```

である。

`p.D : ℕ` は packet が保持する fifth root、`p.base.snd : ℤ` は黄金整数 `base` の第二座標である。`Nat.Coprime` を使うため、整数座標側は `Int.natAbs` によって自然数へ移されている。

## 数学的主張

`p.base = (r,s)` と書き、

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s)
$$

とする。

前段 0383 `coprime_s_H` は

$$
\gcd\bigl(|s|,|H(r,s)|\bigr)=1
$$

を与える。一方 packet の field `H_eq` は

$$
H(r,s)=D^5
$$

を保持する。`D` は自然数なので

$$
|H(r,s)|=D^5
$$

であり、したがって

$$
\gcd(|s|,D^5)=1.
$$

正の指数 5 に対して

$$
\gcd(a,b^5)=1
\Longleftrightarrow
\gcd(a,b)=1
$$

が成り立つため、最終的に

$$
\gcd(D,|s|)=1
$$

を得る。

## 証明全体での役割

この theorem は zero-sector descent の coprimality chain で、quartic factor の互いに素性を fifth root へ降ろす橋である。

直前の流れは

$$
\gcd(|r|,|s|)=1
\Longrightarrow
\gcd(|s|,|H(r,s)|)=1
$$

であり、今回さらに

$$
H(r,s)=D^5
$$

を用いて

$$
\gcd(D,|s|)=1
$$

へ進む。

この結果は直後の `lift_relPrime_conj` で利用される。そこでは quadratic lift とその共役に共通因子 `z` があると仮定し、その norm が `D^5` と `5|s|^4` の双方を割ることを示す。`coprime_D_s` と 0382 `five_not_dvd_D` によって `D^5` と `5|s|^4` が互いに素であるため、共通因子の norm は 1 に強制され、`z` が unit であることへつながる。

したがって 0384 は、第五冪の root `D` が visible coordinate `s` から算術的に分離されていることを確定し、golden lift の相対素性へ進むための主要な入力である。

## 直接依存する定義・補題

直接使われるプロジェクト内宣言は次である。

- `GoldenZeroSectorDescentPacket`
- `GoldenZeroSectorDescentPacket.coprime_s_H`
- `GoldenZeroSectorDescentPacket.H_eq`
- `goldenFifthSndFactor`

直接使われる Mathlib 側の主な API は次である。

- `Int.natAbs_pow`
- `Nat.coprime_pow_right_iff`
- `Nat.Coprime.symm`
- `simp` が利用する整数 natural cast の `natAbs` 簡約規則

0382 `five_not_dvd_D` はこの theorem 自体の直接依存ではない。ただし直後の `lift_relPrime_conj` では `coprime_D_s` と組み合わせて使われる。

## 証明・構築の流れ

1. 0383 の packet API を取り出す。

   ```lean
   have hcop := p.coprime_s_H
   ```

   この時点で

   ```lean
   hcop : Nat.Coprime p.base.snd.natAbs
     (goldenFifthSndFactor p.base.fst p.base.snd).natAbs
   ```

   である。

2. `H_eq` から quartic factor の絶対値を第五冪へ変換する。

   ```lean
   have hHAbs :
       (goldenFifthSndFactor p.base.fst p.base.snd).natAbs = p.D ^ 5 := by
     rw [p.H_eq, Int.natAbs_pow]
     simp
   ```

   `p.H_eq` により `H(r,s)` を `(p.D : ℤ)^5` へ書き換え、`Int.natAbs_pow` で絶対値を冪の外へ出す。最後の `simp` が自然数 `D` の整数 cast の `natAbs` を `D` に簡約する。

3. `hcop` の quartic factor を `D^5` に置換する。

   ```lean
   rw [hHAbs] at hcop
   ```

   よって

   ```lean
   hcop : Nat.Coprime p.base.snd.natAbs (p.D ^ 5)
   ```

   となる。

4. `Nat.coprime_pow_right_iff` で右辺の第五冪を基底へ降ろす。

   ```lean
   (Nat.coprime_pow_right_iff (by decide : 0 < 5)
     p.base.snd.natAbs p.D).mp hcop
   ```

   これで

   ```lean
   Nat.Coprime p.base.snd.natAbs p.D
   ```

   を得る。

5. theorem の goal は引数順が逆なので `.symm` で

   ```lean
   Nat.Coprime p.D p.base.snd.natAbs
   ```

   にする。

## Lean 固有の処理

### `Int.natAbs_pow`

`H_eq` は整数上の等式

```lean
p.H_eq :
  goldenFifthSndFactor p.base.fst p.base.snd = (p.D : ℤ) ^ 5
```

である一方、`coprime_s_H` は `natAbs` を通した自然数上の statement である。その型境界を埋めるために `Int.natAbs_pow` が使われる。

### `simp` による cast 消去

`Int.natAbs_pow` 後には概念的に

```lean
((p.D : ℤ).natAbs) ^ 5
```

が残る。`p.D : ℕ` なので `simp` により `(p.D : ℤ).natAbs = p.D` が処理される。

### `Nat.coprime_pow_right_iff`

今回の証明の中心 API である。指数が正であることを

```lean
(by decide : 0 < 5)
```

で供給し、`Coprime a (b^5)` と `Coprime a b` を同値変換する。

### `.symm`

0383 から継承した orientation は `Coprime |s| D` だが、今回の公開 API は `Coprime D |s|` である。数学的には同じだが、後続 theorem で `D` を左に置く設計に合わせて最後に symmetry を取っている。

## 冗長・重複箇所

大きな冗長性はない。証明は 0383 の結果を fifth root へ一度降ろすだけで、役割が明確である。

ただし `hHAbs` は packet の `H_eq` から何度か必要になり得る派生事実である。後続コードでも同様の `natAbs` 変換が繰り返されるなら、packet namespace に

```lean
theorem H_natAbs_eq (p : GoldenZeroSectorDescentPacket) :
    (goldenFifthSndFactor p.base.fst p.base.snd).natAbs = p.D ^ 5 := ...
```

のような補題を置く余地はある。

一方、この変換が今回しか使われないなら局所 `have` の方が API を増やさず簡潔である。

## 最適化候補

1. **`H_natAbs_eq` の API 化を使用頻度で判断する**

   同じ変換が複数箇所で現れるなら切り出す価値がある。単発なら現状維持が適切である。

2. **orientation は現状が後続に適している**

   0383 は `s` を左に置くが、0384 は `D` を左に置く。これは直後の `Nat.Coprime.pow_left 5 p.coprime_D_s` と自然に接続するため、単なる不統一とは言い切れない。

3. **`by decide : 0 < 5` は十分に安定**

   固定指数なので `norm_num` を呼ぶより軽い。別の named lemma を導入する必要は薄い。

4. **証明本体の polynomial 展開は不要**

   `H_eq` と 0383 を API として使えており、quartic polynomial を再展開しない現在の構成を維持する方がよい。

## 必要 Mathlib import と import 最適化候補

standalone 正本は `import Mathlib` を使用している。

今回の theorem が表面上利用する Mathlib 機能は主として

- `Nat.Coprime`
- `Nat.coprime_pow_right_iff`
- `Int.natAbs`
- `Int.natAbs_pow`
- natural-number cast の simplification
- `decide`

である。

より狭い import へ縮小できる可能性は高いが、この実行では Lean ビルドを行わないため、厳密な最小 Mathlib module 集合は検証していない。したがって具体的な最小 import 名は推測として固定しない。

プロジェクト側では `GoldenZeroSectorDescentPacket`, `coprime_s_H`, `H_eq`, `goldenFifthSndFactor` が見える module dependency が必要である。

## Comparator challenge 化の可否

**可能であり、0383 より少し良い micro challenge になる。**

与える前提を

```lean
hcop : Nat.Coprime sAbs HAbs
hH : HAbs = D ^ 5
```

程度に整理し、目標を

```lean
Nat.Coprime D sAbs
```

とすれば、モデルが

- fifth-power rewrite を行えるか
- `Nat.coprime_pow_right_iff` を発見できるか
- 正の指数条件を供給できるか
- 最後の orientation を `.symm` で合わせられるか

を測定できる。

実コードをそのまま challenge にする場合は `Int.natAbs_pow` と cast simplification も加わり、Nat/Int 境界をまたぐ API 選択能力も評価できる。

ただし数学的難度そのものは低く、Comparator では「既存 API を正しく組み合わせる能力」の評価に向く。

## 次に読むべき宣言

次は 0385 `lift_relPrime_conj`、種別は `theorem` である。

```lean
theorem lift_relPrime_conj (p : GoldenZeroSectorDescentPacket) :
    GoldenRelPrime (goldenZeroSectorLift p.base)
      (goldenConj (goldenZeroSectorLift p.base)) := by
  intro z hzAlpha hzConj
  ...
```

ここでは今回得た

$$
\gcd(D,|s|)=1
$$

と 0382 の

$$
5\nmid D
$$

を組み合わせ、quadratic lift とその conjugate に共通する divisor が unit しかあり得ないことを示す。

0384 までが自然数上の coprimality preparation であり、0385 からその情報を黄金整数環の `GoldenRelPrime` へ持ち上げる段階に入る。