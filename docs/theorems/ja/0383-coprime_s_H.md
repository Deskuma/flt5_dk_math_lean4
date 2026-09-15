# 0383 `coprime_s_H`

## 宣言種別

`theorem`

`GoldenZeroSectorDescentPacket` namespace 内で、packet の第二座標 `s` と quartic factor `H(r,s)` が互いに素であることを公開する補題である。

## Lean コード

```lean
theorem coprime_s_H (p : GoldenZeroSectorDescentPacket) :
    Nat.Coprime p.base.snd.natAbs
      (goldenFifthSndFactor p.base.fst p.base.snd).natAbs :=
  coprime_natAbs_goldenFifthSndFactor_of_coprime
    p.base.fst p.base.snd p.coprime_coords
```

## Lean の型

namespace を展開すると概念的な型は

```lean
GoldenZeroSectorDescentPacket.coprime_s_H :
  (p : GoldenZeroSectorDescentPacket) →
    Nat.Coprime p.base.snd.natAbs
      (goldenFifthSndFactor p.base.fst p.base.snd).natAbs
```

である。

`p.base : GoldenInt` の座標を

```lean
p.base.fst : ℤ
p.base.snd : ℤ
```

とし、`Nat.Coprime` は自然数上の関係なので、両整数は `Int.natAbs` によって自然数へ移されている。

## 数学的主張

`p.base = (r,s)` と置き、

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s)
$$

と書く。

packet は primitive condition

$$
\gcd(|r|,|s|)=1
$$

を field `coprime_coords` として保持している。

今回の theorem はそこから

$$
\gcd\bigl(|s|,|H(r,s)|\bigr)=1
$$

を得る。

すなわち primitive な二座標 `(r,s)` に対して、見えている第二座標 `s` と fifth-power coordinate polynomial の quartic factor `H(r,s)` の間には、新しい共通素因子が発生しないことを packet API として公開している。

## 証明全体での役割

0381–0382 では 5-adic clean property を

$$
5\nmid H(r,s)
\Longrightarrow
5\nmid D
$$

と fifth root `D` まで伝播させた。

0383 からは coprimality chain に移る。今回の theorem は

$$
\gcd(|r|,|s|)=1
\Longrightarrow
\gcd(|s|,|H(r,s)|)=1
$$

を packet 内部の primitive condition から引き出す。

直後の `coprime_D_s` では packet identity

$$
H(r,s)=D^5
$$

を用いて、この結果から

$$
\gcd(D,|s|)=1
$$

を得る。さらに後続の lift / conjugate coprimality では、`D^5`、`|s|`、5 の間の互いに素性を組み合わせて quadratic lift とその共役の common divisor を排除する。

したがって本 theorem は、元の primitive coordinate condition を fifth-power re-entry 後の factorization に必要な coprimality へ翻訳する橋である。

## 直接依存する定義・補題

直接依存するプロジェクト内宣言は次である。

- `GoldenZeroSectorDescentPacket`
- `GoldenZeroSectorDescentPacket.coprime_coords`
- `GoldenInt.fst`
- `GoldenInt.snd`
- `goldenFifthSndFactor`
- `coprime_natAbs_goldenFifthSndFactor_of_coprime`

直接呼び出している一般補題の型は

```lean
coprime_natAbs_goldenFifthSndFactor_of_coprime
    (r s : ℤ) (hrs : Nat.Coprime r.natAbs s.natAbs) :
    Nat.Coprime s.natAbs (goldenFifthSndFactor r s).natAbs
```

である。

この一般補題は primitive coordinates から `s` と quartic factor の coprimality を導く本体であり、今回の theorem は `r := p.base.fst`, `s := p.base.snd`, `hrs := p.coprime_coords` と特殊化している。

0380 `H_pos`、0381 `five_not_dvd_H`、0382 `five_not_dvd_D` には直接依存しない。証明項そのものは `coprime_coords` と一般補題だけで閉じている。

## 証明・構築の流れ

証明は tactic block を持たない term-style proof で一段だけである。

1. packet から座標を取り出す。

   ```lean
   p.base.fst
   p.base.snd
   ```

2. packet の primitive invariant を取り出す。

   ```lean
   p.coprime_coords
   ```

   その型は

   ```lean
   Nat.Coprime p.base.fst.natAbs p.base.snd.natAbs
   ```

   である。

3. 一般補題へそのまま渡す。

   ```lean
   coprime_natAbs_goldenFifthSndFactor_of_coprime
     p.base.fst p.base.snd p.coprime_coords
   ```

4. 一般補題の結論が今回の goal と definitional に一致するため、その証明項がそのまま theorem の本体になる。

数学的な重い部分は一般補題側ですでに処理されており、0383 は descent packet に適した名前付き projection / specialization API を与えている。

## 一般補題側で行われる数学

正本の `coprime_natAbs_goldenFifthSndFactor_of_coprime` は、primitive condition を仮定し、もし `|s|` と `|H(r,s)|` が互いに素でなければ共通素因子 `q` を取る、という contradiction proof を採用している。

冒頭は概略

```lean
by_contra hcop
rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
  ⟨q, hqPrime, hqs, hqH⟩
```

となっており、共通素因子 `q` を抽出した後、`Int.natCast_dvd.mpr` により整数座標の可除性へ戻して quartic polynomial の合同関係を利用する。その結果 `q` が `r` にも入ることを導き、元の

$$
\gcd(|r|,|s|)=1
$$

と矛盾させる構造である。

したがって今回の一行 proof が短いのは数学が弱いからではなく、必要な polynomial divisibility argument がすでに reusable lemma として抽象化されているためである。

## Lean 固有の処理

### term-style proof

今回の theorem には

```lean
:= by
```

がなく、右辺に既存 theorem の適用結果を直接置いている。

Lean が引数から戻り値の型を計算すると、今回の goal と完全に一致するため追加 rewrite は不要である。

### structure projection

```lean
p.base.fst
p.base.snd
p.coprime_coords
```

はすべて structure field projection である。

特に `p.coprime_coords` は `GoldenZeroSectorDescentPacket` の構築時に保存された invariant を、後続 theorem が再証明せず利用する設計になっている。

### `Int.natAbs`

`Nat.Coprime` の対象を自然数に統一するため、整数座標には `natAbs` が使われる。

これにより符号に依存せず

$$
\gcd(|r|,|s|)=1
$$

および

$$
\gcd(|s|,|H(r,s)|)=1
$$

を扱える。

## 冗長・重複箇所

コード上は一行の specialization なので、局所的な冗長性はほぼない。

一見すると一般補題を直接呼べばよく `coprime_s_H` は不要にも見える。しかし descent 本体の可読性という観点では、この named theorem は有用である。

後続コードが毎回

```lean
coprime_natAbs_goldenFifthSndFactor_of_coprime
  p.base.fst p.base.snd p.coprime_coords
```

と書くより

```lean
p.coprime_s_H
```

と書ける方が、数学的意味が明確で packet abstraction も保たれる。

したがってこの重複は API layer として意図的・合理的である。

## 最適化候補

1. **現状維持を推奨**

   一般補題と packet-specific corollary の分離が明快で、証明も最小である。

2. **`@[simp]` 化は不要**

   `Nat.Coprime ...` は rewrite 用等式ではないので、simp lemma とする利益は小さい。

3. **命名の明示性**

   namespace 内なので `coprime_s_H` は短く読みやすい。一方、namespace 外で頻繁に参照する場合は `GoldenZeroSectorDescentPacket.coprime_s_H` が十分に文脈を補うため、長い名前への変更は不要である。

4. **一般補題の再利用維持**

   packet theorem 側へ一般補題の contradiction proof をコピーしないことが重要である。現在の設計は polynomial arithmetic の証明を一箇所へ集約できており、保守性が高い。

## 必要 Mathlib import と import 最適化候補

standalone 正本は `import Mathlib` を使用している。

この theorem 自体で表面上必要なのは概ね次の要素である。

- `Nat.Coprime`
- `Int.natAbs`
- structure projection と theorem application という Lean core の基本機能

今回の theorem 本体自身は tactic を一つも使わず、`ring`, `norm_num`, `omega`, `exact_mod_cast` などにも直接依存しない。

ただし直接呼び出す `coprime_natAbs_goldenFifthSndFactor_of_coprime` の定義元では prime / divisibility / integer cast の API が必要であり、プロジェクト module としての最小 import はその依存も含めて決める必要がある。

Lean ビルドを行わない条件のため、厳密な最小 Mathlib module 集合は確認していない。したがって具体的 module 名の断定は避ける。

## Comparator challenge 化の可否

**可能。ただし theorem 自体は非常に易しいため、二種類の challenge が考えられる。**

### API 選択 challenge

`GoldenZeroSectorDescentPacket` と一般補題を与え、今回の theorem を一行で再構成させる。

評価対象は

- structure projection の選択
- 既存一般補題の発見
- 不要な polynomial 展開を避けられるか

である。

これは「証明検索・再利用能力」を測る小規模 Comparator challenge に向く。

### 数学本体 challenge

より歯応えを持たせるなら一般補題

```lean
coprime_natAbs_goldenFifthSndFactor_of_coprime
```

自体を challenge 化する方がよい。

その場合は

- 非 coprime から共通素因子を抽出
- `Nat` divisibility を `Int` へ移送
- quartic factor の形から `q ∣ r^4` を導出
- prime divisibility から `q ∣ r`
- primitive coordinates と矛盾

という divisibility pipeline が課題の中心になる。

0383 単体は API-composition challenge、一般補題は substantive arithmetic challenge として分離するのが適切である。

## 次に読むべき宣言

次は 0384 `coprime_D_s`、種別は `theorem` である。

```lean
theorem coprime_D_s (p : GoldenZeroSectorDescentPacket) :
    Nat.Coprime p.D p.base.snd.natAbs := by
  have hcop := p.coprime_s_H
  have hHAbs :
      (goldenFifthSndFactor p.base.fst p.base.snd).natAbs = p.D ^ 5 := by
    rw [p.H_eq, Int.natAbs_pow]
    simp
  ...
```

0383 が

$$
\gcd(|s|,|H(r,s)|)=1
$$

を確立したのに対し、0384 は

$$
H(r,s)=D^5
$$

を使って fifth root まで coprimality を降ろし、

$$
\gcd(D,|s|)=1
$$

を得る段階である。