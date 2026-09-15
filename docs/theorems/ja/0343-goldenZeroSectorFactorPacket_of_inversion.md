# 0343 — `goldenZeroSectorFactorPacket_of_inversion`

## 宣言種別

この宣言は **`noncomputable def`** である。

```lean
/-- Chosen exact factor packet attached to an inversion packet. -/
noncomputable def goldenZeroSectorFactorPacket_of_inversion
    (p : GoldenZeroSectorInversionPacket) : GoldenZeroSectorFactorPacket where
  inversion := p
  factors := Classical.choice (nonempty_factorData p)
```

## Lean の型

本体の型は

```lean
GoldenZeroSectorInversionPacket → GoldenZeroSectorFactorPacket
```

である。

より具体的には、任意の

```lean
p : GoldenZeroSectorInversionPacket
```

を受け取り、

```lean
GoldenZeroSectorFactorPacket
```

を一つ返す。

`GoldenZeroSectorFactorPacket` は直前に定義された dependent structure であり、

```lean
structure GoldenZeroSectorFactorPacket : Type where
  inversion : GoldenZeroSectorInversionPacket
  factors : GoldenZeroSectorFactorData inversion
```

という形を持つ。したがって返される packet の `factors` は、同じ packet の `inversion` field に型レベルで結び付けられている。

この定義では

```lean
inversion := p
```

とするため、第二 field の要求型は definitionally

```lean
GoldenZeroSectorFactorData p
```

となる。0342 `nonempty_factorData p` がこの型の inhabitant の存在を与え、`Classical.choice` がその witness を一つ選ぶ。

## 数学的意味

0342 までで既に、任意の inversion packet `p` に対して exact factor data が少なくとも一つ存在することが証明されている。

$$
\operatorname{Nonempty}(\operatorname{GoldenZeroSectorFactorData}(p)).
$$

0343 は、その存在証明から具体的な factor datum を一つ選び、元の inversion packet と組にして完全な factor packet を作る。

概念的には

$$
p
\longmapsto
\bigl(p,\;\operatorname{choose}(\text{factor data for }p)\bigr).
$$

数学的な新しい数論命題を証明しているわけではない。ここで行われているのは、既に証明済みの存在を後続の構造化 API で使える具体的 object に変換することである。

重要なのは、選ばれる factor datum が三 branch

```lean
GoldenZeroSectorFactorData.odd
GoldenZeroSectorFactorData.evenLeftLow
GoldenZeroSectorFactorData.evenRightLow
```

のどれであるかをこの定義自身は指定しない点である。0342 が parity に応じて存在を保証し、その存在証明から `Classical.choice` が一つを取得する。

## 証明全体での役割

この定義は zero-sector factorization の **存在証明層と packet API 層の境界** に位置する。

前段の流れは次のようになっている。

$$
\text{inversion packet}
\to
\text{odd/even analysis}
\to
\operatorname{Nonempty}(\text{factor data}).
$$

0343 はそこから

$$
\operatorname{Nonempty}(\text{factor data})
\to
\text{chosen factor data}
\to
\text{complete factor packet}
$$

へ移す。

この packet 化によって、後続定理は `Nonempty` を逐一開いたり `c` の parity を再分析したりせず、単に

```lean
packet : GoldenZeroSectorFactorPacket
```

を受け取ればよくなる。

直後の 0344 `nonempty_goldenZeroSectorFactorPacket` は raw zero-sector candidate から inversion packet を作り、この定義を適用して factor packet の存在を得る。そのさらに後では `GoldenZeroSectorFactorExclusion` が

```lean
GoldenZeroSectorFactorPacket → False
```

として定義され、factor packet が zero-sector exclusion の直接入力になる。

したがって 0343 は、長い factorization の内部証明を一つの witness-carrying object に封じ込め、後続 descent / exclusion 層へ渡す接続点である。

## 直接依存する定義・補題

直接依存は次の通りである。

- `GoldenZeroSectorInversionPacket`
- `GoldenZeroSectorFactorPacket`
- `GoldenZeroSectorFactorData`
- 0342 `nonempty_factorData`
- `Classical.choice`

特に直接の数論依存は 0342 の内部へ完全に隠蔽されている。

0342 自体は

- 0338 `nonempty_odd_factorData`
- 0341 `nonempty_even_factorData`
- `Nat.even_or_odd`

を使って factor datum の存在を確立していた。したがって 0343 は、それらの odd/even factorization 詳細を知らずに witness だけを消費する。

## 構築の流れ

構築は structure literal の二 field だけで完結する。

1. 入力 `p : GoldenZeroSectorInversionPacket` を受け取る。
2. `GoldenZeroSectorFactorPacket.inversion` にそのまま `p` を格納する。
3. 0342 `nonempty_factorData p` により

   ```lean
   Nonempty (GoldenZeroSectorFactorData p)
   ```

   を得る。
4. `Classical.choice` により

   ```lean
   GoldenZeroSectorFactorData p
   ```

   の witness を一つ選ぶ。
5. その witness を `factors` field に格納する。

Lean コードではこの全過程が

```lean
where
  inversion := p
  factors := Classical.choice (nonempty_factorData p)
```

の二行へ圧縮されている。

## Lean 固有の処理

### `noncomputable def`

この定義が `noncomputable` である理由は `Classical.choice` を使うためである。

`nonempty_factorData p` は

```lean
Nonempty (GoldenZeroSectorFactorData p)
```

を返すだけであり、計算によって branch と witness を返す関数ではない。その proposition-level な存在から inhabitant を取り出すため classical choice を使う。

したがって、この定義には実行可能な branch-selection algorithm が与えられているわけではない。

### dependent structure field

`GoldenZeroSectorFactorPacket` の第二 field は

```lean
factors : GoldenZeroSectorFactorData inversion
```

であり、第一 field `inversion` に依存する。

structure literal で先に

```lean
inversion := p
```

を指定すると、Lean は `factors` の期待型を自動的に

```lean
GoldenZeroSectorFactorData p
```

へ具体化する。そのため cast や equality transport は不要である。

### `Classical.choice` と `Nonempty`

Lean の `Classical.choice` は `Nonempty α` から `α` を返す。この定義では

```lean
α := GoldenZeroSectorFactorData p
```

である。

0342 を `∃ data, ...` の形ではなく `Nonempty (GoldenZeroSectorFactorData p)` として用意していたことが、ここで直接活きている。

## 冗長・重複箇所

この定義にはほぼ冗長性がない。

```lean
inversion := p
factors := Classical.choice (nonempty_factorData p)
```

は、必要な二 field を最短距離で埋めている。

代替として局所変数

```lean
let factors := Classical.choice (nonempty_factorData p)
```

を置いてから structure を構築することもできるが、現行形より長くなるだけである。

また `⟨p, Classical.choice ...⟩` という positional constructor 表記も可能なはずだが、field 名を明示する現行形の方が dependent field の意味を読み取りやすい。

## 最適化候補

局所的なコード最適化余地はほとんどない。

より大きな設計上の候補としては、0338 / 0341 / 0342 の段階で `GoldenZeroSectorFactorData p` を直接返す計算可能または非計算可能な関数を定義し、0343 での `Classical.choice` を不要にする案がある。

しかし現行設計は

1. 数学的存在を proposition-valued `Nonempty` として証明する層
2. classical choice によって object を選ぶ層

を明確に分離している。この分離は、どこから非計算性が入るかを一箇所に局在化できる利点がある。そのため単純な「最適化」として統合すべきとは言えない。

別の候補は、後続が factor packet の具体 witness ではなく存在だけで十分なら `Nonempty GoldenZeroSectorFactorPacket` を直接運ぶことである。ただし実際の後続 `GoldenZeroSectorFactorExclusion` は packet 自体を入力に取るため、現在の chosen packet API には明確な用途がある。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

0343 単体で Mathlib から直接必要になる主要要素は

- `Nonempty`
- `Classical.choice`
- `noncomputable` を許す classical choice 周辺の基盤

である。

ただし宣言が依存する `GoldenZeroSectorInversionPacket`、`GoldenZeroSectorFactorPacket`、`nonempty_factorData` は `DkMath/FLT/Five/SignedGoldenZeroSectorFactorization.lean` 内の前段宣言であるため、実際の source module の import はそれらを成立させる広い依存を含む。

standalone の ordered source list でも `DkMath/FLT/Five/SignedGoldenZeroSectorFactorization.lean` が `SignedGoldenZeroSectorInversion.lean` の後に配置されている。

この定義だけを孤立させた最小 Mathlib import は非常に小さくできる可能性が高いが、今回は Lean ビルドを行っていないため、具体的な細分化 import 名が十分であるとは断定しない。

import 最適化を実施するなら、0343 単体ではなく `SignedGoldenZeroSectorFactorization.lean` 全体を対象に umbrella `Mathlib` 依存を監査するのが妥当である。

## Comparator challenge 化の可否

**可能であり、Lean の dependent structure と classical choice を確認する小問として適している。**

例えば次を与える。

```lean
noncomputable def challenge
    (p : GoldenZeroSectorInversionPacket) : GoldenZeroSectorFactorPacket := by
  -- fill here
```

利用可能な補題として

```lean
nonempty_factorData p : Nonempty (GoldenZeroSectorFactorData p)
```

を与えれば、解答者は

- `GoldenZeroSectorFactorPacket` の dependent field を理解する
- `Classical.choice` で `Nonempty` から witness を取り出す
- `inversion := p` と同じ `p` に対応する factor datum を格納する

必要がある。

数学難度は低いが、Lean の「存在証明と concrete data の境界」を学ぶ challenge として価値がある。

難度を上げるなら `nonempty_factorData` を直接与えず、0342 の parity split まで再構築させることもできる。ただしそれは 0342 と 0343 の複合問題になる。

## 次に読むべき宣言

次は

```lean
/-- Every raw zero-sector candidate produces one of the three exact factor branches. -/
theorem nonempty_goldenZeroSectorFactorPacket
    (p : GoldenZeroSectorCandidate) :
    Nonempty GoldenZeroSectorFactorPacket :=
  ⟨goldenZeroSectorFactorPacket_of_inversion
    (goldenZeroSectorInversionPacket p)⟩
```

である。

宣言種別は **`theorem`**。

0343 が inversion packet から chosen factor packet を構築できるようにしたため、0344 は raw `GoldenZeroSectorCandidate` をまず

```lean
goldenZeroSectorInversionPacket p
```

で inversion packet に変換し、0343 を適用して `GoldenZeroSectorFactorPacket` の存在を示す。

したがって次の段階では

$$
\text{raw candidate}
\to
\text{inversion packet}
\to
\text{chosen factor packet}
\to
\operatorname{Nonempty}(\text{factor packet})
$$

という factorization pipeline の公開存在定理を読むことになる。
