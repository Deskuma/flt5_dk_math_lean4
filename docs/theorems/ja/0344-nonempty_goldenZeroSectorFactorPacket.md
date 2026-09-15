# 0344 — `nonempty_goldenZeroSectorFactorPacket`

## 宣言種別

この宣言は **`theorem`** である。

```lean
/-- Every raw zero-sector candidate produces one of the three exact factor branches. -/
theorem nonempty_goldenZeroSectorFactorPacket
    (p : GoldenZeroSectorCandidate) :
    Nonempty GoldenZeroSectorFactorPacket :=
  ⟨goldenZeroSectorFactorPacket_of_inversion
    (goldenZeroSectorInversionPacket p)⟩
```

## Lean の型

本体の型は

```lean
GoldenZeroSectorCandidate → Nonempty GoldenZeroSectorFactorPacket
```

である。

すなわち任意の raw zero-sector candidate

```lean
p : GoldenZeroSectorCandidate
```

から、完全な exact factor packet が少なくとも一つ存在することを返す。

返り値は packet 自体ではなく

```lean
Nonempty GoldenZeroSectorFactorPacket
```

であり、命題レベルで factor packet の inhabitance を保証する。

## 数学的意味

この定理は、zero-sector の元データが与えられれば、それに対応する exact factorization branch が必ず構成できることを述べる。

概念的には

$$
\text{raw zero-sector candidate}
\longrightarrow
\text{inversion packet}
\longrightarrow
\text{exact factor packet}.
$$

0343 `goldenZeroSectorFactorPacket_of_inversion` は inversion packet から具体的な factor packet を一つ選べることを既に与えている。本定理はその入力をさらに一段前へ戻し、raw candidate `p` から

```lean
goldenZeroSectorInversionPacket p
```

を作って 0343 に渡す。

したがって新しい数論計算を行う定理ではなく、これまでに証明済みの zero-sector inversion と factorization を公開 API として接続する bridge theorem である。

## 証明全体での役割

この定理は signed golden zero-sector factorization 層の **公開存在定理** にあたる。

前段では、

1. raw candidate から inversion packet を構築し、
2. `c` の parity に応じて exact factor data の存在を証明し、
3. `Classical.choice` により factor packet を一つ選んだ。

0344 はこれらを一つの入口へまとめ、後続が raw candidate から factor packet の存在を直接利用できるようにする。

特に直後には

```lean
abbrev GoldenZeroSectorFactorExclusion : Prop :=
  GoldenZeroSectorFactorPacket → False
```

が定義される。その後の exclusion 層では、「raw candidate をどう factor packet に変換するか」という内部工程を再実装せず、今回までに確立した packet pipeline を使えばよい。

つまり証明構造としては

$$
\text{raw candidate}
\to
\text{certified inversion}
\to
\text{certified exact factorization}
\to
\text{branch exclusion}
\to
\bot
$$

の中央接続点である。

## 直接依存する定義・補題

直接依存は次の三つである。

- `GoldenZeroSectorCandidate`
- `goldenZeroSectorInversionPacket`
- 0343 `goldenZeroSectorFactorPacket_of_inversion`

返り値の型として

- `GoldenZeroSectorFactorPacket`
- `Nonempty`

も直接現れる。

0343 の内部では 0342 `nonempty_factorData` と `Classical.choice` が用いられるが、本定理自身はそれらを直接呼ばない。

この分離により、0344 は factor data の odd/even 分岐や第五冪分解の詳細を知らず、完成済み API の合成だけを行っている。

## 証明の流れ

証明は一行の constructor で完結する。

```lean
⟨goldenZeroSectorFactorPacket_of_inversion
  (goldenZeroSectorInversionPacket p)⟩
```

展開すると次の二段階である。

1. `p : GoldenZeroSectorCandidate` から

   ```lean
   goldenZeroSectorInversionPacket p : GoldenZeroSectorInversionPacket
   ```

   を得る。

2. その inversion packet を 0343 に渡し、

   ```lean
   goldenZeroSectorFactorPacket_of_inversion
     (goldenZeroSectorInversionPacket p)
     : GoldenZeroSectorFactorPacket
   ```

   を得る。

3. 得られた packet を `Nonempty` の唯一の constructor で包む。

数学的には単なる関数合成と存在型への封入であり、分岐解析や算術 tactic は不要である。

## Lean 固有の処理

### `Nonempty` constructor

Lean の

```lean
Nonempty α
```

は proposition-valued な「`α` の inhabitant が存在する」という型である。

今回は 0343 が既に concrete value

```lean
GoldenZeroSectorFactorPacket
```

を返すので、

```lean
⟨ ... ⟩
```

でその値を `Nonempty` に包むだけでよい。

### implicit composition

Lean は

```lean
goldenZeroSectorInversionPacket p
```

の返り値型を 0343 の引数型としてそのまま受理するため、中間変数、型注釈、cast は不要である。

### theorem なのに計算可能 witness を持つ点

返り値は proposition だが、証明項の内部には 0343 が構築した具体的 packet がそのまま入っている。

ただし 0343 自体が `noncomputable def` であり `Classical.choice` を用いるため、この証明から実行可能な factorization algorithm が得られると解釈してはならない。

## 冗長・重複箇所

この theorem に局所的な冗長性はほぼない。

例えば

```lean
let inv := goldenZeroSectorInversionPacket p
let packet := goldenZeroSectorFactorPacket_of_inversion inv
exact ⟨packet⟩
```

と書くこともできるが、現行の一行版より長くなる。

また

```lean
by
  exact ⟨...⟩
```

と tactic block にする必要もなく、term-style proof が最も自然である。

## 最適化候補

局所的なコード最適化余地はほぼない。

設計上は、0343 が既に

```lean
GoldenZeroSectorInversionPacket → GoldenZeroSectorFactorPacket
```

を返すため、raw candidate から factor packet を直接返す

```lean
noncomputable def goldenZeroSectorFactorPacket
    (p : GoldenZeroSectorCandidate) : GoldenZeroSectorFactorPacket := ...
```

を定義する案はある。

しかし現行 theorem は `Nonempty` を公開 contract として保っており、後続の「存在すれば矛盾」という論理構造と整合する。また inversion packet を明示的な中間 API として残すことで証明層の責務も分離されている。

したがって短縮のためだけに統合する必然性はない。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

この theorem 単体で Mathlib から直接必要なものは本質的に

- `Nonempty`
- structure / theorem application の Lean 基盤

程度であり、算術 tactic や高度な Mathlib 定理を直接使用しない。

一方、依存する `goldenZeroSectorInversionPacket` と `goldenZeroSectorFactorPacket_of_inversion` の成立には前段の多数の FLT5 宣言が必要である。

そのため import 最適化を行うなら、本 theorem 単体より `SignedGoldenZeroSectorFactorization.lean` とその直前の `SignedGoldenZeroSectorInversion.lean` の module boundary を単位として監査するのが自然である。

具体的な最小 Mathlib import 名は Lean ビルドを行っていないため未確認であり、ここでは断定しない。

## Comparator challenge 化の可否

**可能であり、初級の API composition 問題として適している。**

例えば次の goal を与える。

```lean
theorem challenge
    (p : GoldenZeroSectorCandidate) :
    Nonempty GoldenZeroSectorFactorPacket := by
  -- fill here
```

利用可能な宣言として

```lean
goldenZeroSectorInversionPacket
  : GoldenZeroSectorCandidate → GoldenZeroSectorInversionPacket

goldenZeroSectorFactorPacket_of_inversion
  : GoldenZeroSectorInversionPacket → GoldenZeroSectorFactorPacket
```

を提示すれば、解答者は二つの API を合成し、結果を `Nonempty` に包めばよい。

数学的難度は低いが、長い形式化の中で「重い内部証明を公開 theorem へ接続する」Lean 的な設計を学ぶ小問として価値がある。

## 次に読むべき宣言

次は

```lean
/-- Exclusion of every certified exact factor branch. -/
abbrev GoldenZeroSectorFactorExclusion : Prop :=
  GoldenZeroSectorFactorPacket → False
```

である。

宣言種別は **`abbrev`**。

これは exact factor packet を一つ受け取れば矛盾を導ける、という後続 exclusion 層の contract を名前付きで定義する。

0344 が raw candidate から factor packet の存在までを保証したため、次段階ではその packet をすべて排除する命題

$$
\operatorname{GoldenZeroSectorFactorPacket}\to\bot
$$

を証明できれば zero-sector 全体を閉じられる、という証明インターフェースへ進む。
