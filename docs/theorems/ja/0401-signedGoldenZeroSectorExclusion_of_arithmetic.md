# 0401 `signedGoldenZeroSectorExclusion_of_arithmetic`

## 宣言種別

`theorem`

0400 `GoldenZeroSectorArithmeticExclusion` で公開された生の zero-sector 算術排除命題を、上流の signed-golden 証明層が要求する `SignedGoldenZeroSectorExclusion` へ変換する receiver bridge である。

この定理自身は新しい数論を証明しない。`SignedGoldenRamifierStrippedPacket` 側ですでに証明済みの norm・積等式・primitive 性・十乗分解を、0400 の引数順に並べて適用することで、zero sector の抽象的な排除インターフェースを構築する。

## Lean コード

```lean
/-- The exact quartic/tenth-power proposition is sufficient for the zero sector. -/
theorem signedGoldenZeroSectorExclusion_of_arithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    SignedGoldenZeroSectorExclusion := by
  intro u v w p gamma hbeta
  exact hArithmetic gamma.fst gamma.snd
    p.exceptional.powerSplit.a p.exceptional.powerSplit.b
    p.exceptional.powerSplit.a_pos p.exceptional.powerSplit.b_pos
    p.exceptional.powerSplit.coprime_a_b p.five_not_dvd_b
    (p.zeroSector_gamma_norm_eq_or_eq_neg hbeta)
    (p.zeroSector_snd_factor_eq hbeta)
    (p.zeroSector_coprime_coords hbeta)
    (p.zeroSector_tenthPower_split hbeta)
```

## Lean の型

宣言の型は

```lean
signedGoldenZeroSectorExclusion_of_arithmetic
    (hArithmetic : GoldenZeroSectorArithmeticExclusion) :
    SignedGoldenZeroSectorExclusion
```

である。

論理的には

$$
\mathrm{GoldenZeroSectorArithmeticExclusion}
\longrightarrow
\mathrm{SignedGoldenZeroSectorExclusion}
$$

という含意である。

0400 の `GoldenZeroSectorArithmeticExclusion` は、整数座標 $r,s$ と自然数 $a,b$ に対し、正値性・互いに素性・5 非可除性・signed norm・quartic product・primitive 座標・十乗 split がすべて成立すれば `False` を返す関数型の命題である。

0401 は、`SignedGoldenZeroSectorExclusion` が受け取る packet と第五冪表示から、それらの raw hypotheses がすべて得られることを示している。

## 数学的主張

`SignedGoldenZeroSectorExclusion` 側から与えられる zero-sector のデータを $(p,\gamma)$ とする。ここで `gamma` は黄金整数の座標

$$
\gamma=(r,s)
$$

を持つ。

packet `p` からは、0400 が必要とする自然数 $a,b$ とその基本条件

$$
a>0,\qquad b>0,
$$

$$
\gcd(a,b)=1,
$$

$$
5\nmid b
$$

がすでに得られる。

さらに zero-sector の第五冪関係 `hbeta` から、次の四つが既存補題として供給される。

1. norm の符号付き同定

$$
N(\gamma)=b
\quad\text{または}\quad
N(\gamma)=-b.
$$

2. 第二座標と quartic factor の積等式

$$
s\,H(r,s)=-5^6a^{10}.
$$

3. 座標の primitive 性

$$
\gcd(|r|,|s|)=1.
$$

4. 十乗分解

ある $c,d\in\mathbb N$ が存在して

$$
|s|=5^6c^{10},
$$

$$
|H(r,s)|=d^{10}.
$$

これらは 0400 `GoldenZeroSectorArithmeticExclusion` の仮定と完全に対応するため、`hArithmetic` を適用すれば直ちに `False` が得られる。

したがって数学的内容は

$$
\text{signed-golden zero-sector packet}
\Longrightarrow
\text{0400 の raw arithmetic hypotheses}
\Longrightarrow
\bot
$$

である。

## 証明全体での役割

0401 は証明アーキテクチャ上の **receiver adapter** である。

0397--0399 では zero-sector の無限降下を具体的な `GoldenZeroSectorCandidate` / `GoldenZeroSectorDescentPacket` に対して閉じた。0400 ではその算術核心を structure 非依存の `Prop` として公開した。

0401 はその公開された arithmetic API を、より上流の signed-golden packet 層へ戻す。

流れは

$$
\text{zero-sector arithmetic}
\xrightarrow{0400}
\texttt{GoldenZeroSectorArithmeticExclusion}
\xrightarrow{0401}
\texttt{SignedGoldenZeroSectorExclusion}
$$

となる。

この境界のおかげで、後続の closure theorem は無限降下の内部実装を一切知らず、`SignedGoldenZeroSectorExclusion` だけを仮定すればよい。

つまり 0401 は「算術証明」と「FLT5 の構造的 closure」を疎結合にする接着層である。

## 直接依存する定義・補題

### 型・定義

- `GoldenZeroSectorArithmeticExclusion`
  - 0400 で定義された raw arithmetic receiver contract。
- `SignedGoldenZeroSectorExclusion`
  - signed-golden zero sector を排除する上流向け interface。
- `GoldenInt`
  - `gamma.fst`, `gamma.snd` の座標を持つ黄金整数表現。

### packet から直接利用する field / theorem

- `p.exceptional.powerSplit.a`
- `p.exceptional.powerSplit.b`
- `p.exceptional.powerSplit.a_pos`
- `p.exceptional.powerSplit.b_pos`
- `p.exceptional.powerSplit.coprime_a_b`
- `p.five_not_dvd_b`

これらが 0400 の $a,b$ と

$$
a>0,\quad b>0,\quad \gcd(a,b)=1,\quad 5\nmid b
$$

を供給する。

### `hbeta` を使う zero-sector 補題

- `p.zeroSector_gamma_norm_eq_or_eq_neg hbeta`
- `p.zeroSector_snd_factor_eq hbeta`
- `p.zeroSector_coprime_coords hbeta`
- `p.zeroSector_tenthPower_split hbeta`

それぞれ 0400 の残り四つの仮定へ直接対応する。

0401 の proof body には算術 tactic は現れず、依存補題の結果を接続するだけである。

## 証明の流れ

Lean コードは短いが、依存の流れは明確である。

1. `hArithmetic : GoldenZeroSectorArithmeticExclusion` を受け取る。
2. `SignedGoldenZeroSectorExclusion` を展開するため

```lean
intro u v w p gamma hbeta
```

で必要なデータを導入する。
3. `gamma.fst`, `gamma.snd` を 0400 の整数座標 `r,s` として渡す。
4. `p.exceptional.powerSplit` から $a,b$ と正値性・coprimality を渡す。
5. `p.five_not_dvd_b` を渡す。
6. `hbeta` から norm の符号付き等式を取り出して渡す。
7. `hbeta` から signed quartic product を渡す。
8. `hbeta` から座標 coprimality を渡す。
9. `hbeta` から十乗 split の existential witness を渡す。
10. 0400 の最終結果 `False` がそのまま `SignedGoldenZeroSectorExclusion` の結論となる。

証明は本質的に一回の curried function application である。

## Lean 固有の処理

### `intro u v w p gamma hbeta`

`SignedGoldenZeroSectorExclusion` は長い関数型の `Prop` なので、`intro` によってその量化変数と仮定を順に導入している。

このうち `u v w` は 0401 の body では直接参照されない。必要な算術情報が packet `p` と `hbeta` にすでに集約されているためである。

### curried application

`hArithmetic` は構造体ではなく関数型の proposition なので、

```lean
exact hArithmetic gamma.fst gamma.snd
  ...
```

と各引数・仮定を順に適用できる。

0400 を `abbrev` とした利点がここで現れており、明示的な `unfold GoldenZeroSectorArithmeticExclusion` は不要である。

### projection chain

```lean
p.exceptional.powerSplit.a
```

のような nested projection は、上流で構築済みの証明 packet から必要な算術 witness を型安全に取り出している。

Lean は各 projection の型を追跡するため、$a,b$ の取り違えや coprimality の対象違いは kernel が拒否する。

### theorem application による型合わせ

```lean
p.zeroSector_gamma_norm_eq_or_eq_neg hbeta
```

などは 0400 が要求する型と一致するため、`simpa`、`rw`、cast 処理なしでそのまま渡せる。

これは前段で interface がよく揃えられていることを示す。

## 冗長・重複箇所

0401 のコード自体には大きな冗長性はない。

ただし、`hArithmetic` への長い位置引数列は、0400 の仮定順と強く結合している。0400 の引数順を変更すると 0401 も更新が必要になる。

また

```lean
p.exceptional.powerSplit.a
p.exceptional.powerSplit.b
p.exceptional.powerSplit.a_pos
p.exceptional.powerSplit.b_pos
p.exceptional.powerSplit.coprime_a_b
```

の repeated projection prefix は視覚的には冗長である。

例えば

```lean
let q := p.exceptional.powerSplit
```

のように局所 alias を置けば短くできるが、現状は各値の provenance が一目で分かる利点がある。短い bridge theorem なので現在形の方が監査には向いている。

## 最適化候補

### 1. 現在の direct adapter を維持

0401 はすでにほぼ最小である。証明を tactic-heavy に書き換える利点はない。

### 2. raw hypothesis bundle の導入

将来 0400 と同じ引数列を複数 receiver が利用するなら、

```lean
structure GoldenZeroSectorArithmeticData where
  r s : ℤ
  a b : ℕ
  ...
```

のような bundle を導入し、

```lean
GoldenZeroSectorArithmeticData → False
```

へ整理する余地はある。

ただし現状では 0400 の `abbrev` が軽量で、0401 も一度の適用だけなので、structure 化は過剰設計になり得る。

### 3. projection alias

`p.exceptional.powerSplit` を局所名にすれば読みやすさは上がる可能性があるが、コード行数は増える。最適化というより style choice である。

### 4. receiver interface の型整合性を維持する

0401 が `simpa` や cast を一切必要としない点は設計上かなり良い。今後 upstream theorem の結論型を変更する場合も、この direct-fit property を維持する価値が高い。

## 必要 Mathlib import と import 最適化候補

standalone 正本は現在

```lean
import Mathlib
```

を使用している。

0401 自身の proof body は

- `intro`
- `exact`
- structure projection
- theorem application

しか使っておらず、0401 単独では特別な Mathlib tactic への直接依存はほぼない。

しかし実際の宣言型は `GoldenZeroSectorArithmeticExclusion`、`SignedGoldenZeroSectorExclusion`、packet 型、黄金整数関連定義を必要とするため、実モジュールではそれらを定義する FLT5 内部モジュールへの import が本質的である。

standalone artifact からは `import Mathlib` より細い厳密な最小 Mathlib import 集合を確定できない。また今回 Lean build は行わないため、最小 import の実機検証もしていない。

最適化するなら、個別 Mathlib namespace を推測して削るより、まず DkMath 側で 0401 の直接 upstream module だけを import し、その transitive imports に任せる方が安全である。

## Comparator challenge 化の可否

**可。ただし単独では易しい challenge になる。**

0401 は proof search より **interface matching** を評価する問題に向いている。

challenge とするなら、以下だけを与える。

```lean
hArithmetic : GoldenZeroSectorArithmeticExclusion
```

および `SignedGoldenZeroSectorExclusion` の goal。

被験モデルには、packet の nested fields と `hbeta` 依存補題を見つけ、0400 の引数順に正確に並べることを要求する。

評価点は

- 適切な projection の発見
- `hbeta` を要求する theorem の選択
- $a,b,r,s$ の対応
- 不要な algebra / cast 処理を挿入しないこと

となる。

より難しくするなら、0400 の `abbrev` を展開した長い型だけを提示し、利用可能 theorem 群から bridge を再構成させるとよい。

一方、数学的発見や非自明な自動証明探索を測る challenge としては弱い。0401 の価値は難しさではなく、証明層間の境界がきれいに設計されている点にある。

## 技術的意味

0401 で重要なのは、新しい等式を証明したことではない。

重要なのは、下流で証明された zero-sector 算術排除が、上流の signed-golden closure が期待する型へ **損失なく変換できる** ことを Lean kernel 上で固定した点である。

つまり

$$
\text{descent arithmetic}
\leftrightarrow
\text{raw receiver assumptions}
\longrightarrow
\text{signed zero-sector exclusion}
$$

の最後の矢印を実装している。

このような薄い adapter theorem は、人間には自明に見える一方、大規模形式化では重要である。証明の各層がどの情報だけを必要としているかを型として明示し、循環依存や暗黙の前提混入を防ぐからである。

## 次に読むべき宣言

次は 0402 `CounterexamplePack.branchB_orientation` を読むべきである。

種別は `theorem`。

```lean
theorem CounterexamplePack.branchB_orientation
    {x y z : ℕ} (p : CounterexamplePack x y z) :
    ¬ 5 ∣ z - y ∨ ¬ 5 ∣ z - x := by
  ...
```

0401 で zero-sector receiver への橋が完成すると、`SignedGoldenClosure` は次に primitive FLT5 packet の二つの gap orientation の少なくとも一方が Branch B 条件を満たすことを示す。

数学的には

$$
5\nmid(z-y)
\quad\text{または}\quad
5\nmid(z-x)
$$

というルーティング補題であり、zero-sector 排除を実際の primitive counterexample elimination へ接続する次の段階である。
