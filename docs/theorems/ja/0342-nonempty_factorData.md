# 0342 — `nonempty_factorData`

## 宣言種別

この宣言は **`private theorem`** である。

```lean
private theorem nonempty_factorData (p : GoldenZeroSectorInversionPacket) :
    Nonempty (GoldenZeroSectorFactorData p) := by
  rcases Nat.even_or_odd p.source.c with hc | hc
  · exact nonempty_even_factorData p hc
  · exact nonempty_odd_factorData p hc
```

## Lean の型

本体の型は

```lean
(p : GoldenZeroSectorInversionPacket) →
Nonempty (GoldenZeroSectorFactorData p)
```

である。

`GoldenZeroSectorFactorData p` は inversion packet `p` に依存する dependent inductive 型であり、この定理は追加の parity 仮定なしに、その型が必ず inhabited であることを示す。

返り値が factor datum 自体ではなく `Nonempty (GoldenZeroSectorFactorData p)` であることが重要である。ここでは「どの branch の datum を採用するか」を計算可能な関数として選ばず、存在だけを確立する。直後の `goldenZeroSectorFactorPacket_of_inversion` が `Classical.choice` により実際の datum を一つ選択する。

## 数学的主張

任意の `GoldenZeroSectorInversionPacket` に対し、その source の自然数 `c` は必ず偶数か奇数のどちらかである。

$$
\operatorname{Even}(c)\lor\operatorname{Odd}(c).
$$

既に二つの branch 構築定理が用意されている。

偶数の場合は 0341 `nonempty_even_factorData` により

$$
\operatorname{Nonempty}(\operatorname{GoldenZeroSectorFactorData}(p))
$$

を得る。

奇数の場合は 0338 `nonempty_odd_factorData` により同じ結論を得る。

したがって parity の排中を一度行うだけで、全ての inversion packet に対する exact factor data の存在が得られる。

## 証明全体での役割

この定理は zero-sector factorization の **branch 合流点** である。

0338 は odd-`c` branch を構築し、0341 は even-`c` branch を構築した。それぞれは内部では長い二進付値解析、互いに素性、第五冪分解、factor ownership を扱うが、0342 はそれらを一つの公開可能な存在命題へ畳み込む。

構造としては

$$
\text{odd construction}
\quad\cup\quad
\text{even construction}
\longrightarrow
\text{unconditional factor-data existence}
$$

という位置にある。

この定理自体には新しい数論的内容はほぼなく、前段で完成した二つの証明を parity exhaustion によって接続する制御層である。しかし証明アーキテクチャ上は重要で、後続コードは `p.source.c` の parity を再度意識せず `GoldenZeroSectorFactorData p` の存在だけを利用できる。

## 直接依存する定義・補題

直接依存は非常に少ない。

- `GoldenZeroSectorInversionPacket`
- `GoldenZeroSectorFactorData`
- `nonempty_even_factorData`
- `nonempty_odd_factorData`
- `Nat.even_or_odd`

数学的な重い依存はすべて 0338 と 0341 の内部へ封じ込められている。

特に 0341 は even branch から `.evenLeftLow` または `.evenRightLow` を構築し、0338 は odd branch から `.odd` を構築する。したがって 0342 の結論は三 constructor

```lean
GoldenZeroSectorFactorData.odd
GoldenZeroSectorFactorData.evenLeftLow
GoldenZeroSectorFactorData.evenRightLow
```

のいずれかが存在することを、`c` の parity に応じて保証している。

## 証明の流れ

証明は四行で完結する。

1. `Nat.even_or_odd p.source.c` を適用する。
2. `hc : Even p.source.c` の場合は `nonempty_even_factorData p hc` をそのまま返す。
3. `hc : Odd p.source.c` の場合は `nonempty_odd_factorData p hc` をそのまま返す。
4. 両 branch の codomain が同じ `Nonempty (GoldenZeroSectorFactorData p)` なので、その場で合流する。

Lean コード上の

```lean
rcases Nat.even_or_odd p.source.c with hc | hc
```

は、数学上の「自然数は偶数か奇数」という完全場合分けをそのまま表している。

## Lean 固有の処理

### `Nonempty` による存在の保持

通常の数学なら「factor data が存在する」と述べるだけで済むが、Lean では後で `Classical.choice` を適用するために `Nonempty` という型クラスとは別の proposition-valued wrapper を使って存在を保持している。

```lean
Nonempty (GoldenZeroSectorFactorData p)
```

は existential witness の具体的な field を外部へ露出せず、「型に inhabitant がある」という情報だけを与える。

### dependent codomain の一致

両 branch はどちらも同じ `p` に対する

```lean
GoldenZeroSectorFactorData p
```

を返す。`p` 自体は場合分けされず、場合分けされるのは `p.source.c` の parity proof だけなので、二つの branch の戻り型は definitionally 同じであり、追加の cast や `Eq.ndrec` は不要である。

### `private theorem`

`nonempty_factorData` はこのファイル内部でのみ利用する補助定理として `private` にされている。直後の `goldenZeroSectorFactorPacket_of_inversion` へ存在証明を渡すことが主目的であり、外部 API として名前を公開する必要がない設計である。

## 冗長・重複箇所

この定理そのものには実質的な冗長性はない。

二つの branch が

```lean
· exact nonempty_even_factorData p hc
· exact nonempty_odd_factorData p hc
```

と対称形になっているが、これは parity exhaustion を最も明瞭に示す記述であり、無理に圧縮する利点は小さい。

前段の 0338 / 0341 には多数の構築処理があるが、それらをこの theorem に再展開せず helper theorem として分離している点はむしろ適切である。

## 最適化候補

コード短縮だけなら次のような term-style 記述へ寄せることは可能である。

```lean
private theorem nonempty_factorData (p : GoldenZeroSectorInversionPacket) :
    Nonempty (GoldenZeroSectorFactorData p) := by
  rcases Nat.even_or_odd p.source.c with hc | hc
  · exact nonempty_even_factorData p hc
  · exact nonempty_odd_factorData p hc
```

現行形がすでにほぼ最小なので、実質的な最適化余地はない。

より大きな API 設計としては、0338 と 0341 の戻り値を直接 `GoldenZeroSectorFactorData p` にする案も考えられる。しかし現在は後続で `Classical.choice` を行う設計が明示されており、この変更は証明の計算可能性・非計算性の境界を動かすため、単純な最適化とは言えない。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

この theorem 単体で Mathlib から直接必要なのは主として `Nat.even_or_odd` と `Nonempty` である。ただし実際には `GoldenZeroSectorInversionPacket`、`GoldenZeroSectorFactorData`、`nonempty_even_factorData`、`nonempty_odd_factorData` を定義した前段モジュールへの依存が必要である。

元の ordered source module ではこの宣言は `DkMath/FLT/Five/SignedGoldenZeroSectorFactorization.lean` に属する。standalone は生成物として `import Mathlib` 一つに集約されているため、元モジュールの厳密な最小 Mathlib import 集合は今回 Lean ビルドを行っておらず確認していない。したがって、特定の細分化 import が十分であるという断定はしない。

import 最適化を行うなら、この theorem 単体ではなく `SignedGoldenZeroSectorFactorization.lean` 全体の使用宣言を対象に `Mathlib` umbrella import から必要モジュールを切り出すのが妥当である。

## Comparator challenge 化の可否

**可能である。ただし難度は低い。**

challenge としては次の型だけを与え、0338 と 0341 を利用可能にして証明させる形が自然である。

```lean
example (p : GoldenZeroSectorInversionPacket) :
    Nonempty (GoldenZeroSectorFactorData p) := by
  -- fill here
```

期待解は `Nat.even_or_odd` による場合分けでほぼ一意であり、数論的発見を要求する問題ではない。そのため Comparator では「依存補題を正しく見つけ、二 branch を統合できるか」という proof orchestration の小問として向いている。

より高難度にするなら 0338 / 0341 を直接使用不可にして branch 構築まで再実装させる必要があるが、それは 0342 単体の challenge ではなく factorization 全体の大問になる。

## 次に読むべき宣言

次は

```lean
noncomputable def goldenZeroSectorFactorPacket_of_inversion
    (p : GoldenZeroSectorInversionPacket) : GoldenZeroSectorFactorPacket where
  inversion := p
  factors := Classical.choice (nonempty_factorData p)
```

である。

宣言種別は **`noncomputable def`**。

0342 が証明した `Nonempty (GoldenZeroSectorFactorData p)` から `Classical.choice` により具体的な factor datum を一つ選び、

```lean
GoldenZeroSectorFactorPacket
```

へ格納する。

したがって 0342 が「存在の無条件化」、次宣言が「存在 witness の選択と packet 化」という連続した二段階を形成する。