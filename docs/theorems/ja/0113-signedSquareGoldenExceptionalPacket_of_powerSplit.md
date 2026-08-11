# 0113 — `signedSquareGoldenExceptionalPacket_of_powerSplit`

## Lean の型

```lean
noncomputable def signedSquareGoldenExceptionalPacket_of_powerSplit
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    SignedSquareGoldenExceptionalPacket u v w :=
  Classical.choice (nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit s)
```

本宣言は theorem ではなく `noncomputable def` である。0112 `nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit` が証明した

```lean
Nonempty (SignedSquareGoldenExceptionalPacket u v w)
```

から、`Classical.choice` によって具体的な packet を一つ選び、下流から直接利用できる値として公開する。

## 数学的主張

入力は exact signed five-adic power split

```lean
s : SignedFiveAdicPowerSplit u v w
```

である。0112 によって、この `s` に対応する整数座標 $M,N,\delta$ と provenance が存在し、さらに

$$
\operatorname{GoldenNorm}(M,N)=5b^5,
$$

$$
M-2N=5^8a^{10},
$$

$$
M^2-4N^2=\delta^2,
$$

$$
(2M+N)^2-5N^2=20b^5
$$

を満たすことが既に保証されている。ここで $a,b$ は入力 `s` が保持する power-split witness である。

本宣言自身は新しい数学的等式を証明しない。存在が証明済みの `SignedSquareGoldenExceptionalPacket u v w` の witness を一つ選び、その全 field を reusable object として固定する。

## 証明全体での役割

0112 までは「その packet が存在する」という proposition-level の事実だった。本 0113 はその存在証明を、後続の定義・定理が field projection できる object-level API に変換する。

この変換により、下流では毎回

```lean
rcases nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit s with ⟨p⟩
```

と existential witness を取り出す必要がなく、単に

```lean
let p := signedSquareGoldenExceptionalPacket_of_powerSplit s
```

あるいは直接 field projection を用いて、`p.M`, `p.N`, `p.golden_eq`, `p.tenth_boundary` などへアクセスできる。

直後の

```lean
noncomputable def signedSquareGoldenExceptionalPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedSquareGoldenExceptionalPacket u v w :=
  signedSquareGoldenExceptionalPacket_of_powerSplit
    (signedFiveAdicPowerSplit_of_normalForm hNF)
```

は、本 0113 をそのまま再利用して signed normal form から packet への公開変換を作る。したがって 0113 は power-split 層と square-golden exceptional packet 層の public constructor API である。

## 直接依存する定義・補題

直接依存は非常に少ない。

1. `SignedFiveAdicPowerSplit`
   - 入力型。
2. `SignedSquareGoldenExceptionalPacket`
   - 出力型。
3. `nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit`
   - 0112。出力型の inhabitant が存在することを証明する private theorem。
4. `Classical.choice`
   - `Nonempty α` から `α` の値を一つ選ぶ classical choice operator。

数学的に重い依存、たとえば `GN5_eq_goldenNorm_squareLink`、`sumGN5_eq_goldenNorm_signed`、square discriminant、five-discriminant identity などはすべて 0112 の内部へ封じ込められている。本 0113 はそれらへ直接依存しない。

## 証明・定義の流れ

定義本体は一行である。

```lean
Classical.choice
  (nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit s)
```

処理は次の二段階だけである。

1. 0112 を `s` に適用し、

```lean
Nonempty (SignedSquareGoldenExceptionalPacket u v w)
```

を得る。
2. `Classical.choice` でその inhabitant を一つ取り出し、

```lean
SignedSquareGoldenExceptionalPacket u v w
```

として返す。

本宣言では difference / sum の場合分け、cast、`ring`、`simpa` などは一切行わない。それらは 0112 の construction proof に完全に隠蔽されている。

## Lean 固有の処理

### `noncomputable def`

`Classical.choice` による選択は計算可能なアルゴリズムを与えないため、定義には `noncomputable` が必要である。ここで必要なのは実行可能な $M,N,\delta$ の計算器ではなく、証明内で一貫して参照できる witness である。

### `Classical.choice`

`Nonempty α` は「`α` の要素が存在する」という proof-irrelevant な proposition であり、それだけでは field projection 可能な値を返さない。`Classical.choice` はこれを `α` の値へ持ち上げる。

Lean の設計上、この分離は有用である。0112 は構成の正しさを証明する private implementation theorem、0113 は下流が使う短い public object constructor になっている。

### definitional transparency

この定義を unfold すると `Classical.choice (...)` が露出するが、通常 downstream proof は内部 witness の具体的選択方法に依存すべきではない。利用側は `SignedSquareGoldenExceptionalPacket` の field が持つ定理だけを参照するのが安定した設計である。

## 冗長・重複箇所

本体そのものに計算的・論理的な重複はほぼない。一方、architecture としては

```lean
private theorem ... : Nonempty Packet := by ...
noncomputable def ... : Packet := Classical.choice (...)
```

という二段構成を採用しているため、行数だけを見れば直接 `noncomputable def` 内で packet を構築するより宣言数は増える。

しかしこれは意図的な分離と解釈できる。複雑な proof term を private theorem に隔離し、公開側を一行 API に保っているからである。

また、次の `signedSquareGoldenExceptionalPacket_of_normalForm` も同じ出力型を返すが、これは重複 constructor ではなく、入力 interface を `SignedBranchANormalForm` まで一段持ち上げる adapter である。

## 最適化候補

1. 現状維持。
   - 0112 の複雑な構築と 0113 の公開 API が明確に分離されており、可読性が高い。
2. 直接 constructor 版。
   - `noncomputable def` の本体で `by classical ...` として packet を直接構成し、`Nonempty` theorem を削除する案。ただし proof と API が再び混ざる。
3. `choose` tactic / `Classical.choose` 系の記法比較。
   - 表記上の違いだけで本質的な改善は小さい。
4. computable constructor の検討。
   - 0112 の witness が実際には source の場合分けから明示的に構成されているので、classical choice を使わず computable な `def` にできる可能性を検討する価値はある。ただし `SignedFiveAdicPowerSplit` 内の証明 field を消去してデータを組み立てる際の Lean の reducibility / Prop-elimination 制約を確認する必要がある。今回は Lean ビルドを行わないため、これは推測を含む最適化候補として留める。
5. downstream ではこの定義を unfold せず、packet field API のみを使う。
   - choice の実装詳細への依存を避けられる。

## 必要 Mathlib import と import 最適化候補

対象の generated standalone artifact は先頭で

```lean
import Mathlib
```

を使用しているため、本宣言を含む artifact 全体ではこれで十分である。

本 0113 自身が Mathlib から直接必要とする主要機能は `Nonempty` と `Classical.choice` であり、代数 tactic は使わない。したがって standalone 全体の `import Mathlib` は本宣言だけを基準にすれば大幅に過剰である。

ただし実際の元 module `SignedSquareGoldenExceptional.lean` は 0112 の algebraic construction と多数の DkMath 宣言にも依存するため、module 単位の最小 import は本 0113 だけから決められない。Lean ビルドを行わない条件なので、最小 import 集合の断定は避ける。

## Comparator challenge 化の可否

**適している。** 数学的 challenge というより Lean API 設計 challenge として面白い。

比較候補は次のとおり。

1. 現行の `Nonempty` theorem + `Classical.choice` 版。
2. packet を直接返す `noncomputable def` 版。
3. classical choice を使わず、source case split から直接 data を返す computable candidate 版。
4. dependent pair / subtype を intermediate witness として返す版。

評価軸は、

- public API の短さ
- proof implementation の隔離度
- classical dependency の有無
- reduction / unfolding 時の安定性
- downstream error message の局所性
- refactor 時の依存範囲

である。

特に「0112 で witness は明示的に構成しているのに、なぜ 0113 で classical choice を使うのか」は、Lean の `Prop` elimination と API separation を比較する良い教材になる。

## 資料上の位置づけ

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。今回の GitHub connector では PDF 本文の該当ページを直接照合できていないため、ページ番号・節番号は推測で補っていない。

形式的根拠は `Flt5DkMath/FLT5StandAlone.lean` 内の `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` generated section であり、そこでは 0112 の直後に本宣言、その直後に normal-form adapter が置かれている。

## 次に読むべき定理

次は直後の宣言

```lean
noncomputable def signedSquareGoldenExceptionalPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedSquareGoldenExceptionalPacket u v w :=
  signedSquareGoldenExceptionalPacket_of_powerSplit
    (signedFiveAdicPowerSplit_of_normalForm hNF)
```

を読むべきである。

0113 が power split から packet を選び出す public constructor なら、次宣言は `SignedBranchANormalForm` から `SignedFiveAdicPowerSplit` を経由して同じ packet へ到達する composition adapter である。ここを読むと、signed normal form → five-adic power split → square-golden packet という変換パイプラインが一行で可視化される。