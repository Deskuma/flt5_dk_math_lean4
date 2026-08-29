# 0271 — `SignedGoldenUnitFifthPowerExclusion`

## 宣言種別

これは `theorem` ではなく **`abbrev`** である。

正本 Lean source では、unit sector arithmetic が最終的に供給すべき「再利用可能な排除命題」を `Prop` の省略名として固定している。

## Lean の型

```lean
/--
The reusable packet exclusion produced by the sector arithmetic: no packet's
`beta` can be a unit times a fifth power.
-/
abbrev SignedGoldenUnitFifthPowerExclusion : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    (epsilon gamma : GoldenInt),
    GoldenUnit epsilon →
    p.beta = goldenMul epsilon (goldenPow gamma 5) →
    False
```

型を論理式として読むと、任意の自然数パラメータ `u v w`、任意の ramifier-stripped packet `p`、任意の黄金整数 `epsilon` と `gamma` に対し、

1. `epsilon` が `GoldenUnit` であり、
2. `p.beta` が `epsilon * gamma^5` と表される

なら矛盾 `False` が従う、という命題である。

数学的には

$$
\epsilon\in\mathcal O^\times,
\qquad
\beta=\epsilon\gamma^5
\quad\Longrightarrow\quad
\bot
$$

という「packet の $\beta$ は unit times fifth power ではありえない」という排除契約を表す。

## 数学的主張または宣言の意味

`GoldenInt` を黄金整数環の座標モデルと見ると、`GoldenUnit epsilon` は `epsilon` が二-sided inverse を持つ unit であることを表す。

したがって `SignedGoldenUnitFifthPowerExclusion` は、`SignedGoldenRamifierStrippedPacket` から得られる特殊な元 `beta` が

$$
\beta=\epsilon\gamma^5
$$

という形を取る可能性を、**すべての unit $\epsilon$ とすべての $\gamma$ に対して一括して排除する命題** である。

ここで重要なのは、この宣言自身はその排除を証明していないことである。`abbrev` は「この形の命題を今後この名前で呼ぶ」と定めるだけであり、実際の証明項は後続 theorem が供給する。

この設計により、後段は sector ごとの算術証明の内部を知らずに、単に

```lean
hExclude : SignedGoldenUnitFifthPowerExclusion
```

という一つの仮定または証明済み値を受け取ればよくなる。

## 証明全体での役割

直前の 0264–0268 は、代表 unit sector

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

について `gamma^5 = A + Bφ` としたときの第二座標を

$$
B,\quad A+B,\quad A+2B,\quad 2A+3B,\quad 3A+5B
$$

へ具体化した。

0269 `golden_neg_unit_mul_fifth_snd` は負の unit representative を符号反転へ還元し、0270 `SignedGoldenRamifierStrippedPacket.unitSector_snd_eq` は packet が保存している exact five-adic coordinate

$$
\operatorname{snd}(\beta)=-5^7a^{10}
$$

を finite sector 表現へ搬送した。

0271 は、これらの計算を後段へ渡すための **公開インターフェースの型** を定める位置にある。

つまり証明の層は概念的に、

$$
\text{sector coordinate arithmetic}
\longrightarrow
\text{all unit sectors are impossible}
\longrightarrow
\texttt{SignedGoldenUnitFifthPowerExclusion}
$$

と圧縮される。

後続 theorem `signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector` は、unit の mod-fifth class 分類と zero-sector 排除を組み合わせ、この `Prop` の実際の inhabitant、すなわち証明を構築する。

したがって 0271 は新たな数論計算を追加する宣言ではなく、**長い sector elimination を一つの reusable theorem contract に畳み込む境界** である。

## 直接依存する定義・補題

`abbrev` の右辺に直接現れる依存対象は次の通りである。

### `SignedGoldenRamifierStrippedPacket`

```lean
structure SignedGoldenRamifierStrippedPacket (u v w : ℕ) : Type where
  ...
  beta : GoldenInt
  ...
```

exceptional branch から ramifier を一度除去した packet であり、本宣言ではその field `p.beta` を対象とする。

### `GoldenInt`

黄金整数 $a+b\varphi$ を表す project-side の座標型である。`epsilon` と `gamma` はともにこの型を持つ。

### `GoldenUnit`

正本では次の two-sided inverse predicate として定義されている。

```lean
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧
    goldenMul eta epsilon = goldenOne
```

したがって本宣言は Mathlib の抽象的な `IsUnit` を型に直接置くのではなく、project-side の具体的 unit predicate を入口とする。

### `goldenMul`

`GoldenInt` 上の project-side 乗法 API であり、

```lean
p.beta = goldenMul epsilon (goldenPow gamma 5)
```

の積を形成する。

### `goldenPow`

`GoldenInt` 上の自然数冪 API である。本宣言では指数を `5` に固定し、`gamma^5` を表す。

### `False`

結論はデータではなく矛盾である。したがってこの `Prop` の inhabitant は「そのような representation は存在しない」ことを示す eliminator として利用できる。

なお、0264–0270 の個々の theorem 名はこの `abbrev` の型そのものには現れない。それらは、この契約を後続で **証明するための内部実装** 側に属する。

## 証明または構築の流れ

本宣言には `:= by ...` の proof script は存在しない。

```lean
abbrev SignedGoldenUnitFifthPowerExclusion : Prop :=
  ...
```

は右辺の proposition に名前を付けるだけである。

したがって「構築の流れ」は次のように読むのが正確である。

1. 任意の `u v w : ℕ` を暗黙引数として量化する。
2. 対応する packet `p` を取る。
3. 任意の `epsilon gamma : GoldenInt` を取る。
4. `epsilon` が unit であるという仮定を受け取る。
5. `p.beta = epsilon * gamma^5` という representation hypothesis を受け取る。
6. その二仮定から `False` を返す関数型を要求する。

Lean の Curry–Howard 対応では、この `Prop` の証明は概略

```lean
fun p epsilon gamma hepsilon hbeta =>
  -- derive False
```

という関数になる。

後続 theorem がまさにこの形で `intro` を行い、有限 unit sector へ分類して contradiction を構築する。

## Lean 固有の処理

### `abbrev` と definitional transparency

`abbrev` は通常の opaque theorem 名ではなく、右辺への軽量な省略名として扱われる。したがって Lean は必要に応じて

```lean
SignedGoldenUnitFifthPowerExclusion
```

をその全称量化された implication chain へ展開できる。

このため後続 theorem では、結論がこの名前で書かれていても、

```lean
intro u v w p epsilon gamma hepsilon hbeta
```

のように直接 introduction を開始できる。

### 暗黙量化と明示量化

```lean
∀ {u v w : ℕ} (p : ...) (epsilon gamma : GoldenInt), ...
```

では `u v w` だけが `{...}` により implicit、`p epsilon gamma` は explicit である。

これは packet の型から `u v w` を推論させつつ、排除対象の packet・unit・fifth-power base は呼び出し側が明示的に与えられる API になっている。

### implication chain

```lean
GoldenUnit epsilon →
p.beta = ... →
False
```

は proposition-level の二段関数である。存在量化

```lean
¬ ∃ epsilon gamma, ...
```

として定義することも数学的には可能だが、現在の curried form は後続で得られた具体的 `epsilon`, `gamma`, `hepsilon`, `hbeta` をそのまま適用しやすい。

## 冗長・重複箇所

宣言本体は短く、内部的な冗長性はほぼない。

数学的には

```lean
∀ ...,
  GoldenUnit epsilon →
  p.beta = ... →
  False
```

は

```lean
¬ ∃ epsilon gamma,
  GoldenUnit epsilon ∧
  p.beta = ...
```

に近い内容を持つ。しかし現在の形には、

- witness をいったん existential package に詰め直す必要がない
- downstream で具体的な `epsilon`, `gamma` に直接適用できる
- `intro` による proof construction が自然

という利点があるため、単なる重複とは言えない。

また `SignedGoldenPureFifthPowerExclusion` のような「unit を伴わない pure fifth power 排除」が近接して存在する場合、論理的には unit exclusion から `epsilon = 1` を代入して導出できる可能性がある。ただし正本の依存方向や API 利用箇所を変更すると証明構造が変わるため、ここでは統合可能性を **設計候補** としてのみ扱い、同値・不要性までは断定しない。

## 最適化候補

### 1. `abbrev` を維持する

現状の最大の長所は、巨大な sector proof の結果を短い contract 名で扱えることである。したがって declaration を消して theorem の conclusion を毎回展開する最適化は逆効果である。

### 2. `¬` 形式への変更は必須ではない

例えば

```lean
abbrev SignedGoldenUnitFifthPowerExclusion : Prop :=
  ∀ {u v w} (p : SignedGoldenRamifierStrippedPacket u v w),
    ¬ ∃ epsilon gamma,
      GoldenUnit epsilon ∧
      p.beta = goldenMul epsilon (goldenPow gamma 5)
```

という包装も可能である。

しかし downstream が unit classification から具体 witness をすでに持つなら、現行 curried interface の方が変換が少ない。最適化の価値は利用側の call pattern を全体調査してから判断すべきである。

### 3. 一般的な exponent への抽象化は現段階では不要

指数 `5` をパラメータ化した generic `UnitPowerExclusion n` を作ることは形式上可能だが、この開発では five-adic valuation と `Fin 5` unit classes が核心である。指数 5 を型に露出させている現在の方が FLT5 proof の意味を保持している。

## 必要 Mathlib import と import 最適化候補

確認できた standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

また生成 manifest 上、この宣言を含む source section は `DkMath/FLT/Five/SignedGoldenSectorArithmetic.lean` に由来することを確認できる。

本 `abbrev` 自体が直接要求する機能は軽く、主として

- `Nat`
- proposition / universal quantification / implication
- project-side `GoldenInt`
- `SignedGoldenRamifierStrippedPacket`
- `GoldenUnit`
- `goldenMul`, `goldenPow`

である。

本宣言自身は `ring`, `omega`, `norm_num` などの tactic を一切使用しない。

ただし、この repository に置かれた `FLT5StandAlone.lean` は多数の元 module を連結した generated artifact であり、元の `SignedGoldenSectorArithmetic.lean` の独立した `import` 行はここからは確認できない。したがって最小 Mathlib import 集合を断定することはできない。

import 最適化を行うなら、まず project-side dependency を `SignedGoldenRamifierStrippedPacket`、unit classes、golden fifth-power coordinate API まで絞り、その後 `#print axioms` ではなく実際の module-level build で import を削るべきである。本タスクでは Lean build を行わないため、その検証はしていない。

## Comparator challenge 化の可否

**可能であるが、単独では実装難度が低い。**

この宣言だけを穴埋め問題にすると、必要なのは proposition の API 設計であり proof search は発生しない。そのため theorem prover の推論能力比較より、次の観点を評価する challenge に向く。

1. `abbrev` と `def` / `theorem` の役割を区別できるか。
2. existential negative form と curried contradiction form の違いを説明できるか。
3. implicit parameter `{u v w}` の意図を読めるか。
4. downstream theorem が `intro` だけでこの contract を展開できる理由を説明できるか。

より良い Comparator challenge は、本宣言を仕様として与え、その次の

```lean
signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector
```

を証明させる形である。そこでは unit classification、sector normalization、zero/nonzero sector split が必要になり、モデル間の proof planning 差が現れやすい。

## PDF との対応

対象ブランチには次の PDF が存在することを確認した。

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

ただし今回、PDF 本文の直接取得は成功しなかった。このため 0271 と PDF の具体的ページ・節番号、あるいは PDF 本文中での「unit times fifth power exclusion」の表現との一対一対応は確認できていない。

したがって本稿では PDF 内容を推測して補わず、Lean 型、依存関係、宣言の役割については対象ブランチ上の `Flt5DkMath/FLT5StandAlone.lean` を正本として記述している。

## 次に読むべき宣言

次は theorem

```lean
theorem signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector
    (hClasses : GoldenUnitClassesModFifth)
    (hZero : SignedGoldenZeroSectorExclusion) :
    SignedGoldenUnitFifthPowerExclusion := by
  ...
```

である。

0271 が「何を最終的に排除すべきか」という contract の **型** を定義したのに対し、次の theorem は

- `GoldenUnitClassesModFifth` により任意 unit を有限 sector へ分類し、
- zero sector は `SignedGoldenZeroSectorExclusion` へ送り、
- nonzero sector は直前までに整備した sector arithmetic で排除する

ことで、その contract の実際の証明項を構築する段階に入る。

したがって依存順では、0271 の次に読むべき最も自然な宣言である。
