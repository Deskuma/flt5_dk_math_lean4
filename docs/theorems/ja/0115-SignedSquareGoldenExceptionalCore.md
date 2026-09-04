# 0115 — `SignedSquareGoldenExceptionalCore`

## Lean の型

```lean
/-- Receiver contract for contradictions stated on the common signed square/norm packet. -/
abbrev SignedSquareGoldenExceptionalCore : Prop :=
  ∀ {u v w : ℕ}, SignedSquareGoldenExceptionalPacket u v w → False
```

本宣言は theorem ではなく `abbrev` である。`SignedSquareGoldenExceptionalPacket u v w` を一つ受け取れば `False` を返せる、という universal contradiction receiver を一つの名前にまとめている。

## 数学的主張

`SignedSquareGoldenExceptionalPacket u v w` は、signed five-adic power split から得られた整数座標 $M,N,\delta$ と witnesses $a,b$ に対して、少なくとも

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

を保持し、さらに difference / sum の provenance も記録する。

`SignedSquareGoldenExceptionalCore` は、**そのような packet は任意の $u,v,w$ に対して存在し得ない** という contradiction contract を

$$
\forall u,v,w,\quad
\operatorname{SignedSquareGoldenExceptionalPacket}(u,v,w)\to\bot
$$

という形で表す。

これは個々の invariant のどれが矛盾を生むかをまだ指定しない。黄金整数、ramifier、unit sector、descent など後続層が最終的にこの contract を実装すれば、上流の signed Branch-A normal form を一括して排除できる。

## 証明全体での役割

本宣言は square-golden exceptional 層の **receiver interface** である。

0111–0114 は、入力を徐々に変換して `SignedSquareGoldenExceptionalPacket` を **構築する側** だった。

```text
SignedBranchANormalForm
  → SignedFiveAdicPowerSplit
  → SignedSquareGoldenExceptionalPacket
```

0115 では向きが反転する。

```text
SignedSquareGoldenExceptionalPacket
  → False
```

この分離により、上流は packet の構築だけを担当し、下流は packet が満たす invariant 群だけを見て contradiction を証明できる。元の Fermat equation や signed orientation の分岐を下流へ持ち込む必要がない。

直後の `signedBranchARefuter_of_squareGoldenExceptionalCore` は、この architecture をそのまま一行で利用する。

```lean
exact hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)
```

すなわち 0114 が producer、0115 が consumer contract、次 theorem が両者を接続する adapter である。

## 直接依存する定義・補題

### `SignedSquareGoldenExceptionalPacket`

直接依存する唯一の project declaration である。0111 で解説した `Type` packet で、five-adic split、signed provenance、golden norm、tenth-power boundary、square discriminant、five-discriminant relation を保持する。

### `False`

Lean の組み込み命題。inhabitant を持たない proposition であり、ここでは packet から contradiction を導く codomain になっている。

### 暗黙の自然数パラメータ

```lean
{u v w : ℕ}
```

は implicit binder である。core の利用側では packet 自身の型から `u v w` が推論される。

## 証明・定義の流れ

`abbrev` なので proof script は存在しない。定義を論理的に読み下すと次の通りである。

1. 任意の自然数 `u v w` を取る。
2. `SignedSquareGoldenExceptionalPacket u v w` を仮定する。
3. そこから `False` を返すことを要求する。
4. これをすべての `u v w` に対して要求する関数型全体を `SignedSquareGoldenExceptionalCore` と名付ける。

重要なのは、本宣言自身は contradiction を **証明していない** という点である。後続の黄金整数による議論がこの型の inhabitant を構築することが、実際の数学的課題になる。

## Lean 固有の処理

### `abbrev`

`abbrev` は透明な省略名であり、elaboration や reduction の際に本体

```lean
∀ {u v w : ℕ}, SignedSquareGoldenExceptionalPacket u v w → False
```

へ容易に展開できる。

この用途では新しい wrapper structure や opaque definition を導入せず、長い receiver 型に意味のある名前だけを与えたいので適切である。

### implicit binder

`{u v w : ℕ}` が暗黙引数なので、例えば

```lean
hCore hPacket
```

と適用すれば `hPacket : SignedSquareGoldenExceptionalPacket u v w` の型から indices が推論される。明示的に `hCore (u := u) (v := v) (w := w) hPacket` と書く必要は通常ない。

### `P → False` と否定

Lean では `¬ P` は定義上 `P → False` である。したがって各固定 `u v w` に対して、この core は

```lean
¬ SignedSquareGoldenExceptionalPacket u v w
```

と同じ論理内容を持つ。

ただし現在の形は indices を外側で全称量化しているため、下流 theorem へそのまま高階 receiver として渡しやすい。

## 冗長・重複箇所

同じ architecture は以前の

- `BranchBFifthPowerCore`
- `BranchBSquareGoldenCore`

にも現れている。いずれも「正規化された packet / normal form を受け取れば `False`」という receiver contract である。

これは論理的には重複だが、proof layer ごとに contradiction interface を名付けることで、どの情報レベルまで reduction が済んでいるかが型名だけで分かる。したがって現状では **意図的かつ有益な architecture-level duplication** と評価できる。

また

```lean
∀ {u v w}, Packet u v w → False
```

は

```lean
¬ ∃ u v w, Packet u v w
```

あるいは適切な dependent existential / `Nonempty` を用いた形とも数学的には近い。しかし現在の curried receiver 形式は、既に得られた concrete packet を即座に `hCore packet` と消費できる利点がある。

## 最適化候補

### 1. generic contradiction receiver の抽象化

同型の core declarations が今後さらに増えるなら、indexed packet に対する generic refuter 型を導入する余地がある。

例として概念的には

```lean
abbrev IndexedRefuter (P : ℕ → ℕ → ℕ → Type) : Prop :=
  ∀ {u v w}, P u v w → False
```

のような形が考えられる。

ただし各 proof layer の意味が固有名 `SignedSquareGoldenExceptionalCore` によって明瞭になる利点は大きい。単なる行数削減だけを目的とした一般化は推奨しにくい。

### 2. `¬ Nonempty ...` 表現との比較

packet が `Type` なので、固定 indices に対して

```lean
¬ Nonempty (SignedSquareGoldenExceptionalPacket u v w)
```

と表す設計も可能である。しかし producer 側はすでに concrete packet object を返すため、現在の `Packet → False` の方が余計な `Nonempty.intro` / elimination を必要とせず直接的である。

### 3. core の最小入力化

後続 contradiction が packet の全 field を使わないことが判明した場合、必要な invariant だけを持つより小さな core packet を切り出せる可能性がある。これは証明依存を狭め、Comparator challenge にも向く。

ただし現時点では後続の golden arithmetic / ramifier stripping がどの field を消費するかを依存順に確認してから判断すべきであり、ここでは最適化候補に留める。

## 必要 Mathlib import と import 最適化候補

対象 standalone source は

```lean
import Mathlib
```

を使用している。

本宣言そのものが直接必要とするものは非常に少なく、Lean の `Prop`、`False`、`∀`、関数型、自然数型と、project declaration `SignedSquareGoldenExceptionalPacket` だけである。tactic、ring normalization、divisibility API、golden arithmetic の Mathlib lemma を直接呼ばない。

したがって modular source では、本宣言だけを理由として `Mathlib` 全体を import する必要はない。実際の最小 import は `SignedSquareGoldenExceptionalPacket` を定義する `SignedSquareGoldenExceptional` module の import closure に依存する。

さらに core alias 自体を packet 定義と同じ module に置くなら追加 import は不要である可能性が高い。今回は Lean build を行っていないため、具体的な最小 import 集合は未検証である。

## Comparator challenge 化の可否

**可能。proof API / interface design の比較課題として適している。**

比較候補は次である。

- 現行の `∀ {u v w}, Packet u v w → False`
- `∀ {u v w}, ¬ Packet u v w`
- `¬ ∃ u v w, Nonempty (Packet u v w)` に相当する existential exclusion
- generic indexed refuter alias を導入する設計
- packet 全体ではなく contradiction に必要な最小 invariant packet を入力とする設計

評価軸は kernel proof の短さだけでなく、producer との接続の簡潔さ、implicit inference、エラーメッセージの局所性、proof graph の可読性、下流層との結合度になる。

特に直後の theorem が

```lean
exact hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)
```

と一行で閉じることは、現行 API の強い利点である。

## 既存 PDF との対応

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。

本記事の形式的根拠は、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` generated section である。

今回 GitHub connector から PDF 本文の該当ページを直接照合していないため、PDF 上の具体的な節番号・ページ番号は推測で補っていない。

## 次に読むべき定理

直後の未解説 theorem は

```lean
theorem signedBranchARefuter_of_squareGoldenExceptionalCore
    (hCore : SignedSquareGoldenExceptionalCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)
```

である。

0114 の producer と 0115 の receiver contract を直接接続し、square-golden exceptional packet を排除できるなら signed Branch-A normal form 全体を排除できることを示す adapter theorem である。依存順ではこれを 0116 として読むのが自然である。
