# 0117 — `branchB_false_of_squareGoldenExceptionalCore`

## Lean の型

```lean
/-- The same square-golden core consequently closes every routed Branch-B pack. -/
theorem branchB_false_of_squareGoldenExceptionalCore
    (hCore : SignedSquareGoldenExceptionalCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_squareGoldenExceptionalCore hCore) hPack hBranch
```

本定理は、square-golden exceptional packet を矛盾へ送る core を仮定すると、Branch-B 条件を満たす任意の `CounterexamplePack` が矛盾することを示す closure theorem である。

## 数学的主張

入力は三つである。

1. `hCore : SignedSquareGoldenExceptionalCore`
2. `hPack : CounterexamplePack x y z`
3. `hBranch : ¬ 5 ∣ z - y`

`SignedSquareGoldenExceptionalCore` は概念的に

$$
\forall u,v,w,\quad
\operatorname{SignedSquareGoldenExceptionalPacket}(u,v,w)\to\bot
$$

という refuter である。

一方、`hPack` と Branch-B 条件

$$
5\nmid(z-y)
$$

からは、0058 `branchB_false_of_signedBranchARefuter` が、signed Branch-A normal form をすべて排除する refuter を受け取れば `False` を返す。

0116 `signedBranchARefuter_of_squareGoldenExceptionalCore` により

$$
\operatorname{SignedSquareGoldenExceptionalCore}
\longrightarrow
\operatorname{SignedBranchARefuter}
$$

が得られるので、本定理は二つの既存変換を合成して

$$
\operatorname{SignedSquareGoldenExceptionalCore}
\longrightarrow
\bigl(\operatorname{CounterexamplePack}(x,y,z)\land 5\nmid(z-y)\bigr)
\longrightarrow
\bot
$$

を得ている。

新しい整数恒等式、five-adic valuation、黄金整数の算術をここで証明しているわけではない。数学的内容は、すでに構築済みの contradiction interface を Branch-B closure API まで運ぶことにある。

## 証明全体での役割

この theorem は `SignedSquareGoldenExceptional.lean` の最後の宣言であり、この module の **出口** に相当する。

直前までの流れは次のように整理できる。

```text
SignedBranchANormalForm
  → SignedFiveAdicPowerSplit
  → SignedSquareGoldenExceptionalPacket
  → False
```

0116 では、この packet-level contradiction を

```text
SignedBranchANormalForm → False
```

すなわち `SignedBranchARefuter` へ引き戻した。

0117 はさらに既存の signed routing theorem 0058 を使って、

```text
CounterexamplePack + Branch-B condition
  → Signed Branch-A routing
  → SignedBranchARefuter
  → False
```

まで戻す。

したがって、square-golden exceptional core を将来どのような黄金整数論・降下法で実装しても、その実装は `SignedSquareGoldenExceptionalCore` を満たしさえすれば Branch-B contradiction へ自動的に接続される。この interface separation が本定理の最も重要な役割である。

## 直接依存する定義・補題

### `SignedSquareGoldenExceptionalCore`

0115 で解説した packet-level contradiction contract。

```lean
abbrev SignedSquareGoldenExceptionalCore : Prop :=
  ∀ {u v w : ℕ},
    SignedSquareGoldenExceptionalPacket u v w → False
```

### `signedBranchARefuter_of_squareGoldenExceptionalCore`

0116 で解説した adapter theorem。

```lean
theorem signedBranchARefuter_of_squareGoldenExceptionalCore
    (hCore : SignedSquareGoldenExceptionalCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF)
```

これにより packet-level core が normal-form-level refuter へ変換される。

### `branchB_false_of_signedBranchARefuter`

0058 で解説した既存の Branch-B closure theorem。

```lean
theorem branchB_false_of_signedBranchARefuter
    (hRefuter : SignedBranchARefuter)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  rcases signedBranchA_normalForm_of_branchB hPack hBranch with hDiff | hSum
  · exact hRefuter hDiff
  · exact hRefuter hSum
```

この theorem が difference / sum の signed orientation の場合分けを内部で処理しているため、0117 では orientation を再び展開する必要がない。

### `CounterexamplePack`

FLT5 の正の primitive candidate を保持する基本 packet。0117 自身はその fields を直接参照せず、0058 へそのまま渡す。

### Branch-B 条件 `¬ 5 ∣ z - y`

Branch-B routing を起動する仮定。0117 自身では divisibility reasoning を行わず、0058 へ forwarding する。

## 証明の流れ

証明は単一の関数合成である。

1. `hCore` を 0116 に渡す。
2. `SignedBranchARefuter` を得る。
3. その refuter と `hPack`, `hBranch` を 0058 に渡す。
4. `False` を得る。

Lean term としては、

```lean
branchB_false_of_signedBranchARefuter
  (signedBranchARefuter_of_squareGoldenExceptionalCore hCore)
  hPack
  hBranch
```

そのものが証明になっている。

この形を数学的な関数合成として書けば、

$$
\text{square-golden core}
\xrightarrow{\;0116\;}
\text{signed Branch-A refuter}
\xrightarrow{\;0058\;}
\text{Branch-B contradiction}
$$

である。

## Lean 固有の処理

### `exact` だけで閉じる theorem

proof body に `intro` すらない。定理の引数は declaration header ですでに束縛されており、goal は `False` なので、期待型に一致する compound term を `exact` して終了する。

### implicit arguments の推論

`branchB_false_of_signedBranchARefuter` の `{x y z : ℕ}` は implicit である。Lean は `hPack : CounterexamplePack x y z` と `hBranch` の型から indices を推論するので、

```lean
(x := x) (y := y) (z := z)
```

の明示指定は不要である。

同様に、0116 が返す `SignedBranchARefuter` の内部 indices も 0058 側で必要なときに推論される。

### `abbrev` を介した interface matching

`SignedSquareGoldenExceptionalCore` と `SignedBranchARefuter` は `abbrev` で定義された proposition interface である。Lean の reducibility により、それぞれの関数型として利用できるが、0117 自身は展開形を知る必要がない。named interface のまま theorem composition が成立している。

### algebra tactic が一切現れない

`ring`, `omega`, `norm_num`, `simp`, `rw`, `push_cast`, `exact_mod_cast` などは使われない。square-golden identities、signed routing、five-adic split といった実質的な数学処理が upstream に完全に隔離されている証拠である。

## 冗長・重複箇所

本 theorem は論理的には非常に薄い wrapper である。

概念的には

```lean
A → B
B → C → D → False
-----------------
A → C → D → False
```

という composition にすぎない。

さらに、0116 自体も

```text
SignedSquareGoldenExceptionalCore
  → SignedBranchARefuter
```

という adapter なので、0117 で 0116 を使わず producer を直接展開することも理論上は可能である。

例えば概念的には、

```lean
branchB_false_of_signedBranchARefuter
  (fun hNF => hCore (signedSquareGoldenExceptionalPacket_of_normalForm hNF))
  hPack hBranch
```

のように一段をインライン化できる。

しかしこれは重複削減というより abstraction boundary の破壊に近い。現在の theorem chain は各層を名前で可視化しており、proof graph を読むうえで価値がある。

## 最適化候補

### 1. 現行の named adapter を維持する

最も有力な選択。コード量はすでに最小級で、0116 と 0058 の責務分離も明確である。

### 2. 0116 を inline 化する

一行の proof term に圧縮できるが、`SignedSquareGoldenExceptionalCore → SignedBranchARefuter` という重要な層間変換の名前が失われる。保守性と可読性の観点では現行形に分がある。

### 3. generic refuter transport helper

否定の前合成を一般化した helper を用意すれば、0116 と 0117 に類する adapter 群を抽象化できる。

ただし FLT5 proof graph では theorem 名そのものが数学的な routing map として機能しているので、同型 wrapper が大量に増えない限り generic 化の利益は小さい。

### 4. theorem chain の documentation 化

コード最適化より、

```text
ExceptionalCore → SignedBranchARefuter → Branch-B False
```

という chain を module-level documentation に明示する方が実用的な改善になり得る。本 theorem はまさに module boundary の出口だからである。

## 必要 Mathlib import と import 最適化候補

対象 repository の standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

0117 自身が直接必要とする要素は非常に少ない。

- `ℕ`
- `False`
- divisibility notation `∣`
- natural subtraction `z - y`
- project 内の `CounterexamplePack`
- `SignedSquareGoldenExceptionalCore`
- `signedBranchARefuter_of_squareGoldenExceptionalCore`
- `branchB_false_of_signedBranchARefuter`

proof body では Mathlib tactic を一つも使用しない。

したがって、modular source で本 theorem のためだけに `Mathlib` 全体を import する必要はないと考えられる。ただし、この repository では元の modular file が standalone artifact に統合されており、今回確認できた formal source は generated section である。依存 declarations の本来の import graph を実際に削って Lean build する操作は行っていないため、具体的な最小 import 集合は **未検証** である。

import 最適化を行うなら、まず `SignedSquareGoldenExceptional.lean` が直接参照する project modules を列挙し、その transitive Mathlib imports を `lake build` で検証するのが安全である。本博物館では Lean build を行わない方針なので、ここでは候補の指摘に留める。

## Comparator challenge 化の可否

**可能。proof composition と abstraction boundary の比較課題として適している。**

比較候補は次の通りである。

- 現行の named two-stage composition
- 0116 を inline 化した一段 proof
- `fun hNF => ...` を明示した lambda 版
- generic refuter transport helper を使う版
- 0058 の signed orientation routing まで展開した完全 inline 版

評価軸は、

- 行数
- elaboration の安定性
- エラーメッセージの局所性
- 依存関係の可読性
- upstream implementation 変更への耐性
- theorem 名が proof graph documentation として果たす役割

である。

特に完全 inline 版は、difference / sum routing と packet construction が再露出し、コードが長くなるだけでなく責務分離も弱くなる可能性が高い。Comparator challenge としては、単なる最短コード競争ではなく **API boundary を保った証明がなぜ強いか** を比較する題材になる。

## 既存 PDF との対応

対象ブランチには次の既存 PDF が存在する。

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

また TeX source archive `docs/pdf/TeX/TeX-FLT5_Fermat's_Last_Theorem_for_Exponent_Five-v0-r1.zip` も存在する。

本記事の形式的根拠は、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` generated section である。

今回 GitHub connector では PDF 本文の該当ページそのものを展開して照合していない。そのため、PDF 上の具体的な節番号・ページ番号は推測で補っていない。PDF は narrative context の存在確認に留め、Lean declaration を最終根拠とした。

## 次に読むべき定理

本 theorem は `SignedSquareGoldenExceptional.lean` の最後の宣言である。直後に module が閉じ、次の generated source `DkMath/FLT/Five/GoldenOrder.lean` が始まる。

その最初の未解説宣言は theorem ではなく、

```lean
/-- An integral pair representing `a+b*φ` in the basis `1,φ`, with `φ^2=φ+1`. -/
structure GoldenInt where
  fst : ℤ
  snd : ℤ
deriving DecidableEq
```

である。

これは整数対 $(a,b)$ により

$$
a+b\varphi,
\qquad \varphi^2=\varphi+1
$$

を表現する黄金整数環の基礎 carrier である。

0117 までで「square-golden exceptional core があれば Branch-B は閉じる」という interface が完成した。次の module からは、その core を最終的に供給するための黄金整数算術そのものを構築する段階へ移る。依存順では `GoldenInt` を 0118 として読むのが自然である。
