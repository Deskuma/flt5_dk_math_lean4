# 0248 — `SignedGoldenConjugateCoprimeCore`

## Lean の型

```lean
/-- Receiver contract for contradictions on packets carrying certified conjugate
relative primality. -/
abbrev SignedGoldenConjugateCoprimeCore : Prop :=
  ∀ {u v w : ℕ}, SignedGoldenConjugateCoprimePacket u v w → False
```

これは `theorem` ではなく `abbrev` であり、値域は `Prop` である。`SignedGoldenConjugateCoprimePacket` を一つ受け取れば `False` を返す、という contradiction receiver contract に名前を与える。

## 数学的主張・宣言の意味

数学的には、任意の `u v w : ℕ` について、conjugate-coprime certificate を保持する packet

$$
P : \mathrm{SignedGoldenConjugateCoprimePacket}(u,v,w)
$$

が与えられれば矛盾を導ける、という仮定を一つの命題としてまとめている。

すなわち

$$
\forall u,v,w,\quad
\mathrm{SignedGoldenConjugateCoprimePacket}(u,v,w)
\to \bot.
$$

0245–0247 までで producer 側は、signed normal form から ramifier-stripped data を作り、さらに

$$
\operatorname{GoldenRelPrime}(\beta,\overline{\beta})
$$

を certificate として packet に保持するところまで進んだ。0248 は、その certified state から最終的な矛盾を返す「残りの core」だけを切り出す。

したがって 0248 自身は新しい数論 theorem を証明するものではなく、証明の未解決部分を明確な関数型として表現する architectural declaration である。

## 証明全体での役割

この宣言の役割は、producer pipeline と contradiction pipeline を分離することである。

上流では、normal form から

$$
\mathrm{SignedGoldenRamifierStrippedPacket}
$$

を作り、0244 で `beta` とその共役の relative primality を証明し、0245 でその certificate を持つ `SignedGoldenConjugateCoprimePacket` を定義し、0247 で normal form から直接その packet を得られる facade まで完成した。

0248 では、そこから先を

$$
\text{certified packet}
\longrightarrow
\mathrm{False}
$$

という一点に集約する。

これにより、下流で fifth-power extraction や unit analysis、最終 descent などの方法が変わっても、上流 routing は `SignedGoldenConjugateCoprimeCore` という受け口だけを見ればよい。

正本 source では直後に

```lean
theorem signedBranchARefuter_of_goldenConjugateCoprimeCore
    (hCore : SignedGoldenConjugateCoprimeCore) : SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedGoldenConjugateCoprimePacket_of_normalForm hNF)
```

が続き、本 core が実際に signed Branch-A 全体の refuter へ持ち上げられる。

## 直接依存する定義・補題

直接依存は非常に小さい。

- `SignedGoldenConjugateCoprimePacket`
- Lean の universal quantification `∀`
- implication `→`
- `False`

0245 の packet 自体は内部に

```lean
stripped : SignedGoldenRamifierStrippedPacket u v w
relPrime : GoldenRelPrime stripped.beta (goldenConj stripped.beta)
```

を保持するため、0248 はそれらを個別引数として受け取らず、一つの certified state として受け取る。

直接の theorem 依存はなく、0244 の relative-primality theorem や 0247 の producer は、この `abbrev` の型定義そのものには不要である。

## 構築の流れ

構築は型の別名を与えるだけである。

```lean
abbrev SignedGoldenConjugateCoprimeCore : Prop :=
  ∀ {u v w : ℕ}, SignedGoldenConjugateCoprimePacket u v w → False
```

1. `u v w : ℕ` を暗黙引数として任意に取る。
2. `SignedGoldenConjugateCoprimePacket u v w` を受け取る。
3. その packet から `False` を返すことを要求する。

証明 script、rewrite、tactic は一切ない。

## Lean 固有の処理

### `abbrev`

`abbrev` は透明な略称であり、必要なら Lean は右辺の関数型へ展開できる。したがって `SignedGoldenConjugateCoprimeCore` は新しい opaque な論理対象を作るのではなく、長い proposition を読みやすい名前で扱うための API である。

### `Prop` 値としての関数型

右辺は

```lean
∀ {u v w : ℕ}, SignedGoldenConjugateCoprimePacket u v w → False
```

なので、`hCore : SignedGoldenConjugateCoprimeCore` は実際には関数として適用できる。次の 0249 では

```lean
hCore (signedGoldenConjugateCoprimePacket_of_normalForm hNF)
```

と、packet を直接渡して矛盾を得る。

### 暗黙引数

`u v w` は `{...}` で暗黙化されているため、packet の型から Lean が自動推論する。consumer は通常 `u v w` を明示指定する必要がない。

## 冗長・重複箇所

0237 にはすでに似た形の

```lean
abbrev SignedGoldenRamifierStrippedCore : Prop :=
  ∀ {u v w : ℕ}, SignedGoldenRamifierStrippedPacket u v w → False
```

がある。0248 は packet の refinement が一段進み、`beta` とその共役の relative primality certificate まで保持した状態を受け取る点だけが異なる。

論理的には、0248 を置かずに各 theorem で長い関数型を直接書くこともできる。しかし phase boundary として名前を付ける利点が大きい。

- stripped core と conjugate-coprime core の責任範囲を区別できる。
- proof pipeline のどこまで完了しているかが型名から分かる。
- downstream 実装を差し替えても上流 facade を安定させやすい。
- theorem signatures が短くなる。

したがって API-level の意図的重複と見るのが適切である。

## 最適化候補

1. **現行の phase-specific core 名を維持する**
   - proof-state の到達段階が明確で監査しやすい。

2. **generic contradiction core を導入する**
   - 例えば `Refuter P := P → False` のような一般 alias を用意し、各 phase では `Refuter (Packet ...)` を使う設計が考えられる。
   - ただし domain-specific な theorem discovery は弱くなる。

3. **packet refinement と core lift を統一命名する**
   - `StrippedCore`, `ConjugateCoprimeCore`, `FifthPowerCore` のような段階が増えるなら namespace / naming convention をさらに統一できる。

4. **`Not` 表記との比較**
   - `SignedGoldenConjugateCoprimePacket u v w → False` は `¬ SignedGoldenConjugateCoprimePacket u v w` と同値なので、可読性比較の余地がある。ただし universal quantification と組み合わせた現行形は関数適用しやすい。

局所的には一行の `abbrev` なので、実装最適化より architecture の整理が主な検討対象である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用しているが、本宣言自身は Mathlib の高度な theorem や tactic を一切使用しない。

必要なのは実質的に

- `Nat`
- `Prop`
- `False`
- `SignedGoldenConjugateCoprimePacket`

だけである。

ただし packet 定義の上流は `GoldenRelPrime`、黄金整数ノルム、Euclidean-domain、整数整除など広い Mathlib API に依存する。そのため実際の module import 最適化は `SignedGoldenConjugateCoprime.lean` 全体で測る必要がある。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、候補としてのみ記録する。

## Comparator challenge 化の可否

適している。ただし theorem proof の速度比較というより API architecture の比較になる。

比較候補は次の通り。

- A: 現行の phase-specific `abbrev`
- B: 長い関数型を各 theorem に直接書く
- C: generic `Refuter` alias を導入する
- D: packet の `Nonempty` 否定や `¬ ∃ ...` として contradiction contract を表現する

比較軸は、theorem signature の短さ、phase boundary の可視性、Lean の elaboration の単純さ、theorem discovery、refactor 耐性、consumer code の読みやすさである。

特に A と C の比較は、domain-specific な名前付けが長い形式化の認知負荷をどれだけ下げるかを評価するよい課題になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` generated section である。

正本 source では 0247 の直後に本宣言があり、その直後に 0249 `signedBranchARefuter_of_goldenConjugateCoprimeCore` が続く。

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし、この internal receiver contract に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0249 `signedBranchARefuter_of_goldenConjugateCoprimeCore`** である。

```lean
theorem signedBranchARefuter_of_goldenConjugateCoprimeCore
    (hCore : SignedGoldenConjugateCoprimeCore) : SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedGoldenConjugateCoprimePacket_of_normalForm hNF)
```

0248 が certified packet から `False` を返す receiver contract を定義し、0249 は 0247 の normal-form producer とこの receiver を合成して、signed Branch-A normal form 全体を refute する theorem へ持ち上げる。