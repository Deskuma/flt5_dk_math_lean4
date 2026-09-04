# 0245 — `SignedGoldenConjugateCoprimePacket`

## Lean の型

```lean
/-- A packet retaining the stripped data and certified conjugate coprimality. -/
structure SignedGoldenConjugateCoprimePacket (u v w : ℕ) : Type where
  stripped : SignedGoldenRamifierStrippedPacket u v w
  relPrime : GoldenRelPrime stripped.beta (goldenConj stripped.beta)
```

これは `theorem` ではなく `structure` である。0231 `SignedGoldenRamifierStrippedPacket` が保持する ramifier-stripped data と、0244 で証明した `beta` とその共役の相対素性 certificate を一つの型へ束ねる。

## 数学的主張・宣言の意味

この structure の元は、単なる `beta` ではなく、次の二つを同時に保持する certified state である。

1. `stripped` — 可視な ramified factor `tau` を取り除いた packet。
2. `relPrime` — その packet の `beta` と `goldenConj beta` が黄金整数環の意味で相対素である証明。

すなわち、数学的には

$$
\beta \text{ is ramifier-stripped}
$$

かつ

$$
\gcd(\beta,\overline\beta)\sim 1
$$

という二つの条件を同じ object にまとめる。

ここで `GoldenRelPrime x y` は Bézout 係数や gcd の具体値を直接要求せず、任意の共通因子 `d` が `GoldenUnit d` であることを要求する定義である。したがって `relPrime` field は、概念的には

$$
\forall d,\quad d\mid\beta\land d\mid\overline\beta
\Longrightarrow d\text{ is a unit}
$$

という certificate を保持する。

## 証明全体での役割

0231–0244 では、exceptional branch から構成した `beta` について、

$$
N(\beta)=b^5,
$$

$$
\tau\nmid\beta,
$$

さらに 0244 で

$$
GoldenRelPrime(\beta,\overline\beta)
$$

まで証明した。

0245 は、その成果を downstream が直接消費できる packet へ昇格させる integration point である。

この直後には

```lean
def signedGoldenConjugateCoprimePacket_of_stripped
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    SignedGoldenConjugateCoprimePacket u v w :=
  ⟨p, p.beta_relPrime_conj⟩
```

が続く。すなわち 0244 の theorem を毎回明示的に呼び出す代わりに、`stripped` data と `relPrime` certificate を一度 packet 化し、その後の fifth-power extraction 層へ渡す設計になっている。

さらに source では、この packet を signed normal form から直接構成する facade、そしてこの packet を受け取って `False` を返す receiver contract が続く。したがって 0245 は、局所算術の証明結果を上位 pipeline へ運ぶ representation boundary として機能する。

## 直接依存する定義・補題

structure の型定義として直接依存するのは次の三点である。

- 0231 `SignedGoldenRamifierStrippedPacket`
- 0208 `GoldenRelPrime`
- 0163 `goldenConj`

`relPrime` field の型は

```lean
GoldenRelPrime stripped.beta (goldenConj stripped.beta)
```

であり、field dependency によって `stripped.beta` を参照している。

0244 `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj` は structure 定義そのものの型には現れないが、直後の constructor

```lean
⟨p, p.beta_relPrime_conj⟩
```

で `relPrime` field を埋める producer theorem として実質的に直結している。

概念的には

$$
\texttt{SignedGoldenRamifierStrippedPacket}
+
\texttt{beta\_relPrime\_conj}
\longrightarrow
\texttt{SignedGoldenConjugateCoprimePacket}
$$

である。

## 構築の流れ

この宣言自身には proof script は存在しない。Lean の structure declaration によって二つの field を持つ新しい型を定義するだけである。

```lean
structure SignedGoldenConjugateCoprimePacket (u v w : ℕ) : Type where
  stripped : SignedGoldenRamifierStrippedPacket u v w
  relPrime : GoldenRelPrime stripped.beta (goldenConj stripped.beta)
```

構築時には、まず `stripped` field に packet を渡し、その packet に依存して `relPrime` field の期待型が決まる。

直後の source では、

```lean
⟨p, p.beta_relPrime_conj⟩
```

によってこの structure が構成される。第一 field に `p` を入れると、第二 field は自動的に

```lean
GoldenRelPrime p.beta (goldenConj p.beta)
```

を要求するため、0244 の theorem がそのまま certificate になる。

## Lean 固有の処理

重要なのは dependent field である。

```lean
relPrime : GoldenRelPrime stripped.beta (goldenConj stripped.beta)
```

は単なる独立した `Prop` field ではなく、同じ structure 内の前 field `stripped` の値に依存している。

そのため packet を持てば、

```lean
p.stripped
p.relPrime
```

という projection により、data とその data に対する正当性 certificate を常に対応づけたまま取り出せる。

これは Lean でよく使われる dependent record pattern であり、後続 theorem が「stripped packet と、それに対応する relPrime proof を別々の引数として受け取る」必要をなくす。

また本宣言は `structure` なので、Lean は自動的に constructor と projection を生成する。proof irrelevance により `relPrime : Prop` の具体的 proof term 自体を計算データとして扱う必要もない。

## 冗長・重複箇所

情報として見ると、0245 は 0231 の packet に 0244 の theorem を付加しただけなので、論理的な新情報はほとんど増えていない。

実際、任意の `p : SignedGoldenRamifierStrippedPacket u v w` に対して 0244 が既に

```lean
p.beta_relPrime_conj
```

を与えるため、downstream は必要な場所で毎回 0244 を呼び出す設計でもよい。

それでも専用 packet にする利点は大きい。

- fifth-power extraction 層が 0244 の proof provenance を知らずに済む。
- 「stripped 済み」かつ「共役相対素性 certified」という状態遷移を型で表現できる。
- producer / consumer の module boundary が明確になる。
- 後続 receiver contract が certified state 一つだけを引数にできる。

したがってこれは論理的 redundancy ではあるが、proof architecture 上は意図的な state refinement である。

## 最適化候補

1. **現行の certified packet を維持する**
   - pipeline の状態遷移が型で見え、監査性が高い。

2. **0245 を削除して stripped packet + theorem を直接利用する**
   - declaration 数は減るが、downstream が 0244 へ直接依存する。

3. **0231 に `relPrime` field を直接追加する**
   - packet 数は減るが、ramifier stripping と conjugate coprimality という異なる proof stage が融合し、依存順が重くなる。

4. **generic certified wrapper を導入する**
   - 例えば `structure Certified (α : Type) (P : α → Prop)` のような一般 wrapper を使えるが、この一例だけなら抽象化過多になる可能性が高い。

5. **後続 fifth-power extraction packet と統合する**
   - さらに `beta = epsilon * gamma^5` certificate まで同じ structure に加えることもできるが、proof stage の境界が失われるため現行の段階的 refinement の方が読みやすい。

現行設計は theorem museum の依存順を追う上でも、各 proof milestone が型として明確なので合理的である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用しているが、本 structure 自体が要求する Mathlib 表面は非常に小さい。

実質的には、

- structure / dependent field machinery
- `Prop`
- 上流で定義済みの `SignedGoldenRamifierStrippedPacket`
- `GoldenRelPrime`
- `goldenConj`

だけである。

本宣言自身は tactic を一切使わない。したがって `Mathlib` 全体を必要とする理由は 0245 単独にはない。

ただし実際の `SignedGoldenConjugateCoprime.lean` module では、直前の 0241–0244 が整数整除、`Nat.Coprime`、`omega`、`ring` などを利用する。そのため module 単位の最小 import は structure 単独より大きい。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較対象は proof そのものではなく representation design になる。

- A: 現行の dedicated certified packet
- B: `SignedGoldenRamifierStrippedPacket` と 0244 theorem を別々に保持
- C: 0231 に `relPrime` field を統合
- D: generic `Certified` wrapper を利用
- E: fifth-power extraction certificate まで一つの大きな packet に統合

比較軸は、

- downstream theorem の引数数
- module dependency depth
- state transition の可視性
- proof reconstruction の必要性
- field projection の読みやすさ
- 将来の refactor に対する安定性

である。

特に A と B の比較は、「証明済み invariant を型に昇格させる価値」を測る明瞭な Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` generated section である。

source では 0244 `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj` の直後に本 structure が置かれ、その直後に

```lean
def signedGoldenConjugateCoprimePacket_of_stripped ...
```

が続くことを確認した。

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし、本 structure に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0246 `signedGoldenConjugateCoprimePacket_of_stripped`** である。

```lean
def signedGoldenConjugateCoprimePacket_of_stripped
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    SignedGoldenConjugateCoprimePacket u v w :=
  ⟨p, p.beta_relPrime_conj⟩
```

0245 が certified state の型を定義したので、0246 は任意の stripped packet に 0244 の theorem を添えて、その certified state を実際に構成する canonical producer になる。