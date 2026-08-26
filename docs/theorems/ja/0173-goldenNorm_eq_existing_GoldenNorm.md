# 0173 — `goldenNorm_eq_existing_GoldenNorm`

## Lean の型

```lean
/-- Compatibility between the structured norm and the earlier binary quadratic form. -/
theorem goldenNorm_eq_existing_GoldenNorm (M N : ℤ) :
    goldenNorm (⟨M, N⟩ : GoldenInt) = GoldenNorm M N := rfl
```

これは `theorem` であり、整数座標 `M,N` から直接構成した `GoldenInt` の structure-level norm `goldenNorm` と、FLT5 の前段から使われている二変数二次形式 `GoldenNorm M N` が定義的に一致することを示す。

## 数学的主張または宣言の意味

`GoldenInt` の元を

$$
M+N\varphi
$$

と読む。`goldenNorm` は

$$
N(M+N\varphi)=M^2+MN-N^2
$$

を返し、既存 API `GoldenNorm M N` も同じ二次形式

$$
M^2+MN-N^2
$$

を表す。

したがって本 theorem の数学的内容は

$$
\mathrm{goldenNorm}(M+N\varphi)=\mathrm{GoldenNorm}(M,N)
$$

という、同一の黄金ノルムを「structure の元」と「二つの整数座標」という二つの表現で結ぶ互換性である。

新しい数論的事実を証明する theorem ではなく、表現境界を閉じる bridge theorem である。

## 証明全体での役割

0172 `goldenNorm_eq_GoldenNorm` は任意の `x : GoldenInt` に対して

```lean
goldenNorm x = GoldenNorm x.fst x.snd
```

を与えた。

0173 はその座標入力版であり、前段の FLT5 証明で既に `M N : ℤ` を持っている場面から、わざわざ `x.fst`, `x.snd` を経由せずに structured `GoldenInt` API へ移るための convenience bridge である。

概念的には

```text
整数座標 M,N
    │
    ├─ GoldenNorm M N
    │
    └─ ⟨M,N⟩ : GoldenInt
          │
          └─ goldenNorm ⟨M,N⟩
```

という二本の経路が同じ値へ合流することを明示する。

この直後には `goldenNorm_mul` が続き、structure 上のノルムに乗法性

$$
N(xy)=N(x)N(y)
$$

を与える。そのため 0173 は、前段の binary norm 計算から後段の ring-theoretic norm API へ入る最後の座標 bridge と見ることができる。

## 直接依存する定義・補題

直接依存は次である。

- `GoldenInt`
- `goldenNorm`
- 既存の二変数二次形式 `GoldenNorm`
- `GoldenInt` の structure literal `⟨M,N⟩`

証明は `rfl` なので、0172 を theorem として利用してはいない。つまり 0173 は 0172 から論理的に導出可能ではあるが、Lean source 上では両者とも同じ定義的等価性から独立に閉じている。

## 証明または構築の流れ

証明は一語である。

```lean
:= rfl
```

左辺を展開すると

```lean
goldenNorm (⟨M, N⟩ : GoldenInt)
```

は

```lean
M ^ 2 + M * N - N ^ 2
```

へ還元される。

右辺 `GoldenNorm M N` も同じ整数式へ展開されるので、Lean は両辺を definitional equality として認識し、反射律だけで証明できる。

proof flow は

```text
goldenNorm ⟨M,N⟩
→ unfold goldenNorm
→ M^2 + M*N - N^2

GoldenNorm M N
→ unfold GoldenNorm
→ M^2 + M*N - N^2

→ rfl
```

である。

## Lean 固有の処理

重要なのは theorem が `rfl` で閉じることである。

これは `goldenNorm` と `GoldenNorm` が、後から証明された非自明な等式によって一致しているのではなく、最終的に同じ term へ reduce するよう設計されていることを意味する。

また `⟨M,N⟩ : GoldenInt` という型注釈により、単なる pair ではなく `GoldenInt` constructor として elaboration される。そこから `.fst` と `.snd` が定義的に `M`,`N` へ還元されるため、追加の `simp` すら不要になる。

## 冗長・重複箇所

0172

```lean
theorem goldenNorm_eq_GoldenNorm (x : GoldenInt) :
    goldenNorm x = GoldenNorm x.fst x.snd := rfl
```

に `x := (⟨M,N⟩ : GoldenInt)` を代入すれば、0173 とほぼ同じ内容が得られる。

その意味で theorem surface には明確な重複がある。

ただし用途は異なる。

- 0172 は既に `x : GoldenInt` を持つ proof から binary API へ降りるのに自然。
- 0173 は既に `M,N : ℤ` を持つ前段の proof から structured API へ上がるのに自然。

したがってこれは数学的重複というより、呼び出し側の表現に合わせた ergonomic duplication と評価できる。

## 最適化候補

候補は次である。

1. 現行どおり 0172 と 0173 を両方残し、利用側の rewrite を最短にする。
2. 0172 のみを primitive theorem とし、0173 を

```lean
simpa using goldenNorm_eq_GoldenNorm (⟨M, N⟩ : GoldenInt)
```

で導出する。
3. 0173 のみを残し、structure 版は `x.fst`, `x.snd` を渡して構築する。
4. `goldenNorm` 自体を `GoldenNorm x.fst x.snd` の wrapper として定義し、bridge theorem を API documentation 用に限定する。
5. 一般の二次形式 abstraction を導入し、structured norm と coordinate norm を同じ primitive definition の specialization とする。

局所 proof は `rfl` なので、tactic-level の最適化余地はない。主な検討対象は theorem 数、命名、API 境界である。

## 必要 Mathlib import と import 最適化候補

本 theorem 単独では tactic を使用しない。

必要なのは `GoldenInt`、`goldenNorm`、`GoldenNorm`、整数の基本演算だけであり、standalone artifact の `import Mathlib` はこの theorem 単体には過剰である可能性が高い。

ただし `GoldenOrder` module 全体では `Zsqrtd`、typeclass hierarchy、`omega`、`norm_num`、`ring` などを使っているため、実際の最小 import は module 単位で検証する必要がある。今回は Lean build を行わないため、具体的な最小 import 集合は未確認とする。

## Comparator challenge 化の可否

適している。ただし proof tactic の速さではなく API architecture の比較課題になる。

比較候補は、

- 0172/0173 の二本立て
- structure bridge 一本だけ
- coordinate bridge 一本だけ
- `goldenNorm := GoldenNorm x.fst x.snd` を唯一の実装とする設計
- 一般 quadratic norm abstraction から両 API を生成する設計

である。

比較軸は、downstream rewrite の長さ、theorem surface の大きさ、definition unfolding の透明性、前段の整数座標 theorem との接続容易性、一般化可能性である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `DkMath/FLT/Five/GoldenOrder.lean` generated section である。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在することを確認した。ただし、本 theorem に対応する具体的な PDF ページ・節番号は直接特定していないため推測しない。

## 次に読むべき宣言

Lean source 上で直後に置かれている宣言は

```lean
/-- The golden norm is multiplicative. -/
theorem goldenNorm_mul (x y : GoldenInt) :
    goldenNorm (goldenMul x y) = goldenNorm x * goldenNorm y := by
  simp [goldenNorm, goldenMul]
  ring
```

である。

したがって依存順の次は **0174 `goldenNorm_mul`** とする。

0172–0173 で representation bridge を閉じたあと、0174 では黄金ノルムが単なる二次形式ではなく、環乗法と整合する乗法的不変量であることを証明する段階へ進む。