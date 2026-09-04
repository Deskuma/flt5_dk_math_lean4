# 0172 — `goldenNorm_eq_GoldenNorm`

## Lean の型

```lean
/-- The structure norm is the previously exposed binary golden norm. -/
theorem goldenNorm_eq_GoldenNorm (x : GoldenInt) :
    goldenNorm x = GoldenNorm x.fst x.snd := rfl
```

これは `theorem` であり、`GoldenInt` structure 上の一変数ノルム `goldenNorm` と、より前段から使われている二変数二次形式 `GoldenNorm` が、座標 `x.fst`, `x.snd` を介して定義的に同一であることを示す。

## 数学的主張または宣言の意味

`GoldenInt` の元を

$$
x=a+b\varphi
$$

と読む。上流の `goldenNorm` は

```lean
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

と定義されているので、

$$
N(x)=a^2+ab-b^2
$$

である。

本 theorem は、同じ二次形式を既存 API `GoldenNorm` に座標を渡した

$$
\mathrm{GoldenNorm}(a,b)
$$

と完全に一致させる。

したがって数学的内容は

$$
N(a+b\varphi)=\mathrm{GoldenNorm}(a,b)=a^2+ab-b^2
$$

という「同じノルムの二つの表現の一致」である。新しい数論的事実を導く theorem ではなく、旧 API と新しい structure API の境界を閉じる bridge theorem である。

## 証明全体での役割

`GoldenOrder` では、`GoldenInt` を明示的な二座標 structure として構築し、その上に `goldenConj` と `goldenNorm` を定義している。一方、FLT5 の前段では、整数二変数の二次形式 `GoldenNorm M N` が既に平方・五進・golden bridge の式で使われている。

本 theorem はこの二つを接続する。

```text
既存の二変数 API
GoldenNorm M N
        ↑
        │ fst / snd
        │
structured API
goldenNorm x
```

これにより、前段で得られた `GoldenNorm M N` に関する等式を `GoldenInt` の元 `⟨M,N⟩` のノルムとして読み替えたり、逆に structure 上のノルム計算を既存の二変数定理へ戻したりできる。

直後には、より明示的な座標版

```lean
theorem goldenNorm_eq_existing_GoldenNorm (M N : ℤ) :
    goldenNorm (⟨M, N⟩ : GoldenInt) = GoldenNorm M N := rfl
```

が続く。0172 は任意の `GoldenInt x` に対する一般 bridge、次の宣言は具体的な整数座標 `M,N` を直接受け取る convenience bridge という関係である。

## 直接依存する定義・補題

直接依存は次である。

- `GoldenInt`
- `goldenNorm`
- 既存の二変数二次形式 `GoldenNorm`
- `GoldenInt.fst`
- `GoldenInt.snd`

Lean proof が `rfl` なので、他の theorem や tactic には依存しない。

概念的には

$$
\texttt{goldenNorm},\ \texttt{GoldenNorm}
\longrightarrow
\texttt{goldenNorm_eq_GoldenNorm}
$$

である。

## 証明または構築の流れ

証明は `rfl` 一語だけである。

```lean
:= rfl
```

Lean が左右を展開すると、左辺 `goldenNorm x` は

```lean
x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

となり、右辺 `GoldenNorm x.fst x.snd` も同じ式へ定義展開される。そのため theorem-level rewrite や整数環上の algebra tactic は不要である。

proof flow は

```text
goldenNorm x
→ unfold goldenNorm
→ x.fst^2 + x.fst*x.snd - x.snd^2

GoldenNorm x.fst x.snd
→ unfold GoldenNorm
→ x.fst^2 + x.fst*x.snd - x.snd^2

→ definitional equality
→ rfl
```

となる。

## Lean 固有の処理

`rfl` で閉じることは、両 API が theorem を介して偶然一致しているのではなく、定義そのものが同じ normal form を持つことを意味する。

これは downstream proof にとって重要である。bridge を rewrite に使っても余計な proof burden を導入せず、必要なら両側を直接 unfold しても同じ整数式へ落ちる。

また theorem 名に `eq_GoldenNorm` と大文字の既存 API 名を残すことで、structure 上の lowercase `goldenNorm` と binary form `GoldenNorm` の接続点であることが明瞭になっている。

## 冗長・重複箇所

直後の

```lean
theorem goldenNorm_eq_existing_GoldenNorm (M N : ℤ) :
    goldenNorm (⟨M, N⟩ : GoldenInt) = GoldenNorm M N := rfl
```

は、本 theorem を `x := ⟨M,N⟩` に特殊化すれば得られる内容とほぼ同じである。

したがって API-level では重複がある。

ただし用途は少し異なる。

- `goldenNorm_eq_GoldenNorm` は `GoldenInt` を既に持っている proof に自然。
- `goldenNorm_eq_existing_GoldenNorm` は前段の整数座標 `M,N` から structure 側へ渡る proof に自然。

このため、冗長性はあるが bridge の向きごとに usability を優先した設計と解釈できる。

## 最適化候補

候補は次である。

1. 現行の二つの bridge theorem を維持し、利用側の可読性を優先する。
2. 0172 だけを残し、座標版は `simpa using goldenNorm_eq_GoldenNorm (⟨M,N⟩ : GoldenInt)` で導出する。
3. 逆に座標版だけを基本 theorem とし、structure 版を `x.fst`, `x.snd` により導く。
4. `GoldenNorm` を `GoldenInt` の norm API の唯一の primitive として再設計し、`goldenNorm` を wrapper にする。
5. 一般 quadratic form API を用意し、`GoldenNorm` / `goldenNorm` を同じ抽象定義の specialization にする。

現行 theorem は `rfl` なので局所 proof の最適化余地はほぼない。改善点があるとすれば API の重複整理と命名・module 境界の設計である。

## 必要 Mathlib import と import 最適化候補

本 theorem 単独では tactic を一切使用せず、必要なのは `GoldenInt`、`goldenNorm`、`GoldenNorm` と整数の基本演算だけである。

したがって standalone artifact の `import Mathlib` は、この theorem 単独には明らかに過剰である可能性が高い。

ただし `GoldenOrder` module 全体では `Zsqrtd`、`CommRing`、`omega`、`norm_num`、`ring` などを使用するため、実際の import 削減は module 単位で Lean build により確認すべきである。今回は Lean build を行わないため、具体的な最小 import 集合は未検証とする。

## Comparator challenge 化の可否

適しているが、proof tactic の比較というより API 設計比較に向いている。

比較候補は、

- 現行の structure bridge + coordinate bridge の二本立て
- structure bridge 一本だけ
- coordinate bridge 一本だけ
- `GoldenNorm` を primitive にして `goldenNorm` を wrapper 化
- 一般 quadratic norm abstraction から双方を specialization

である。

比較軸は、

- downstream rewrite の短さ
- theorem 数と API 重複
- simp normal form
- 前段の `GoldenNorm M N` 系 theorem との接続容易性
- `GoldenInt` structure API の読みやすさ
- 一般二次環への再利用性

である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `DkMath/FLT/Five/GoldenOrder.lean` generated section である。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在することを確認した。ただし、本 theorem に対応する具体的な PDF ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

Lean source 上で直後に置かれている宣言は

```lean
/-- Compatibility between the structured norm and the earlier binary quadratic form. -/
theorem goldenNorm_eq_existing_GoldenNorm (M N : ℤ) :
    goldenNorm (⟨M, N⟩ : GoldenInt) = GoldenNorm M N := rfl
```

である。

したがって依存順の次は **0173 `goldenNorm_eq_existing_GoldenNorm`** とする。0172 が任意の `GoldenInt` から既存の binary norm API へ橋を架けたのに対し、0173 は既存側で使っていた整数座標 `M,N` を直接 `GoldenInt` へ載せる convenience bridge を公開する。