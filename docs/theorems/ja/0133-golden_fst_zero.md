# 0133 — `golden_fst_zero`

## Lean の型

```lean
@[simp] theorem golden_fst_zero : (0 : GoldenInt).fst = 0 := rfl
```

これは `theorem` であり、同時に `@[simp]` 属性を持つ座標射影補題である。

## 数学的主張・宣言の意味

`GoldenInt` は整数対 `⟨a,b⟩` により $a+b\varphi$ を表す。零元は

```lean
def goldenZero : GoldenInt := ⟨0, 0⟩
instance : Zero GoldenInt := ⟨goldenZero⟩
```

として定義・登録されている。

したがって黄金整数の零元 $0=0+0\varphi$ の第一座標は $0$ である。本補題はその事実を標準記法 `(0 : GoldenInt)` に対して公開する。

$$
\operatorname{fst}(0_{\mathbb Z[\varphi]})=0.
$$

## 証明全体での役割

0132 までで `GoldenInt` の raw coordinate operation が Lean 標準の `Zero`、`One`、`Add`、`Neg`、`Sub`、`Mul` に登録された。0133 からは、その標準記法を座標式へ戻すための `@[simp]` 補題群が始まる。

`golden_fst_zero` はその最初の一つであり、後続の `AddCommGroup GoldenInt`、`CommRing GoldenInt`、共役・ノルム・整除関連の証明で、`ext` と `simp` を組み合わせた座標計算を成立させるための基礎となる。

特に `GoldenInt` の構造等式を第一座標・第二座標へ分解した後、零元の第一座標を即座に整数の `0` へ正規化できる点が重要である。

## 直接依存する定義・補題

直接依存は次の三点である。

- `GoldenInt`
- `goldenZero : GoldenInt := ⟨0, 0⟩`
- `instance : Zero GoldenInt := ⟨goldenZero⟩`

数学補題への依存はなく、定義展開のみで成立する。

依存関係は概念的に

$$
\texttt{goldenZero}
\longrightarrow
\texttt{Zero GoldenInt}
\longrightarrow
\texttt{golden\_fst\_zero}
$$

である。

## 証明・構築の流れ

証明本体は

```lean
rfl
```

だけである。

`(0 : GoldenInt)` を typeclass resolution により `goldenZero` へ展開し、さらに

```lean
⟨0, 0⟩.fst
```

を評価すると整数 `0` になる。左右が定義的に同一なので reflexivity で閉じる。

## Lean 固有の処理

ここでは `@[simp]` が重要である。Lean はこの theorem を simplifier の rewrite rule として登録するため、後続証明では

```lean
simp
```

だけで `(0 : GoldenInt).fst` を `0` へ簡約できる。

一方で証明そのものは `simp` を使わず `rfl` である。これは `Zero GoldenInt` の instance が raw definition `goldenZero` に直接接続されており、間に非定義的な証明層がないことを示している。

## 冗長・重複箇所

数学的には `goldenZero := ⟨0,0⟩` を見れば第一座標が `0` であることは自明であり、本補題は情報を新しく追加していない。その意味では定義内容の再公開である。

しかし Lean API としては冗長ではない。標準記法 `0` を使った式を `simp` が座標へ落とすための公開 rewrite lemma として機能するからである。

`golden_fst_zero` と直後の `golden_snd_zero` は対になっており、同じ構造を二座標について繰り返している。この重複は product-like structure の projection API では自然なものである。

## 最適化候補

候補は次の三つである。

1. 現行どおり個別に `@[simp]` theorem を置く。
2. `goldenZero` または `Zero GoldenInt` の定義展開を simp に任せ、専用補題を削除する。
3. `GoldenInt` を既存の product / algebraic structure 上に実装し、標準 projection simp lemma をより多く再利用する。

2 はコード量を減らせる可能性があるが、simp が raw implementation detail をどこまで unfold するかに依存し、API 境界が弱くなる。現行方式は補題数が増える代わりに、simp の公開仕様を明示できる利点がある。

## 必要 Mathlib import と import 最適化候補

standalone source は `import Mathlib` を使用しているが、本 theorem 単独は高度な Mathlib 定理を必要としない。必要なのは structure、`Zero` typeclass、`@[simp]` theorem registration、整数型 `ℤ` といった基礎機能、および上流の `GoldenInt` / `goldenZero` 定義である。

したがって本補題だけを理由に `Mathlib` 全体を import する必要はないと考えられる。ただし実際の `GoldenOrder` モジュールは後続で `AddCommGroup`、`CommRing`、`Zsqrtd`、`ring`、`omega` 等を使用するため、モジュール全体の最小 import は別問題である。Lean build は行っていないため、具体的な最小 import 集合は未検証である。

## Comparator challenge 化の可否

可能だが、単独では小さすぎる。より適切なのは、0133 以降の projection simp lemma 群をまとめて Comparator challenge にすることである。

比較対象としては、

- 個別 `@[simp]` lemma を明示する方式
- raw definitions の unfold に simp を依存させる方式
- product-like generic API を利用する方式

を用意し、`ext <;> simp` で閉じる downstream proof の数、simp trace の複雑さ、実装詳細への依存度を比較できる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/GoldenOrder.lean` generated section である。そこでは `Mul GoldenInt` の直後に本 theorem が置かれ、その後に `golden_snd_zero`、`golden_fst_one` などの projection simp lemma 群が続く。

対象ブランチには日本語版・英語版 PDF が存在することは確認できるが、本 theorem に対応する具体的ページは今回直接特定していない。そのためページ番号や節番号は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
@[simp] theorem golden_snd_zero : (0 : GoldenInt).snd = 0 := rfl
```

である。0133 が零元の第一座標を simp API に登録したのに対し、次は第二座標も同様に `0` へ正規化する。