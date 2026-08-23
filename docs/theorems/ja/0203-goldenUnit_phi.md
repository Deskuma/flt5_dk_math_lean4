# 0203 — `goldenUnit_phi`

## Lean の型

```lean
theorem goldenUnit_phi : GoldenUnit goldenPhi := by
  apply goldenUnit_of_norm_eq_neg_one
  norm_num [goldenNorm, goldenPhi]
```

これは `theorem` であり、黄金整数環の生成元 `goldenPhi`、すなわち数学的な $\varphi$ が `GoldenUnit` であることを示す。

## 数学的主張

`goldenPhi` は

```lean
def goldenPhi : GoldenInt := ⟨0, 1⟩
```

であり、$\varphi^2=\varphi+1$ を満たす黄金整数の基底元を表す。

0167 `goldenNorm_phi` では

$$
N(\varphi)=-1
$$

が既に証明されている。0199–0202 の unit-by-norm block により、ノルムが $1$ または $-1$ の黄金整数は単元であるため、本 theorem の数学的内容は

$$
N(\varphi)=-1\Longrightarrow \varphi\in\mathbb Z[\varphi]^\times
$$

という具体例である。

さらに $\varphi^2=\varphi+1$ から

$$
\varphi(\varphi-1)=1
$$

なので、数学的には逆元を $\varphi-1$ と直接書くこともできる。本 Lean proof はその明示的逆元を再構成せず、ノルム判定 API を経由する。

## 証明全体での役割

0198–0202 で一般の unit criterion

$$
GoldenUnit(x)\iff N(x)=\pm1
$$

が実質的に完成した。0203 は、その一般論を最初の具体的な黄金整数へ適用する宣言である。

`goldenPhi` が単元であることは後続の ramification 構造にも意味を持つ。0183 では

$$
\tau=\varphi\sqrt5
$$

が証明されているため、$\tau$ と $\sqrt5$ は単元 $\varphi$ を掛けた差しか持たず、同じ ramified prime direction を表す。この「$\varphi$ は unit」という事実を named theorem にしておくことで、associate / unit-class の議論を明示的に支えられる。

また後続の `goldenUnit_pow` により $\varphi^n$ もすべて unit となり、さらに後段の unit-classification や sector arithmetic で基本単元の冪を扱う土台になる。

## 直接依存する定義・補題

直接の proof dependency は次の通りである。

- 0200 `goldenUnit_of_norm_eq_neg_one`
- 0164 `goldenNorm`
- 0161 `goldenPhi`
- `norm_num`

数学的には 0167 `goldenNorm_phi` が同じ事実 `goldenNorm goldenPhi = -1` を既に公開している。ただし現行 proof はその theorem を直接再利用せず、

```lean
norm_num [goldenNorm, goldenPhi]
```

で座標計算をもう一度行っている。

概念的には

$$
N(\varphi)=-1
\Longrightarrow
GoldenUnit(\varphi)
$$

という一段の適用である。

## 証明の流れ

proof は二段階だけである。

```lean
apply goldenUnit_of_norm_eq_neg_one
```

により goal `GoldenUnit goldenPhi` を

```lean
goldenNorm goldenPhi = -1
```

へ変換する。

続いて

```lean
norm_num [goldenNorm, goldenPhi]
```

で `goldenPhi = ⟨0,1⟩` とノルム式を展開し、

$$
0^2+0\cdot1-1^2=-1
$$

という閉じた整数計算を処理して終了する。

## Lean 固有の処理

`apply goldenUnit_of_norm_eq_neg_one` は theorem の conclusion を現在の goal に合わせ、暗黙引数 `x` を `goldenPhi` に特殊化したうえで、その仮定 `goldenNorm goldenPhi = -1` を新しい subgoal として残す。

`norm_num [goldenNorm, goldenPhi]` は両定義を unfold し、structure projection と整数算術を正規化する。ここでは `ring` や `omega` は不要で、完全に閉じた数値計算である。

重要なのは、proof が 0200 の一般 theorem を再利用しながら、ノルム値だけは concrete coordinates から再計算している点である。

## 冗長・重複箇所

最も明確な重複は、0167 `goldenNorm_phi` が既に

```lean
@[simp] theorem goldenNorm_phi : goldenNorm goldenPhi = -1 := by
  norm_num [goldenNorm, goldenPhi]
```

を証明しているのに、本 theorem が同じ `norm_num` 計算を再実行していることだ。

したがって現行 proof は例えば

```lean
exact goldenUnit_of_norm_eq_neg_one goldenNorm_phi
```

または

```lean
apply goldenUnit_of_norm_eq_neg_one
simpa using goldenNorm_phi
```

のように短縮できる可能性が高い。前者の exact な elaboration は Lean build 未実施のため候補として扱う。

また `GoldenUnit` 自体は Mathlib 標準 `IsUnit` と意味が重なるため、将来 bridge が整備されれば `goldenUnit_phi` も一般 unit API に寄せられる。

## 最適化候補

1. **0167 `goldenNorm_phi` を再利用する**
   - 同じ座標計算の重複を除去できる。

2. **unit criterion の iff theorem を公開する**
   - `GoldenUnit x ↔ goldenNorm x = 1 ∨ goldenNorm x = -1` があれば `simp` ベースで具体的 unit を処理しやすい。

3. **`GoldenUnit` と `IsUnit` を接続する**
   - Mathlib の一般 unit API と associate theory を利用できる。

4. **`goldenPhi` の明示的逆元 theorem を置く**
   - $\varphi^{-1}=\varphi-1$ を直接公開すれば、unit-classification の数学的意味がさらに見えやすくなる。ただし API 増加との比較が必要である。

現行 theorem 自体は短く明快であり、最大の改善点は 0167 の再利用である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem が直接利用する Mathlib 表面は主に `norm_num` と基本 tactic machinery だけである。

ただし依存先 `goldenUnit_of_norm_eq_neg_one`、`goldenNorm`、`goldenPhi` は同一 generated development の上流宣言であり、`GoldenDivisibility.lean` 全体では整数整除・共役・ring tactics なども使用する。

宣言単独の最小 import は Mathlib 全体よりかなり小さい可能性が高いが、今回は Lean build を行わないため未検証であり、module 単位の import 最適化候補として扱う。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 `apply` + `norm_num`
- B: 0167 `goldenNorm_phi` を直接再利用
- C: $\varphi(\varphi-1)=1$ を明示して `GoldenUnit` witness を直接構成
- D: `IsUnit` / generic algebra API を利用
- E: unit criterion の iff theoremを `simp` で使う

比較軸は proof 長、直接依存、数学的 provenance、座標計算の重複、Mathlib 標準 API 再利用率、downstream readability である。

特に A と B の比較は、既に named theorem として公開済みの closed computation を再計算すべきか再利用すべきかを見る小さく明快な Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

正本 source では 0202 の直後に本 theorem、その次に `goldenUnit_one` が置かれている。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0204 `goldenUnit_one`** である。

```lean
theorem goldenUnit_one : GoldenUnit goldenOne := by
  apply goldenUnit_of_norm_eq_one
  norm_num [goldenNorm, goldenOne]
```

0203 が norm `-1` を持つ生成元 $\varphi$ を unit criterion に通したのに対し、0204 は norm `1` を持つ単位元 `1` 自身が unit であることを確認する。続く `goldenUnit_neg`、`goldenUnit_mul`、`goldenUnit_pow` では unit の閉性を順に整備する。