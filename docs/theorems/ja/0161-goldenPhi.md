# 0161 — `goldenPhi`

## Lean の型

```lean
/-- The basis element `phi`. -/
def goldenPhi : GoldenInt := ⟨0, 1⟩
```

これは theorem ではなく `def` であり、黄金整数環 `GoldenInt` の基底元 $\varphi$ を座標 `⟨0,1⟩` として定義する。

## 数学的主張または宣言の意味

`GoldenInt` の元を

$$
x=a+b\varphi
$$

と読むと、`goldenPhi` は

$$
\varphi=0+1\varphi
$$

そのものを表す。したがって第一座標は $0$、第二座標は $1$ である。

ここまでの 0156–0160 は raw operation を標準 algebra notation へ接続する API bridge 群だった。0161 では抽象化された `CommRing GoldenInt` に対して、黄金整数環固有の生成元を改めて明示する。

## 証明全体での役割

`goldenPhi` は後続の黄金整数算術を具体化する基準点である。source では直後に `goldenOfInt`、`goldenConj`、`goldenNorm` が定義され、さらに

```lean
@[simp] theorem golden_phi_sq :
    goldenMul goldenPhi goldenPhi = goldenAdd goldenPhi goldenOne := by
  decide
```

によって

$$
\varphi^2=\varphi+1
$$

という定義関係が形式化される。

また `goldenConj_phi` では共役が $\varphi\mapsto1-\varphi$ を満たすこと、`goldenNorm_phi` では $N(\varphi)=-1$ が証明される。後続の `goldenUnit_phi` はこのノルム計算を使って $\varphi$ が単元であることを示す。

したがって 0161 は単なる定数名ではなく、黄金整数環の「黄金」部分を Lean の構造へ注入する宣言である。

## 直接依存する定義・補題

直接依存は主に次の通りである。

- `GoldenInt`
- `GoldenInt.fst`
- `GoldenInt.snd`

構築自体には theorem や typeclass inference はほとんど必要なく、structure literal `⟨0,1⟩` だけで完了する。

ただし意味論上は、上流で構築済みの `CommRing GoldenInt` と raw multiplication `goldenMul` が重要である。これらがあることで、`goldenPhi` を単なる座標ベクトルではなく環の生成元として扱える。

## 証明または構築の流れ

証明 script は存在しない。

```lean
def goldenPhi : GoldenInt := ⟨0, 1⟩
```

という直接構築のみである。

数学的には基底 $(1,\varphi)$ における第二基底ベクトルを指定している。

## Lean 固有の処理

`GoldenInt` が二つの整数座標を持つ structure であるため、`⟨0,1⟩` は expected type `GoldenInt` から fields を推論して elaboration される。

`goldenPhi` 自体には `@[simp]` は付いていない。その代わり、後続 theorem が `simp [goldenPhi]` や `norm_num [goldenNorm, goldenPhi]` のように定義を局所展開して使う。

これは `goldenPhi` を常時展開して座標 `⟨0,1⟩` に潰すより、意味のある名前を保ったまま必要な場所だけ展開する設計である。

## 冗長・重複箇所

`⟨0,1⟩` を直接書けば `goldenPhi` は不要に見える。しかし後続の theorem では $\varphi$ そのものを数学的対象として扱うため、専用名を持つ意義は大きい。

特に

- `golden_phi_sq`
- `goldenConj_phi`
- `goldenNorm_phi`
- `goldenUnit_phi`
- `goldenTau_eq_phi_mul_sqrtFive`

などが同じ生成元を共有するため、座標 literal の反復より named constant の方が証明意図を明瞭にする。

## 最適化候補

1. 現行どおり `goldenPhi` を明示的な named constant として維持する。
2. `GoldenInt` の生成元をより一般的な quadratic-order abstraction の generator として定義し、黄金整数を特殊化する。
3. `goldenPhi` の座標 projection lemma、例えば `(goldenPhi).fst = 0`、`(goldenPhi).snd = 1` を追加するか検討する。ただし `simp [goldenPhi]` で十分なら API 増加は不要である。
4. 将来的に `AdjoinRoot` などを使う場合、座標定義 `⟨0,1⟩` と抽象生成元の bridge theorem を設ける。

現行実装は非常に透明で、FLT5 の局所計算を追跡しやすい。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を利用しているが、`goldenPhi` 単独は `GoldenInt` の定義と整数 literal があれば足りる。

したがってこの宣言自体に高度な Mathlib import は不要である。ただし同じ `GoldenOrder` source は `Zsqrtd`、`ring`、`omega`、`norm_num` などを使うため、module 全体の最小 import は別途 Lean build による検証が必要である。今回は build を行わないため、import 削減は候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は例えば次の三方式である。

- 現行の明示座標 `goldenPhi := ⟨0,1⟩`
- 一般 quadratic-order generator の特殊化
- `AdjoinRoot` / quotient-based generator からの bridge

比較軸は、`golden_phi_sq` がどれだけ直接的に証明できるか、共役・ノルム・単元 theorem の proof burden、座標展開の透明性、一般化可能性である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる generated `DkMath/FLT/Five/GoldenOrder.lean` section である。そこでは `golden_pow_eq` の直後に本定義があり、続いて `goldenOfInt`、`goldenConj`、`goldenNorm`、`golden_phi_sq` が並ぶ。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在することも確認した。ただし、この一行定義に対応する具体的ページは今回直接特定していないため、PDF ページ番号は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
/-- Embed an integer in the golden order. -/
def goldenOfInt (a : ℤ) : GoldenInt := ⟨a, 0⟩
```

である。

`goldenPhi` が第二基底方向 $\varphi$ を与えたのに対し、`goldenOfInt` は第一基底方向へ整数を埋め込む。両者が揃うことで、$a+b\varphi$ という座標表示の二本の基本軸が明示される。