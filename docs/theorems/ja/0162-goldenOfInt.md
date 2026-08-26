# 0162 — `goldenOfInt`

## Lean の型

```lean
/-- Embed an integer in the golden order. -/
def goldenOfInt (a : ℤ) : GoldenInt := ⟨a, 0⟩
```

これは theorem ではなく `def` であり、整数 `a : ℤ` を黄金整数環 `GoldenInt` の第一基底方向へ埋め込む関数である。

## 数学的主張または宣言の意味

`GoldenInt` の元を

$$
x=a+b\varphi
$$

と読むと、`goldenOfInt a` は

$$
a=a+0\varphi
$$

を表す。したがって整数環 $\mathbb Z$ を黄金整数環 $\mathbb Z[\varphi]$ の定数部分へ送る最も直接的な座標埋め込みである。

0161 `goldenPhi := ⟨0,1⟩` が第二基底方向 $\varphi$ を指定したのに対し、0162 は第一基底方向 $1$ に沿って整数を配置する。これにより、座標表示 $a+b\varphi$ を構成する二本の基本軸が明示的に揃う。

## 証明全体での役割

`goldenOfInt` は、通常の整数算術と黄金整数算術をつなぐ raw API である。`GoldenInt` はすでに `AddGroupWithOne`、`CommRing`、`IsDomain` まで構築され、標準整数 cast も存在するが、この定義はその抽象 cast とは別に、座標として `⟨a,0⟩` を直接指す名前付き入口を提供する。

この明示性は、共役・ノルム・単元・整除・Euclidean-domain 構築などで、通常整数が黄金整数の定数部分として現れる場面を監査しやすくする。抽象 coercion に任せるだけでなく、座標モデルとの対応を固定できる点が重要である。

## 直接依存する定義・補題

直接依存は主に次の通りである。

- `GoldenInt`
- 整数型 `ℤ`
- `GoldenInt.fst`
- `GoldenInt.snd`

構築そのものに theorem は不要で、structure literal `⟨a,0⟩` だけで完了する。

意味論上は、上流の `goldenAddGroupWithOne` が

```lean
intCast := fun z => ⟨z, 0⟩
```

という同じ座標規則を持つため、`goldenOfInt a` と標準 cast `(a : GoldenInt)` は同じ実装思想を共有する。

## 証明または構築の流れ

証明 script は存在しない。

```lean
def goldenOfInt (a : ℤ) : GoldenInt := ⟨a, 0⟩
```

と直接構築するだけである。

数学的には

$$
\mathbb Z\hookrightarrow\mathbb Z[\varphi],\qquad a\mapsto a+0\varphi
$$

という標準包含を座標化している。

## Lean 固有の処理

`GoldenInt` が二つの整数座標を持つ structure なので、expected type から `⟨a,0⟩` の fields が推論される。

ここで重要なのは、`goldenOfInt` 自身は `Int.cast` の notation ではないことである。標準 cast `(a : GoldenInt)` は上流の `AddGroupWithOne` / `CommRing` instance を通して解決される。一方 `goldenOfInt a` は raw coordinate API として独立した名前を持つ。

両者が同じ座標式を採用しているため、将来的に `@[simp] theorem golden_ofInt_eq ...` のような bridge を置けば `rfl` で閉じられる可能性が高いが、今回の source でその専用 bridge の存在までは確認していないので推測として扱う。

## 冗長・重複箇所

`goldenOfInt a` と標準 cast `(a : GoldenInt)` は意味的に重複して見える。実際、上流の `intCast` も `⟨z,0⟩` なので、座標式は一致している。

ただし役割は異なる。

- 標準 cast は Mathlib algebra hierarchy の一般 API。
- `goldenOfInt` は黄金整数の明示座標層で使う raw API。

この二層構造は 0156–0160 の `goldenAdd` / `goldenMul` と標準 notation の関係と同じ設計哲学であり、形式化の監査可能性を高めている。

## 最適化候補

1. 現行どおり raw constructor と標準 cast の二層を維持する。
2. `goldenOfInt a = (a : GoldenInt)` を明示する `@[simp]` bridge theorem を追加し、raw API から標準 API への正規化を統一する。
3. `goldenOfInt` を単なる alias にして `(a : GoldenInt)` を返す実装へ変更する。ただし bootstrap 順序や definitional transparency への影響を要検証。
4. 一般 quadratic-order abstraction を導入する場合、基礎環 `ℤ` からの canonical embedding として一般化する。

現行の `⟨a,0⟩` は非常に単純で、座標意味論を一目で確認できる利点が大きい。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用しているが、`goldenOfInt` 単独では `GoldenInt` と整数型・zero literal があれば足りる。

したがって、この宣言単独のために高度な Mathlib import は不要である。`GoldenOrder` module 全体では `Zsqrtd`、ring tactic、`omega`、`norm_num` などを利用するため、実際の最小 import 集合は module 全体を Lean build して確認する必要がある。今回は build を行わないので、import 削減は候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は例えば次の通りである。

- 現行の raw coordinate 定義 `goldenOfInt a := ⟨a,0⟩`
- 標準 cast `(a : GoldenInt)` のみを使う設計
- 一般 quadratic-order の canonical base-ring embedding
- `AdjoinRoot` / quotient-based implementation における整数埋め込み

比較軸は、`rfl` で閉じる bridge lemma 数、bootstrap の単純さ、simp 正規形、座標展開の透明性、一般化可能性である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる generated `DkMath/FLT/Five/GoldenOrder.lean` section である。0161 文書で確認済みの source 順序では、`goldenPhi` の直後に本 `goldenOfInt` が置かれ、その後 `goldenConj`、`goldenNorm` へ進む。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在することを今回も確認した。ただし、この一行定義に対応する具体的 PDF ページは直接特定していないため、ページ番号は推測しない。

## 次に読むべき宣言

依存順の次は `goldenConj` である。

黄金整数

$$
a+b\varphi
$$

に対して、黄金比の共役 $\varphi' = 1-\varphi$ を作用させる共役写像を座標で定義する段階へ進む。0161 `goldenPhi` と 0162 `goldenOfInt` で基底の二方向が揃ったため、次はその基底上の Galois 的対称性を具体化することになる。