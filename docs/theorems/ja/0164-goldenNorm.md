# 0164 — `goldenNorm`

## Lean の型

```lean
/-- The integral norm `N(a+b*φ)=a^2+a*b-b^2`. -/
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

これは theorem ではなく `def` であり、黄金整数 `x = a + bφ` に対する整数値ノルムを明示的な二次形式として定義する。

## 数学的主張または宣言の意味

`GoldenInt` の元を

$$
x=a+b\varphi
$$

と読み、`φ` が

$$
\varphi^2=\varphi+1
$$

を満たすとする。0163 `goldenConj` は

$$
\overline{x}=(a+b)-b\varphi
$$

を表す。したがって積は

$$
x\overline{x}=a^2+ab-b^2
$$

となり、`goldenNorm` はこの整数値を

$$
N(a+b\varphi)=a^2+ab-b^2
$$

として直接座標で定義している。

Lean の式

```lean
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

は、第一座標を `a`、第二座標を `b` とした二次形式をそのまま実装している。

## 証明全体での役割

`goldenNorm` は `GoldenOrder` 以降の算術で最も重要な数値不変量の一つである。0163 で導入した共役を数値へ圧縮し、黄金整数の乗法構造を整数算術へ移す橋になる。

後続では、少なくとも次の性質へ発展する。

- `goldenNorm` の共役不変性
- `goldenNorm` の乗法性
- `x * goldenConj x` と `goldenNorm x` の対応
- `goldenNorm x = ±1` による単元判定
- Euclidean division における remainder の大きさ評価
- `GoldenInt` を Euclidean domain として構築するための measure

したがって本定義は、単なる補助関数ではなく、黄金整数の「サイズ」と「可逆性」を整数へ射影する魔核に相当する。

## 直接依存する定義・補題

直接依存は次の通りである。

- `GoldenInt`
- `GoldenInt.fst`
- `GoldenInt.snd`
- 整数の加法・乗法・減法
- 自然数冪 `^ 2`

定義自身は theorem に依存せず、座標から直接整数式を構成する。

意味論上は 0163 `goldenConj` が最重要の直前依存である。`goldenNorm` の式は、共役との積を展開した結果として理解できるためである。

## 証明または構築の流れ

証明 script は存在しない。構築は一行である。

```lean
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

数学的には、`x = a+bφ` に対し

$$
(a+b\varphi)((a+b)-b\varphi)
$$

を展開し、`φ² = φ + 1` を用いて `φ` 成分が消えることから得られる整数

$$
a^2+ab-b^2
$$

を先に定義として固定している。

この方針により、後続 theorem は「ノルムが実際に共役積と一致する」「乗法的である」という方向で検証できる。

## Lean 固有の処理

`goldenNorm` の codomain は `ℤ` であり、`GoldenInt` ではない。したがって後続でノルムを環内部へ戻す場合には `goldenOfInt` や標準 cast が必要になる。

また `^ 2` は整数上の標準冪であり、ここでは `GoldenInt` 側の `goldenPow` とは無関係である。式全体が整数多項式なので、後続の等式証明は `ring` や `nlinarith` と相性がよい。

定義を raw function として置いているため、現時点では一般的な `MonoidHom` や `RingHom` ではない。乗法性は後続 theorem として別途証明される設計である。

## 冗長・重複箇所

`goldenNorm` の定義そのものはほぼ最小であり、冗長性はない。

ただし抽象的には、共役が既に存在するので

$$
N(x)=x\overline{x}
$$

からノルムを定義する設計も可能である。現行実装は逆に、整数二次形式を直接定義し、その後で共役積との一致を証明する。

この重複は意図的と考えられる。座標式を直接持つことで、Euclidean estimate や単元判定を整数算術として扱いやすくなるからである。

## 最適化候補

1. 現行の明示二次形式を維持する。
2. `goldenConj` と積からノルムを定義し、整数値であることを別途抽出する。
3. `goldenNorm` の乗法性を `MonoidHom GoldenInt ℤ` 相当の構造へまとめる。
4. 絶対値 `|goldenNorm x|` を Euclidean measure 用 API として明示的に分離する。
5. 一般 quadratic order に対して trace / norm を抽象化し、黄金整数を特殊化する。
6. `AdjoinRoot` や quadratic algebra の既存 norm API と接続する。

FLT5 の監査性という目的では、現在の二次形式を直接見せる方式は非常に強い。最適化は局所行数より downstream theorem の再利用性で評価すべきである。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 `goldenNorm` 単独なら、`GoldenInt` と整数の基本環演算・冪があれば足り、高度な theorem は必要ない。

一方、後続のノルム乗法性、Euclidean estimate、単元判定では `ring`、`norm_num`、`nlinarith`、絶対値や Euclidean-domain infrastructure が必要になる。今回は Lean build を行わないため、真の最小 import 集合は未検証であり、import 削減は候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通りである。

- 現行の座標二次形式 `a^2 + a*b - b^2`
- 共役積から導く norm
- 一般 quadratic-order norm
- `AdjoinRoot` / quadratic algebra の norm

比較軸は、乗法性 theorem の証明量、共役との整合性、Euclidean estimate の証明量、simp 正規形、一般化可能性、import 依存、後続 FLT5 コード量である。

特に現行方式は数値評価が即座に `ℤ` へ落ちるため、Euclidean-domain 構築との相性を比較する良い challenge になる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる generated `DkMath/FLT/Five/GoldenOrder.lean` section である。0163 `goldenConj` の次に本 `goldenNorm` が置かれている。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在することを確認した。ただし、この定義に対応する具体的 PDF ページは今回直接特定していないため、ページ番号は推測しない。

## 次に読むべき宣言

依存順の次は `golden_phi_sq` である。

```lean
@[simp] theorem golden_phi_sq :
    goldenMul goldenPhi goldenPhi = goldenAdd goldenPhi goldenOne := by
  rfl
```

`goldenNorm` で数値不変量を導入した直後、次は黄金比の基本関係

$$
\varphi^2=\varphi+1
$$

を Lean theorem として公開し、以後の共役・ノルム算術を支える基礎恒等式へ進む。