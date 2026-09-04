# 0148 — `goldenDoubleEmbedding`

## Lean の型

```lean
def goldenDoubleEmbedding (x : GoldenInt) : Zsqrtd 5 :=
  ⟨2 * x.fst + x.snd, x.snd⟩
```

これは theorem ではなく `def` である。`GoldenInt` の要素を `Zsqrtd 5` 側へ送る明示的な座標写像を定義する。

## 数学的主張・宣言の意味

`GoldenInt` の要素を

$$
x=a+b\varphi
$$

と読み、黄金比生成元を

$$
\varphi=\frac{1+\sqrt5}{2}
$$

と解釈すると、

$$
2x=2a+b+b\sqrt5
$$

である。`goldenDoubleEmbedding` はこの倍化された表示を `Zsqrtd 5` の整数座標

$$
(2a+b,\ b)
$$

として記録する。

したがって名前の `DoubleEmbedding` は重要である。この写像は $x$ 自身をそのまま $\mathbb Z[\sqrt5]$ に送るのではなく、分母 $2$ を払った $2x$ を送る。黄金整数 $\mathbb Z[\varphi]$ と `Zsqrtd 5` の間で基底を変換するための、分母を持たない整数座標写像である。

## 証明全体での役割

`goldenCommRing` により `GoldenInt` が可換環として完成した直後に、この写像が導入される。役割は `GoldenInt` と Mathlib 側の `Zsqrtd 5` を直接同一視することではなく、後続の零因子排除を `Zsqrtd 5` 側へ移すことである。

実際、直後には `goldenFiveNonsquare`、`goldenDoubleEmbedding_injective`、`goldenDoubleEmbedding_mul` が続き、その後

```lean
theorem GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero {x y : GoldenInt}
    (h : x * y = 0) : x = 0 ∨ y = 0 := by
  ...
```

が証明される。つまり流れは概念的に

$$
\mathbb Z[\varphi]
\xrightarrow{\;x\mapsto 2x\;}
\mathbb Z[\sqrt5]
\longrightarrow
\text{zero-divisor control}
$$

である。

standalone source のコメントも、この doubled map は零因子が存在しないことを保証するためにのみ使用すると明示している。したがって本定義は FLT5 の降下本体そのものではなく、黄金整数環を整域・Euclidean-domain 側へ安全に持ち上げるための基礎橋である。

## 直接依存する定義・補題

直接依存するのは次である。

- `GoldenInt`
- `GoldenInt.fst`
- `GoldenInt.snd`
- `Zsqrtd 5`
- 整数の加法・乗法と numeral `2`

本定義自体には theorem-level の依存はない。0147 `goldenCommRing` の直後に置かれているが、定義式だけを見る限り `CommRing GoldenInt` instance を必要としているわけではなく、`GoldenInt` の座標だけで定義可能である。

数学的な背景としては

$$
2(a+b\varphi)=(2a+b)+b\sqrt5
$$

という基底変換に依存する。ただし Lean 定義では `φ` や平方根を展開する証明を経由せず、最初から整数座標式 `⟨2*a+b,b⟩` を採用している。

## 証明・構築の流れ

`def` なので証明 script は存在しない。入力 `x : GoldenInt` の二座標を読み、`Zsqrtd 5` の二座標を直接構成する。

```lean
⟨2 * x.fst + x.snd, x.snd⟩
```

第一座標には $2a+b$、第二座標には $b$ を置く。これだけで分母を払った黄金整数の表現が得られる。

## Lean 固有の処理

`Zsqrtd 5` は二つの整数座標を持つ型として constructor notation `⟨_, _⟩` で構築できるため、写像は極めて透明である。

重要なのは、この段階では `RingHom` や `AlgHom` として package していない点である。実際、後続の乗法互換性は通常の環準同型

$$
f(xy)=f(x)f(y)
$$

ではなく、倍化のため

$$
f(x)f(y)=2f(xy)
$$

という形の `goldenDoubleEmbedding_mul` として別途証明される。したがって `goldenDoubleEmbedding` を無理に標準 `RingHom` interface へ押し込まない設計は数学的にも正しい。

また後続の injectivity 証明では `Zsqrtd.im` と `Zsqrtd.re` に `congrArg` を適用して座標等式を取り出す。つまり本定義は後続証明で unfolding しやすい concrete coordinate map として意図されている。

## 冗長・重複箇所

座標式

$$
(2a+b,b)
$$

は後続の injectivity や multiplication compatibility でも展開されるため、見方によっては同じ線形変換が繰り返し露出する。しかし raw coordinate definition を一箇所に固定し、後続 theorem が `[goldenDoubleEmbedding]` を unfold する構成なので、数学的重複は比較的小さい。

一方で名称 `Embedding` は Lean の `Embedding` structure を意味するものではない。現段階では単なる関数であり、injective であることも次々段の theorem で証明される。この名称上の意味と Lean type 上の意味のずれは、読む側が注意すべき点である。

## 最適化候補

候補は主に三つある。

1. 現行どおり単純な関数として定義し、injectivity と乗法関係を個別 theorem とする。
2. injectivity 証明後に `GoldenInt ↪ Zsqrtd 5` の `Embedding` を別途構築し、単射性を API に載せる。
3. より一般に、判別式 $5$ の二次整数環間の基底変換として線形写像を抽象化する。

`RingHom` 化はそのままでは不適切である。倍化が入るため乗法保存が通常の形では成立せず、後続 source も `f(x)f(y)=2f(xy)` を使う。もし標準的な環埋め込みが必要なら、target を単純な `Zsqrtd 5` ではなく適切な部分環・局所化・分母 $2$ を扱える型へ変更する必要がある。

したがって現行設計は、零因子排除という目的に対してかなり局所的で効率がよい。

## 必要 Mathlib import と import 最適化候補

standalone artifact 全体は `Mathlib` を利用している。本定義自体に必要なのは `GoldenInt` と `Zsqrtd` の型・constructor、および整数算術だけである。

したがって本定義単独のために `Mathlib` 全体を import する必要はないはずである。特に `Zsqrtd` を提供する Mathlib module と、上流の `GoldenInt` 定義を import すれば足りる可能性が高い。

ただし今回 Lean build は行わず、元の modular `GoldenOrder.lean` の import 行もこの run では直接確認していない。そのため最小 import の具体的 module 名については断定せず、import 最適化候補として扱う。

## Comparator challenge 化の可否

適している。比較対象として次が考えられる。

- 現行の raw coordinate function
- injective `Embedding` として package した版
- 一般二次環の基底変換として抽象化した版
- 分母 $2$ を許す target を用いて真の ring embedding を構成する版

比較軸は、後続の零因子証明の短さ、unfolding の透明性、型クラス・構造体の overhead、乗法互換性の表現の自然さ、他の二次環への再利用可能性である。

特に「標準構造へ package するほど良い」とは限らない好例である。今回の目的では倍化写像の非標準的な乗法則をそのまま theorem にした方が証明の意図を明瞭に保てる可能性が高い。

## PDF・Lean source との対応

形式的な正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/GoldenOrder.lean` generated section である。そこでは `goldenCommRing` の直後に本定義が置かれ、module コメントにも doubled map が零因子排除に使われることが記されている。

対象ブランチには `docs/pdf/FLT5-main-ja-v0-r1.pdf` と `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在することも確認した。ただし本定義に対応する具体的な PDF ページ・節は今回直接特定していないため、ページ番号は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
instance goldenFiveNonsquare : Zsqrtd.Nonsquare 5 := by
  refine ⟨fun n h => ?_⟩
  ...
```

である。

`goldenDoubleEmbedding` の target である `Zsqrtd 5` を零因子排除に利用するには、まず $5$ が自然数平方でないことを `Zsqrtd.Nonsquare 5` instance として供給する必要がある。その後 `goldenDoubleEmbedding_injective`、`goldenDoubleEmbedding_mul` を経て、`GoldenInt` 自身の零因子排除へ進む。