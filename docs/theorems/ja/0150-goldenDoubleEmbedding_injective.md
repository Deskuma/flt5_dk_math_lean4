# 0150 — `goldenDoubleEmbedding_injective`

## Lean の型

```lean
theorem goldenDoubleEmbedding_injective :
    Function.Injective goldenDoubleEmbedding := by
  intro x y h
  have hsnd : x.snd = y.snd := congrArg Zsqrtd.im h
  have hfst : 2 * x.fst + x.snd = 2 * y.fst + y.snd :=
    congrArg Zsqrtd.re h
  apply GoldenInt.ext
  · omega
  · exact hsnd
```

これは `theorem` である。0148 で定義した `goldenDoubleEmbedding : GoldenInt → Zsqrtd 5` が単射であることを証明する。

## 数学的主張・宣言の意味

`GoldenInt` の元を

$$
x=a+b\varphi,\qquad \varphi=\frac{1+\sqrt5}{2}
$$

と書くと、0148 の doubled embedding は

$$
2x=(2a+b)+b\sqrt5
$$

に対応し、座標では

$$
(a,b)\longmapsto(2a+b,b)
$$

である。本 theorem は、この座標変換が情報を失わないことを述べる。

実際、

$$
(2a+b,b)=(2c+d,d)
$$

なら第二座標から $b=d$ が分かる。これを第一座標へ戻すと

$$
2a+b=2c+b
$$

なので $a=c$。したがって元の座標も一致し、$x=y$ となる。

この写像は $x$ そのものを `Zsqrtd 5` に送る通常の環埋め込みではなく、分母 $2$ を払った $2x$ を整数座標へ送るための doubled map である。それでも単射性には十分であり、後続では `Zsqrtd 5` 側で得た零元情報を `GoldenInt` 側へ引き戻すために使われる。

## 証明全体での役割

0148 `goldenDoubleEmbedding` は、黄金整数環を `Zsqrtd 5` の整域的構造へ接続するための補助写像である。0149 では `5` が平方数でないことを `Zsqrtd.Nonsquare 5` instance として供給した。本 theorem はその接続が injective、すなわち元を識別するのに十分な情報を保持していることを保証する。

直後の `goldenDoubleEmbedding_mul` では、黄金整数の積と doubled embedding の積の関係

$$
E(x)E(y)=2E(xy)
$$

が証明される。その後の `GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero` では、`Zsqrtd 5` 側で積が零ならどちらかの因子が零であることを使い、最後に本 theorem の単射性によって

$$
E(x)=E(0)\Longrightarrow x=0
$$

を戻す。したがって本 theorem は、`Zsqrtd 5` の零因子のない性質を `GoldenInt` へ移送する際の「帰路」に当たる。

## 直接依存する定義・補題

直接依存は次の通りである。

- 0148 `goldenDoubleEmbedding`
- `GoldenInt.ext`
- `Function.Injective`
- `Zsqrtd.re`
- `Zsqrtd.im`
- `congrArg`
- `omega`

`goldenDoubleEmbedding` の定義は

```lean
def goldenDoubleEmbedding (x : GoldenInt) : Zsqrtd 5 :=
  ⟨2 * x.fst + x.snd, x.snd⟩
```

であるため、等式 `h : goldenDoubleEmbedding x = goldenDoubleEmbedding y` へ `Zsqrtd.im` と `Zsqrtd.re` をそれぞれ適用すれば、必要な二つの整数座標等式が得られる。

## 証明・構築の流れ

証明は四段階である。

1. `intro x y h` で単射性の定義を開き、二つの `GoldenInt` と embedding 後の等式を受け取る。
2. `congrArg Zsqrtd.im h` により第二座標の等式 `x.snd = y.snd` を得る。
3. `congrArg Zsqrtd.re h` により第一座標の変換後等式 `2*x.fst+x.snd = 2*y.fst+y.snd` を得る。
4. `GoldenInt.ext` で元の等式を二座標の等式へ分解し、第一座標は `omega`、第二座標は `hsnd` で閉じる。

第一座標の `omega` は `hfst` と `hsnd` を局所仮定として利用し、整数線形算術から `x.fst = y.fst` を導く。

## Lean 固有の処理

`Function.Injective goldenDoubleEmbedding` は定義上、

```lean
∀ ⦃a b⦄, goldenDoubleEmbedding a = goldenDoubleEmbedding b → a = b
```

という形なので、`intro x y h` でそのまま展開できる。

`congrArg` は等式の両辺へ同じ関数を適用する標準的な congruence 操作である。ここでは `Zsqrtd.im` と `Zsqrtd.re` を使うことで、structure 全体の等式から座標等式だけを安全に取り出している。

最後の `apply GoldenInt.ext` は `GoldenInt` の structure equality を `fst` と `snd` の二つの goal に変換する。`omega` は整数上の線形算術に適しており、係数 `2` を含む第一座標等式と `hsnd` の組から目的を自動で導く。

## 冗長・重複箇所

`hsnd` と `hfst` を個別に作る部分は、数学的には embedding equality の二座標展開を手書きしているため多少の定型性がある。しかし、この明示性により「どの座標が何を保持しているか」が非常に読みやすい。

また `GoldenInt.ext` と `Zsqrtd.re/im` の両方を使うため、source type と target type の二つの extensionality 層を手動で渡っている。ただし本 theorem は短く、抽象化しすぎると doubled embedding の仕組みがかえって見えにくくなる。

## 最適化候補

第一候補は現行のままである。証明は短く、数学的構造も明瞭である。

別案として、`goldenDoubleEmbedding` を単なる関数ではなく加法準同型や線形写像として包装し、その `ker = ⊥` から injectivity を得る設計も考えられる。しかし後続で必要なのは主に injectivity と特殊な乗法関係であり、通常の ring hom ではないため、抽象化の利益は限定的である。

第一座標の `omega` をより手動の整数消去で置き換えることも可能だが、現行は「線形算術」という本質を正確に自動化しており、むしろ保守性が高い。最適化するなら、将来同型や additive embedding を構築する必要が出た時点で structure 化するのが自然である。

## 必要な Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem が直接利用するのは `Function.Injective`、`congrArg`、`Zsqrtd` の座標 API、`omega` tactic、および上流で定義済みの `GoldenInt` / `goldenDoubleEmbedding` / `GoldenInt.ext` である。

したがって modular source では、`GoldenOrder` の上流依存に加え `Zsqrtd` を提供する Mathlib module と `omega` tactic を提供する import に絞れる可能性がある。ただし今回 Lean build は行わないため、Mathlib v4.33.0 系での厳密な最小 import 集合は未検証である。具体的な module 名の削減は build による確認を伴う import audit として行うべきである。

## Comparator challenge 化の可否

適している。小さいが、次の三方式を比較できる。

- 現行の `congrArg re/im` + `GoldenInt.ext` + `omega`
- target 側を `cases` / extensionality で分解して座標を直接処理する方式
- `goldenDoubleEmbedding` を additive hom / linear map 的 structure に昇格し、kernel から injectivity を示す方式

比較軸は、証明行数、definitional unfolding の量、automation 依存、再利用性、後続の zero-divisor transfer との接続のしやすさである。現行方式は抽象度が低い一方、写像 $(a,b)\mapsto(2a+b,b)$ の情報保存構造が最も直接見える。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/GoldenOrder.lean` generated section である。そこでは 0149 `goldenFiveNonsquare` の直後に本 theorem があり、続いて `goldenDoubleEmbedding_mul`、`GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero` と進む。

対象ブランチには `docs/pdf/FLT5-main-ja-v0-r1.pdf` と `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在することも確認した。ただし本補題に対応する具体的ページ番号は今回特定していないため、PDF 上の位置は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
theorem goldenDoubleEmbedding_mul (x y : GoldenInt) :
    goldenDoubleEmbedding x * goldenDoubleEmbedding y =
      (2 : Zsqrtd 5) * goldenDoubleEmbedding (goldenMul x y) := by
  ext <;> simp [goldenDoubleEmbedding, goldenMul] <;> ring
```

である。0150 が doubled embedding の情報保存性を保証したのに対し、次の宣言は黄金整数の乗法と `Zsqrtd 5` 側の乗法を接続する。両者が揃うことで、target 側の零積分解を source 側へ戻す準備が完成する。