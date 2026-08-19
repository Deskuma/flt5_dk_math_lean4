# 0136 — `golden_snd_one`

## Lean の型

```lean
@[simp] theorem golden_snd_one : (1 : GoldenInt).snd = 0 := rfl
```

これは `theorem` であり、同時に `@[simp]` 属性を持つ座標射影補題である。

## 数学的主張・宣言の意味

`GoldenInt` は整数対 `⟨a,b⟩` によって黄金整数

$$
a+b\varphi
$$

を表す。Lean source では乗法単位元を raw definition として

```lean
def goldenOne : GoldenInt := ⟨1, 0⟩
instance : One GoldenInt := ⟨goldenOne⟩
```

と定義・登録している。したがって標準記法 `(1 : GoldenInt)` は座標 `⟨1,0⟩` に定義的に還元され、その第二座標は整数 `0` である。本定理は数学的には

$$
\operatorname{snd}(1_{\mathbb Z[\varphi]})=0
$$

すなわち黄金整数環の単位元 $1$ が $\varphi$ 成分を持たないことを述べる。

## 証明全体での役割

0133–0136 は、`Zero GoldenInt` と `One GoldenInt` を標準記法で使ったときの座標を `@[simp]` 補題として公開する最初の projection API 群である。

0135 `golden_fst_one` が単位元の第一座標を `1` に正規化するのに対し、本定理は第二座標を `0` に正規化する。両者を組み合わせることで、`1 : GoldenInt` に関する extensionality 証明では各座標を直接計算する必要がなくなり、`simp` が単位元の座標を自動的に消去できる。

後続の `golden_fst_add`、`golden_snd_add`、加法群構造、環構造の構築では、標準記法を座標計算へ落とす simp infrastructure が重要になる。本定理はその最小単位元側の一部を担う。

## 直接依存する定義・補題

直接依存は次の要素である。

- `GoldenInt`
- `goldenOne : GoldenInt := ⟨1, 0⟩`
- `instance : One GoldenInt := ⟨goldenOne⟩`
- `Prod.snd` に相当する `GoldenInt.snd` の座標射影

論理的には

$$
\texttt{goldenOne}
\longrightarrow
\texttt{One GoldenInt}
\longrightarrow
\texttt{golden\_snd\_one}
$$

という依存である。数学的な補題を介さず、定義展開だけで成立する。

## 証明・構築の流れ

証明は

```lean
:= rfl
```

だけで閉じる。

Lean は `(1 : GoldenInt)` を `One GoldenInt` instance を通して `goldenOne` に展開し、さらに `goldenOne = ⟨1,0⟩` を展開する。すると左辺は `⟨1,0⟩.snd` となり、これは定義的に `0` へ簡約されるため、両辺が同一項となる。

したがって証明の本体は theorem-level の推論ではなく、representation と instance registration が正しく設計されていることそのものにある。

## Lean 固有の処理

この定理には二つの Lean 固有の意味がある。

第一に、`rfl` で閉じることは propositional equality を別補題から導出しているのではなく、左辺と右辺が definitional equality で一致していることを示す。

第二に、`@[simp]` 属性により、今後 `simp` が

```lean
(1 : GoldenInt).snd
```

を自動的に `0` へ正規化できる。これにより `GoldenInt.ext` と組み合わせた座標ごとの証明や、環法則の簡約で単位元の第二座標が残留しにくくなる。

## 冗長・重複箇所

0135 `golden_fst_one` と本定理は同じ `goldenOne = ⟨1,0⟩` の二つの射影を別 theorem として公開しているため、構造的には対になった重複がある。

しかしこれは意図的な API-level duplication である。Lean の simp set は各射影式を個別 rewrite rule として持つ方が単純で予測可能であり、`Prod` 型の等式 `((1 : GoldenInt) = ⟨1,0⟩)` を毎回展開させるより、下流コードでの正規化が明瞭になる。

## 最適化候補

候補は三つある。

1. 現行のように `fst` / `snd` を別々の `@[simp]` theorem として保持する。
2. `goldenOne` の全体等式を一つの simp lemma として公開し、射影 simplification を構造展開に任せる。
3. `GoldenInt` を既存の代数構造に寄せ、標準的な product / quadratic algebra の simp lemma を再利用する。

現行方式は宣言数こそ増えるが、simp の rewrite surface が局所的で、どの座標がどの値へ落ちるかが明示的である。証明監査の容易さを優先するなら妥当な設計である。

## 必要 Mathlib import と import 最適化候補

standalone source は全体として `import Mathlib` を利用している。本定理そのものが必要とする機能は、`GoldenInt`、`One` instance、構造体の射影、`@[simp]` 属性、`rfl` による定義的等価性だけであり、高度な Mathlib theorem は使用しない。

したがって本定理単独のために `Mathlib` 全体を必要とするわけではない。実際の最小 import は `GoldenInt` とその上流定義をどのモジュールへ分離するかに依存する。今回は Lean build を行わないため、具体的な最小 import 集合は未検証であり、ここは最適化候補としての推測である。

## Comparator challenge 化の可否

小さいが可能である。例えば次の三方式を比較できる。

- 現行の個別 `@[simp]` projection theorem
- `goldenOne` 全体を rewrite する一つの simp lemma
- `change` / `rfl` のみで downstream proof ごとに展開する方式

比較軸は、downstream proof の行数、`simp` の安定性、不要な structure 展開の発生、simp trace の読みやすさ、API の発見可能性である。

この宣言単独では数学的難度は低いが、「どの definitional fact を public simp API として固定するか」という Lean ライブラリ設計上の Comparator challenge として有用である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの Lean source と、その直前までの theorem-museum 文書である。対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` も存在する。

ただし本定理のような定義的 projection lemma に対応する PDF の具体的ページ・節番号は今回直接特定していないため、その対応位置は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
@[simp] theorem golden_fst_add (x y : GoldenInt) :
    (x + y).fst = x.fst + y.fst := rfl
```

である。0133–0136 で零元・単位元の二座標に対する simp API が揃い、次からは二項演算 `+` の座標射影へ進む。