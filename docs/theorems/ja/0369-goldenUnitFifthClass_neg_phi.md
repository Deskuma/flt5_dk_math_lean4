# 0369 `goldenUnitFifthClass_neg_phi`

## 宣言種別

`private theorem`

## Lean コード

```lean
private theorem goldenUnitFifthClass_neg_phi :
    GoldenUnitFifthClass (-goldenPhi) := by
  refine ⟨⟨1, by decide⟩, -goldenOne, ?_⟩
  decide
```

## Lean の型

```lean
goldenUnitFifthClass_neg_phi : GoldenUnitFifthClass (-goldenPhi)
```

この宣言は引数を取らない閉じた命題であり、黄金整数 `-goldenPhi` が `GoldenUnitFifthClass` に属することを証明する。

`private theorem` なので、この補題名はモジュール外の公開 API として使うことを意図していない。役割は `goldenUnitFifthClass_of_unit` の内部で measure-one の基底ケースを閉じることである。

## 数学的主張

`GoldenUnitFifthClass x` は、ある `i : Fin 5` と `delta : GoldenInt` が存在して

$$
x = \varphi^i\delta^5
$$

と書けることを表す。

ここで `x=-\varphi` とすると、この補題は具体的に

$$
-\varphi = \varphi^1(-1)^5
$$

を witness として与える。

5 は奇数なので

$$
(-1)^5=-1,
$$

したがって

$$
\varphi(-1)=-\varphi.
$$

よって `-goldenPhi` は `i=1` の fifth-power class に属する。

## 証明全体での役割

この補題は `GoldenUnitClassification.lean` における黄金 unit の fifth-power class 分類の基底ケースの一つである。

直前までに、measure が 1 の黄金 unit は

$$
1,\quad -1,\quad \varphi,\quad -\varphi
$$

の四つに限られることが証明されている。これらに対して

- `goldenUnitFifthClass_one`
- `goldenUnitFifthClass_neg_one`
- `goldenUnitFifthClass_phi`
- `goldenUnitFifthClass_neg_phi`

の四補題が、それぞれ具体的な fifth-power class witness を与える。

今回の `goldenUnitFifthClass_neg_phi` はその最後の一つであり、後続の `goldenUnitFifthClass_of_unit` の strong induction において `x=-\varphi` の分岐を直接閉じる。

したがって、この補題単独には深い降下論は含まれないが、直前までに構築した measure-one classification と後続の一般 unit classification を接続する有限基底の一部として不可欠である。

## 直接依存する定義・補題

### `GoldenUnitFifthClass`

本 theorem の結論そのもの。

概念的には

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

という形で、黄金 unit を fifth powers を法として 5 sector に分類するための述語である。

### `goldenPhi`

黄金整数環における $\varphi$ の具体的元。

今回分類する対象は `-goldenPhi` である。

### `goldenOne`

黄金整数環の単位元 $1$。

この補題では fifth-power witness として `-goldenOne`、すなわち $-1$ を用いる。

### `Fin 5`

sector 番号を `0,1,2,3,4` に制限する有限型。

今回は

```lean
⟨1, by decide⟩
```

を witness とするので sector は `1` である。

### 黄金整数環上の `Neg`、`Pow`、`Mul`

`-goldenOne`、`(-goldenOne)^5`、`goldenPhi^1 * (-goldenOne)^5` といった具体式の評価に必要である。

## 証明の流れ

証明は二段階だけである。

### 1. existential witness の構築

```lean
refine ⟨⟨1, by decide⟩, -goldenOne, ?_⟩
```

ここで `GoldenUnitFifthClass (-goldenPhi)` の二つの存在量化に対して

```lean
i     := ⟨1, by decide⟩ : Fin 5
delta := -goldenOne
```

を与える。

数学的には

$$
i=1,
\qquad
\delta=-1
$$

を選んでいる。

`by decide` は `1 < 5` という `Fin` の境界条件を決定手続きで証明する。

### 2. 残った具体等式を決定計算で閉じる

残るゴールは概念的には

$$
-\varphi
=
\varphi^1(-1)^5
$$

である。

Lean コードでは

```lean
decide
```

だけで終了する。

`GoldenInt` は整数座標の具体的構造として定義され、`DecidableEq` を持つため、ここで現れる閉じた等式は計算可能である。したがって一般的な ring 正規化や既存補題の rewrite を明示せずとも、kernel が評価可能な決定手続きにより証明できる。

## Lean 固有の処理

### `Fin 5` の値構築

Lean の `Fin 5` は自然数だけではなく境界証明も保持するので、単なる `1` ではなく

```lean
⟨1, by decide⟩
```

と構築している。

この `decide` は数学的本質ではなく、型に必要な `1 < 5` の証明を自動生成する Lean 固有の処理である。

### `refine` による nested existential の同時構築

`GoldenUnitFifthClass` は二重の存在量化を持つため、

```lean
refine ⟨⟨1, by decide⟩, -goldenOne, ?_⟩
```

によって sector と fifth-power base を一度に埋め、最後の等式だけを metavariable として残している。

### 閉じた等式に対する `decide`

最後の `decide` は、変数を含まない `GoldenInt` の具体的 equality を判定する。

この方法は非常に短く、証明対象が具体値であることを明確に利用している。一方、数学的構造を読み手へ説明するという観点では

```lean
norm_num
```

や定義展開、あるいは `ring` による証明より情報量が少ない。

## 冗長・重複箇所

この theorem 自体の証明は二行であり、局所的な冗長性はほぼない。

ただし周囲には非常によく似た四つの基底補題がある。

```lean
goldenUnitFifthClass_one
goldenUnitFifthClass_neg_one
goldenUnitFifthClass_phi
goldenUnitFifthClass_neg_phi
```

これらはすべて

1. `Fin 5` の具体 sector を選ぶ
2. `goldenOne` または `-goldenOne` を fifth-power witness に選ぶ
3. 閉じた等式を `decide` で証明する

という同一パターンである。

特に

$$
1=\varphi^0 1^5,
\qquad
-1=\varphi^0(-1)^5,
$$

$$
\varphi=\varphi^1 1^5,
\qquad
-\varphi=\varphi^1(-1)^5
$$

という 2×2 の対称構造になっている。

## 最適化候補

### 1. 負号吸収の一般補題

5 が奇数であることを利用して、概念的には

```lean
GoldenUnitFifthClass x → GoldenUnitFifthClass (-x)
```

のような補題を用意できれば、`neg_one` と `neg_phi` はそれぞれ正の基底ケースから導ける可能性がある。

ただし `GoldenUnitFifthClass` の witness `delta` を `-delta` に変更し、5 乗の負号を処理する必要があるので、実際のコード量が減るかは Lean で検証しなければ確定できない。

### 2. measure-one 四ケースの一括補題

四つの private theorem を独立に置く代わりに、measure-one classification の直後で sector witness まで含めた一つの有限分類 theorem に統合する設計も可能である。

一方、現状の分割は `goldenUnitFifthClass_of_unit` の各分岐から意味の明確な名前付き補題を直接参照できるため、可読性上の利点がある。

### 3. `decide` を構造的証明へ置換するか

現在の `decide` は最短であり、保守性も高い。

教育・展示目的で数学的等式を露出したい場合には

$$
(-1)^5=-1
$$

を明示し、`pow_succ`、`ring`、既存の乗法法則などを使う形へ変える余地がある。ただし証明コードとしては現状の方が簡潔である。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

この theorem が直接必要とする機能は概ね次である。

- `Fin`
- `DecidableEq`
- `decide`
- 整数を使う `GoldenInt` の既存定義
- `Neg` / `Mul` / natural power の既存 instance

ただし `GoldenInt`、`GoldenUnitFifthClass`、`goldenPhi` などは同一開発内で既に構築された宣言であり、この theorem 単体の「最小 Mathlib import」を standalone から正確に逆算することはできない。

候補としては広い `import Mathlib` より、`Fin`、整数、代数基本構造、決定可能等式を供給する個別 module へ縮小できる可能性が高い。しかし今回は Lean ビルドを行わない条件なので、最小 import の組合せは未確認であり推測として扱う。

## Comparator challenge 化の可否

**可能。特に micro challenge 向き。**

入力として次を与えるだけで独立性の高い小課題になる。

- `GoldenInt` の必要最小限の定義
- `goldenOne`
- `goldenPhi`
- ring / power instance
- `GoldenUnitFifthClass`

ゴールは

```lean
GoldenUnitFifthClass (-goldenPhi)
```

でよい。

難度そのものは低いが、Comparator では

- nested existential witness を正しく構築できるか
- `Fin 5` の境界証明を処理できるか
- 負号を odd fifth power に吸収する witness を見抜けるか
- concrete equality を `decide`、`norm_num`、定義展開などのどの方法で閉じるか

を比較できる。

より意味のある challenge にするなら、先に `goldenUnitFifthClass_phi` だけを与え、一般的な負号保存 lemma を作らせてから `goldenUnitFifthClass_neg_phi` を導かせる構成が適している。

## 技術的意味

この補題の本質は、fifth powers を法とした unit sector において **符号が新しい sector を増やさない** ことの最小具体例である。

5 が奇数であるため

$$
-1=(-1)^5
$$

が fifth power 側へ完全に吸収される。したがって

$$
\varphi
\quad\text{と}\quad
-\varphi
$$

は同じ sector `1` に属する。

同様に

$$
1
\quad\text{と}\quad
-1
$$

は sector `0` に属する。

よって measure-one の四つの unit は、符号を無視した意味では二つの sector `0` と `1` に収まり、残る sector 遷移は `goldenUnitFifthClass_mul_phi` と `goldenUnitFifthClass_mul_phiInv` によって生成される。この有限 sector 構造を strong induction と結合することで、すべての黄金 unit の fifth-power class 分類へ進む。

## 次に読むべき宣言

次は

```lean
theorem goldenUnitFifthClass_of_unit (x : GoldenInt) (hx : GoldenUnit x) :
    GoldenUnitFifthClass x := by
  ...
```

である。

今回までに揃った四つの measure-one 基底補題と、先に証明された strict descent

```lean
goldenUnit_descent
```

および sector 保存補題

```lean
goldenUnitFifthClass_mul_phi
goldenUnitFifthClass_mul_phiInv
```

を `Nat.strong_induction_on` で統合し、任意の黄金 unit が必ず five-sector のいずれかに属することを証明する、`GoldenUnitClassification.lean` の中心定理である。
