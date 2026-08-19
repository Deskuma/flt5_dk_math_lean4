# 0144 — `golden_snd_mul`

## Lean の型

```lean
@[simp] theorem golden_snd_mul (x y : GoldenInt) :
    (x * y).snd =
      x.fst * y.snd + x.snd * y.fst + x.snd * y.snd := rfl
```

これは `GoldenInt` 上の標準乗法 `x * y` の第二座標 `snd` を、整数座標による明示式へ還元する `@[simp]` theorem である。

## 数学的主張・宣言の意味

`GoldenInt` の元を

$$
x=a+b\varphi,\qquad y=c+d\varphi
$$

と書き、生成元が

$$
\varphi^2=\varphi+1
$$

を満たすとする。積を展開すると

$$
(a+b\varphi)(c+d\varphi)=ac+(ad+bc)\varphi+bd\varphi^2
$$

であり、二次関係を代入すると

$$
(a+b\varphi)(c+d\varphi)=(ac+bd)+(ad+bc+bd)\varphi
$$

となる。したがって第二座標、すなわち基底 `φ` の係数は

$$
\operatorname{snd}(xy)=ad+bc+bd
$$

である。本 theorem はこの式を Lean 上で

```lean
(x * y).snd =
  x.fst * y.snd + x.snd * y.fst + x.snd * y.snd
```

として公開する。

0143 `golden_fst_mul` が積の基底 `1` 成分 $ac+bd$ を扱うのに対し、本 theorem は `φ` 成分 $ad+bc+bd$ を扱う。両者が揃うことで `GoldenInt` の乗法は二つの整数多項式として完全に可視化される。

## 証明全体での役割

本 theorem は乗法 projection API の第二半分である。0143 と組み合わせると、黄金整数上の積を含む等式を `fst` と `snd` の整数恒等式へ完全に分解できる。

source では本 theorem の直後に `goldenAddCommGroup`、続いて `goldenAddGroupWithOne`、`goldenCommRing : CommRing GoldenInt` が構築される。`goldenCommRing` の環法則は概ね

```lean
intros <;> ext <;>
simp <;> ring
```

という形で閉じられる。`GoldenInt.ext` が構造体等式を二座標へ分解し、`simp` が 0143 と本 theorem を使って `GoldenInt` の積を整数多項式へ展開し、最後に `ring` が可換環恒等式を処理する。

特に本 theorem は分配法則、結合則、単位元則、可換則などの第二座標側を標準整数環へ橋渡しする。その意味で、単なる表示用 lemma ではなく `CommRing GoldenInt` の構築を短く保つための主要 rewrite interface である。

## 直接依存する定義・補題

直接依存は次の通りである。

- `GoldenInt`
- `goldenMul`
- `Mul GoldenInt` instance

上流の raw multiplication は

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

であり、標準乗法は

```lean
instance : Mul GoldenInt := ⟨goldenMul⟩
```

として登録されている。したがって本 theorem の右辺は `goldenMul` の第二座標そのものである。

数学的背景には $\varphi^2=\varphi+1$ があるが、本 theorem の証明でその関係を別 lemma として呼ぶわけではない。二次還元は `goldenMul` の定義式に既に埋め込まれている。

0143 `golden_fst_mul` は対となる第一座標 projection だが、本 theorem の `rfl` 証明自体は 0143 に依存しない。

## 証明・構築の流れ

証明は

```lean
:= rfl
```

だけで完了する。

`(x * y).snd` を展開すると、概念的には

```text
x * y
→ goldenMul x y
→ ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

となり、第二射影 `snd` を取れば右辺

```lean
x.fst * y.snd + x.snd * y.fst + x.snd * y.snd
```

がそのまま現れる。左右は定義的に同一なので `rfl` で閉じる。

ここでも二次関係の展開を theorem 内で再証明していないことが重要である。数学的複雑さは raw operation の定義時に一度だけ固定され、本 theorem は標準 notation と座標式の definitional bridge に徹している。

## Lean 固有の処理

中心は `@[simp]` と `rfl` の組み合わせである。

`rfl` が成立するため、`x * y` から `goldenMul x y`、さらに第二座標式までの経路は完全に definitional に透明である。

`@[simp]` により、後続 goal 中の

```lean
(x * y).snd
```

は自動的に

```lean
x.fst * y.snd + x.snd * y.fst + x.snd * y.snd
```

へ正規化される。結果として `GoldenInt` 固有の演算は早い段階で消え、整数上の `simp`、`ring`、`omega` などが扱える形へ落ちる。

また、0143 と本 theorem がともに `[simp]` であることで、`ext <;> simp` という二座標 structure に非常に相性の良い proof pattern が成立する。これは後続の `goldenCommRing` 構築を大幅に簡潔化している。

## 冗長・重複箇所

本 theorem の式は `goldenMul` の第二座標定義をそのまま再公開しているため、定義内容としては重複している。また 0143 と二本一組で projection theorem を置くことも、二座標 structure に伴う boilerplate である。

しかし raw `goldenMul` を後続 proof で直接 unfold すると、証明が内部実装へ密結合する。専用 `@[simp]` theorem を置けば、raw representation と algebra proof の間に小さく安定した rewrite API を設けられる。

したがってこの重複は、simp normal form の制御、proof auditability、後続 tactic の安定性のための意図的な API-level duplication と評価できる。

## 最適化候補

候補は次の通りである。

1. 現行どおり `golden_fst_mul` / `golden_snd_mul` を個別に維持する。
2. `x * y = ⟨..., ...⟩` という pair-level theorem を一つ作り、両 projection theorem をそこから導出する。
3. projection theorem を削除し、必要箇所で `simp [goldenMul]` を用いる。
4. 一般二次関係 $\theta^2=p\theta+q$ に対する座標乗法を抽象化し、黄金整数を $p=q=1$ の特殊化として構成する。
5. `AdjoinRoot` や quadratic algebra 系の Mathlib infrastructure に寄せ、一般環構造と座標計算の再利用を増やす。

現行方式は多少の boilerplate と引き換えに `rfl`、単純な simp normal form、短い `CommRing` 構築を得ている。FLT5 証明の監査性を重視するなら、抽象化による行数削減よりもこの透明性の維持を優先する合理性がある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は

```lean
import Mathlib
```

を使用している。

本 theorem 単独では高度な Mathlib theorem を直接使用せず、必要なのは `GoldenInt`、`goldenMul`、`Mul GoldenInt`、整数の加法・乗法、標準 simp infrastructure である。

ただし `GoldenOrder` モジュール全体では直後に `AddCommGroup`、`AddGroupWithOne`、`CommRing` を構築し、`ring` tactic や後続の二次拡大関連 API も利用する。したがって実際の最小 import は theorem 単体ではなくモジュール全体の依存で決まる。

今回は Lean build を行わないため、正確な最小 import 集合は未検証である。`Mathlib` umbrella import からより細かな import へ分割できる可能性はあるが、ここでは最適化候補として明示するに留める。

## Comparator challenge 化の可否

適している。

比較対象として次の方式を用意できる。

- 現行の dedicated `@[simp]` projection theorem
- `simp [goldenMul]` による raw unfold
- pair-level multiplication theorem からの projection
- generic quadratic-order / `AdjoinRoot` ベース実装

評価軸は、`goldenCommRing` の proof 行数、`rfl` で閉じる補題数、simp normal form の安定性、raw representation 変更への耐性、一般化可能性、下流 FLT5 theorem の可読性である。

特に 0144 は $\varphi$ 成分 $ad+bc+bd$ に二次関係の影響が最も明瞭に現れるため、専用座標実装と一般二次環実装の差を比較する Comparator challenge として分かりやすい。

## PDF・Lean source との対応

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。

本 theorem の形式的根拠は `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/GoldenOrder.lean` generated section で確認した。同 source では `goldenMul`、`Mul GoldenInt`、0143 `golden_fst_mul`、本 theorem、`goldenAddCommGroup`、`goldenCommRing` が連続した局所 API として配置されている。

ただし、この小さな projection theorem に対応する PDF の具体的ページ・節は今回直接特定していない。そのため PDF 上のページ番号や叙述位置は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
instance goldenAddCommGroup : AddCommGroup GoldenInt := by
  ...
```

である。

0143–0144 までで乗法の両座標 projection が揃い、零元・単位元・加法・否定・減算・乗法の座標 simp API が一通り完成した。次はこれらの projection theorem と `GoldenInt.ext` を使って、明示的な座標演算が実際に `AddCommGroup GoldenInt` を構成することを証明する段階へ進む。