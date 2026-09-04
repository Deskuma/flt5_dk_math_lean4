# 0145 — `goldenAddCommGroup`

## Lean の型

```lean
instance goldenAddCommGroup : AddCommGroup GoldenInt := by
  refine
    { sub := goldenSub
      nsmul := @nsmulRec GoldenInt ⟨goldenZero⟩ ⟨goldenAdd⟩
      zsmul := @zsmulRec GoldenInt ⟨goldenZero⟩ ⟨goldenAdd⟩ ⟨goldenNeg⟩
        (@nsmulRec GoldenInt ⟨goldenZero⟩ ⟨goldenAdd⟩)
      add_assoc := ?_
      zero_add := ?_
      add_zero := ?_
      neg_add_cancel := ?_
      add_comm := ?_ } <;>
    intros <;> ext <;> simp [add_comm, add_left_comm]
```

これは theorem ではなく、`GoldenInt` に Lean / Mathlib 標準の `AddCommGroup` 構造を与える named `instance` である。

## 数学的主張・宣言の意味

`GoldenInt` の元を

$$
x=a+b\varphi
$$

と書くと、上流で定義された加法・零元・否定は座標ごとに

$$
(a,b)+(c,d)=(a+c,b+d),
$$

$$
0=(0,0),
$$

$$
-(a,b)=(-a,-b)
$$

として実装されている。したがって `GoldenInt` の加法構造は本質的に整数格子 $\mathbb Z^2$ の座標加法であり、結合則、零元則、逆元則、可換則を満たす。

本 instance はこの事実を `AddCommGroup GoldenInt` として Lean の algebra hierarchy に登録する。ここで扱われるのは黄金比関係 $\varphi^2=\varphi+1$ そのものではなく、黄金整数の基底 $1,\varphi$ に関する加法部分である。

## 証明全体での役割

0133–0144 までで `Zero`、`One`、`Add`、`Neg`、`Sub`、`Mul` に対する座標 projection simp API が整備された。本宣言は、それらのうち加法側の API をまとめて、単なる raw operation 群から正式な可換加法群へ昇格する最初の大きな algebra structure constructor である。

この instance が得られることで、後続では `GoldenInt` に対して一般的な加法群の補題、整数倍、減算、消去則などを標準 API として利用できる。直後の `goldenAddGroupWithOne`、さらに `goldenCommRing` の構築にとっても基礎となる。

特に FLT5 証明全体では、黄金整数上の因数分解・共役・ノルム・整除・Euclidean-domain 構造へ進むために、まず `GoldenInt` が通常の環論 API に参加できる必要がある。本 instance はその additive half を閉じる宣言である。

## 直接依存する定義・補題

直接または実質的に依存するものは次の通りである。

- `GoldenInt`
- `goldenZero`
- `goldenAdd`
- `goldenNeg`
- `goldenSub`
- `GoldenInt.ext`
- `Zero GoldenInt` / `Add GoldenInt` / `Neg GoldenInt` / `Sub GoldenInt`
- 0133–0142 の座標 `@[simp]` projection theorem 群
- `nsmulRec`
- `zsmulRec`
- 標準 `AddCommGroup` 型クラス

`GoldenInt.ext` は構造体等式を `fst` と `snd` の二座標等式へ分解する。そこへ `simp` が `golden_fst_zero`、`golden_snd_zero`、`golden_fst_add`、`golden_snd_add`、`golden_fst_neg`、`golden_snd_neg` などを適用し、最終的に整数上の加法恒等式へ落とす。

## 証明・構築の流れ

証明は `refine` による structure 構築から始まる。

```lean
refine
  { sub := goldenSub
    nsmul := @nsmulRec GoldenInt ⟨goldenZero⟩ ⟨goldenAdd⟩
    zsmul := @zsmulRec GoldenInt ⟨goldenZero⟩ ⟨goldenAdd⟩ ⟨goldenNeg⟩
      (@nsmulRec GoldenInt ⟨goldenZero⟩ ⟨goldenAdd⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ }
```

ここで減算、自然数倍、整数倍の実装を明示し、残る群法則を proof hole として並べる。

その後の

```lean
<;> intros <;> ext <;> simp [add_comm, add_left_comm]
```

が各 law を一括して処理する。

概念的には各 goal に対して、

1. `intros` で変数を導入する。
2. `ext` で `GoldenInt` の等式を `fst` / `snd` の二座標へ分解する。
3. `simp` で黄金整数の演算を整数座標演算へ展開する。
4. 整数の `add_comm`、`add_left_comm` などで正規化して閉じる。

という流れである。

例えば結合則

$$
(x+y)+z=x+(y+z)
$$

は二座標とも単なる整数加法の結合則になる。可換則も同様に各座標の整数加法可換性へ還元される。

## Lean 固有の処理

重要なのは、既存 instance を単純に組み合わせるのではなく `AddCommGroup` の field を明示的に埋めている点である。

`nsmulRec` と `zsmulRec` を明示しているのは、自然数倍・整数倍の実装をこの raw coordinate API に沿った再帰定義へ固定するためである。特に algebra structure の bootstrap 中に、まだ構築途中の instance へ不透明に依存することを避け、依存方向を明確に保っている。

また

```lean
intros <;> ext <;> simp [add_comm, add_left_comm]
```

という tactic chain は複数の structure field goal を同一パターンで処理する Lean 特有の圧縮である。`ext` が `GoldenInt.ext` を利用し、`simp` が直前までに整備された projection theorem 群を rewrite database として使う。

したがって 0133–0144 の小さな `@[simp]` theorem 群は、本宣言で初めてまとまった algebra proof automation として回収される。

## 冗長・重複箇所

数学的には `GoldenInt` の加法は $\mathbb Z\times\mathbb Z$ の componentwise addition と同型なので、群法則を座標ごとに再証明すること自体は既知構造の再構築である。

また `sub := goldenSub`、`nsmul := nsmulRec ...`、`zsmul := zsmulRec ...` を instance 本体で明示するのは、Mathlib の hierarchy が自動補完できる場合と比べると冗長に見える。

しかし現行方式には、

- raw operation と typeclass hierarchy の接続点が明示される
- bootstrap 時の instance search 依存が減る
- `GoldenInt` の algebra structure がどの演算で構成されているか監査しやすい

という利点がある。FLT5 の証明監査という目的では、単なる短縮よりもこの透明性に価値がある。

## 最適化候補

候補は次の通りである。

1. 現行の explicit structure construction を維持する。
2. `GoldenInt` と `ℤ × ℤ` の加法同型を定義し、既存の product `AddCommGroup` を transport する。
3. `GoldenInt` 自体を pair / product に近い表現へ寄せ、加法 instance を既存 instance から得る。
4. `nsmul` / `zsmul` を可能なら hierarchy の既定実装に任せ、明示 field を減らす。
5. `ext <;> simp` のための projection theorem 群を generator 的に作り、boilerplate を削減する。

比較上の論点は、コード行数だけではなく definitional transparency、simp normal form、instance search の安定性、後続 `CommRing` 構築の簡潔さである。

## 必要 Mathlib import と import 最適化候補

standalone artifact は

```lean
import Mathlib
```

を利用している。

本 instance で必要になる機能は `AddCommGroup`、`nsmulRec`、`zsmulRec`、`ext`、`simp`、整数の加法群構造などである。したがって theorem 単体で `Mathlib` umbrella import 全体が必須とは考えにくい。

一方で正確な最小 import は、`GoldenInt` の上流定義と tactic support を含めて Lean build で検証する必要がある。今回の作業では Lean build を行わないため、例えば `Mathlib.Algebra.Group.*` 系への縮小可能性は最適化候補としてのみ述べ、確定的な最小 import 名は主張しない。

## Comparator challenge 化の可否

非常に適している。

比較対象として、

- 現行の field-by-field `AddCommGroup` 構築
- `ℤ × ℤ` との additive equivalence からの transport
- product 表現を直接利用する実装

を用意できる。

評価軸は、proof 行数、`rfl` / `simp` で閉じる law の数、instance search の安定性、definitional unfolding の読みやすさ、後続 `AddGroupWithOne` / `CommRing` 構築への影響、representation 変更への耐性である。

小さな projection theorem 単体よりも、本宣言は API 設計と algebra hierarchy 構築の trade-off が明確に表れるため、Comparator challenge として特に価値が高い。

## PDF・Lean source との対応

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。

形式的根拠は `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/GoldenOrder.lean` generated section と、直前の 0144 文書で確認した source 配置である。そこでは `golden_snd_mul` の直後に本 `goldenAddCommGroup` が置かれ、続いて `goldenAddGroupWithOne`、`goldenCommRing` へ進む。

ただし、本 instance に対応する PDF の具体的ページ・節は今回直接特定していないため、PDF 上の位置は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
instance goldenAddGroupWithOne : AddGroupWithOne GoldenInt :=
  { goldenAddCommGroup with
    natCast := fun n => ⟨n, 0⟩
    intCast := fun z => ⟨z, 0⟩ }
```

である。

本宣言で `GoldenInt` の可換加法群構造が完成した。次は自然数・整数からの標準埋め込みを追加して `AddGroupWithOne` へ昇格し、その後 `goldenCommRing` で乗法を含む完全な可換環構造へ進む。