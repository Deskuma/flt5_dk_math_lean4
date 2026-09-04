# 0179 — `sqrtFiveElement`

## Lean の型

```lean
/-- Short public name for the element `2φ-1`, whose square is five. -/
abbrev sqrtFiveElement : GoldenInt := goldenSqrtFive
```

これは `theorem` や `def` ではなく `abbrev` である。0177 で定義された `goldenSqrtFive` に対して、下流で使いやすい短い公開名 `sqrtFiveElement` を与える。

## 数学的主張または宣言の意味

0177 では

```lean
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩
```

と定義されている。`GoldenInt` の座標 `⟨a,b⟩` を $a+b\varphi$ と読むと、

$$
goldenSqrtFive=-1+2\varphi=2\varphi-1.
$$

黄金比 $\varphi=(1+\sqrt5)/2$ を用いれば、

$$
2\varphi-1=\sqrt5.
$$

したがって本宣言は新しい元を構成するのではなく、既存の ramified element `goldenSqrtFive` に、数学的意味を前面に出した短い名前 `sqrtFiveElement` を与えるだけである。

`abbrev` なので、`sqrtFiveElement` と `goldenSqrtFive` は単に同値な theorem で結ばれるのではなく、展開可能な同一実装として扱われる。

## 証明全体での役割

0177–0178 で内部的な distinguished elements

- `goldenSqrtFive`
- `goldenTau`

が具体的座標として導入された。0179 とその直後の `tau` は、それらに短い public alias を与える API 整備の層である。

source 上の並びは

```lean
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩
def goldenTau : GoldenInt := ⟨2, 1⟩
abbrev sqrtFiveElement : GoldenInt := goldenSqrtFive
abbrev tau : GoldenInt := goldenTau

theorem goldenSqrtFive_sq :
    goldenMul goldenSqrtFive goldenSqrtFive = goldenOfInt 5 := by
  decide
```

となっている。

したがって本宣言の役割は数学的証明を進めることではなく、ramified element 群を読みやすい API 名で公開することである。直後には

$$
(2\varphi-1)^2=5,
$$

$$
N(2\varphi-1)=-5
$$

を表す theorem 群へ進む。

## 直接依存する定義・補題

直接依存は非常に小さい。

- `GoldenInt`
- 0177 `goldenSqrtFive`

宣言本体は

```lean
abbrev sqrtFiveElement : GoldenInt := goldenSqrtFive
```

だけなので、新しい補題や tactic を必要としない。

数学的意味付けではさらに

- 0161 `goldenPhi`
- 0177 `goldenSqrtFive`

により

$$
sqrtFiveElement=2\varphi-1
$$

と読める。

## 証明または構築の流れ

proof script は存在しない。

1. 0177 で `goldenSqrtFive` が既に構成されている。
2. その値を変更せず、`sqrtFiveElement` という別名を与える。
3. `abbrev` により elaboration 時に透明に展開できる公開 API とする。

したがって数学的な構築は一切追加されない。

## Lean 固有の処理

`abbrev` は通常の `def` よりも reducible な別名として扱われる。ここでは `sqrtFiveElement` が独立した opaque な定義境界を作るのではなく、必要に応じて `goldenSqrtFive` へ容易に展開される。

これは、短い public name を提供しつつ、後続の既存 theorem が `goldenSqrtFive` を使っていても大きな変換コストを発生させない設計である。

一方、source の後続 theorem は現時点では主に内部名 `goldenSqrtFive` を使っている。したがって `sqrtFiveElement` は proof core を置換するというより、公開 API や読みやすさのための façade に近い。

## 冗長・重複箇所

本宣言は意図的な alias なので、値の意味では 0177 `goldenSqrtFive` と完全に重複する。

```lean
sqrtFiveElement
```

と

```lean
goldenSqrtFive
```

は同じ `GoldenInt` を指す。

さらに直後に

```lean
abbrev tau : GoldenInt := goldenTau
```

があり、ramified element 二種について同じ alias pattern が繰り返される。

この重複はコード上の冗長性ではあるが、内部実装名 `goldenSqrtFive` / `goldenTau` と、短い数学記法寄りの public 名 `sqrtFiveElement` / `tau` を分離する意図があるなら合理的である。

## 最適化候補

1. 現行の alias 層を維持し、内部名と公開名の役割を明確に文書化する。
2. downstream theorem 群を `sqrtFiveElement` 側へ寄せ、public API 名を主役にする。
3. 逆に alias がほぼ使われていないなら削除し、`goldenSqrtFive` に一本化する。
4. `sqrtFiveElement` と `tau` を同じ naming policy で整理し、どちらが canonical 名か明示する。
5. 一般 quadratic order で discriminant element / ramified element を bundle し、個別 alias を減らす。

局所的には一行の `abbrev` なので、最適化の焦点は proof performance ではなく API naming と公開面の一貫性である。

## 必要 Mathlib import と import 最適化候補

本 `abbrev` 単独は `GoldenInt` と `goldenSqrtFive` が既に利用可能なら追加の Mathlib theorem や tactic を必要としない。

standalone artifact 全体は `import Mathlib` を使用しているが、本宣言だけを理由に広い import は必要ない。実際の最小 import は `GoldenOrder` module の上流定義に支配される。

今回は Lean build を行わないため、module の最小 import 集合は未検証であり、import 削減は候補としてのみ扱う。

## Comparator challenge 化の可否

小さいが可能である。

比較候補は、

- `abbrev sqrtFiveElement := goldenSqrtFive`
- `def sqrtFiveElement := goldenSqrtFive`
- alias を設けず `goldenSqrtFive` に統一
- 最初から canonical 名を `sqrtFiveElement` として定義し、`goldenSqrtFive` を alias にする

である。

比較軸は、

- definitional transparency
- simp / unfolding の挙動
- エラーメッセージで現れる名前
- API discoverability
- downstream proof の書き換え量
- 内部名と公開名の役割分離

である。

数学そのものを比較する challenge ではなく、Lean library design における `abbrev` / `def` / canonical naming の比較課題として適している。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `GoldenOrder` generated source である。source では 0178 `goldenTau` の直後に本 `abbrev` があり、その次に `tau` alias、さらに `goldenSqrtFive_sq` が続く。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、本 alias に対応する具体的 PDF ページ・節番号は直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は

```lean
/-- Short public name for the distinguished norm-five element `2+φ`. -/
abbrev tau : GoldenInt := goldenTau
```

である。

0179 が `goldenSqrtFive` の短い公開名を与えたのに対し、次の 0180 は 0178 `goldenTau` に短い公開名 `tau` を与える。その後、alias 整備を終えて `goldenSqrtFive_sq` に進み、ramified element の実際の平方・ノルム性質を証明する段階へ戻る。