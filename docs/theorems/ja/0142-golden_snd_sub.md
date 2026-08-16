# 0142 — `golden_snd_sub`

## Lean の型

```lean
@[simp] theorem golden_snd_sub (x y : GoldenInt) :
    (x - y).snd = x.snd - y.snd := rfl
```

これは `GoldenInt` 上の減算について、第二座標 `snd` が整数の減算と一致することを公開する `@[simp]` theorem である。

## 数学的主張・宣言の意味

`GoldenInt` の元を

$$
x=a+b\varphi,\qquad y=c+d\varphi
$$

と書けば、減算は

$$
x-y=(a-c)+(b-d)\varphi
$$

である。したがって第二座標、すなわち $\varphi$ の係数は

$$
\operatorname{snd}(x-y)=b-d
$$

となる。本定理はこれを Lean の座標射影として

```lean
(x - y).snd = x.snd - y.snd
```

と表現している。

数学的には自明な座標恒等式だが、形式化上は `GoldenInt` の標準減算記法を整数座標の算術へ落とすための公開 rewrite API である。

## 証明全体での役割

0141 `golden_fst_sub` と本 0142 `golden_snd_sub` が揃うことで、`GoldenInt` の減算を両座標とも整数減算へ分解できる。

これは `GoldenInt.ext` と組み合わせた座標証明で重要である。黄金整数同士の等式を第一座標・第二座標へ分解した後、`simp` が減算を通常の整数演算へ正規化できるため、加法群や環の法則を座標ごとの標準算術へ還元できる。

さらに standalone source の後段では、Euclidean division に用いる `goldenRemainder` の第二座標を有理数へ cast して整理する箇所で、`simp only` の明示的な rewrite 集合に `golden_snd_sub` が実際に含まれている。したがって本定理は単なる表示用補題ではなく、後続の norm-Euclidean 証明でも直接利用される API である。

## 直接依存する定義・補題

直接の依存は次の通りである。

- `GoldenInt`
- `goldenNeg`
- `goldenAdd`
- `goldenSub`
- `Sub GoldenInt` instance

raw subtraction は

```lean
def goldenSub (x y : GoldenInt) : GoldenInt :=
  goldenAdd x (goldenNeg y)
```

であり、`goldenNeg` は座標ごとの否定として定義される。したがって第二座標では定義的に

$$
x_{\mathrm{snd}}+(-y_{\mathrm{snd}})=x_{\mathrm{snd}}-y_{\mathrm{snd}}
$$

となる。

0141 `golden_fst_sub` は数学的には対になる補題だが、本定理の証明そのものが 0141 を rewrite として使用するわけではない。両者は同じ raw definition から独立に `rfl` で得られる。

## 証明・構築の流れ

証明は

```lean
:= rfl
```

のみで完了する。

Lean が左辺 `(x - y).snd` を展開すると、概念的には

```text
x - y
→ goldenSub x y
→ goldenAdd x (goldenNeg y)
→ ⟨x.fst + (-y.fst), x.snd + (-y.snd)⟩
```

へ進み、その第二座標は `x.snd + (-y.snd)` になる。整数上では subtraction の定義と一致するため、右辺 `x.snd - y.snd` と定義的に同一となり `rfl` で閉じる。

つまりこの theorem は新しい数学的事実を導出するというより、上流のデータ設計が標準減算と完全に整合していることを定義的等価性で公開している。

## Lean 固有の処理

重要なのは `@[simp]` と `rfl` の組み合わせである。

`rfl` が通ることは、標準記法 `x - y` と raw operation `goldenSub x y` の間に追加の証明層がなく、第二座標まで definitional に透明であることを示す。

`@[simp]` により、後続の証明では

```lean
(x - y).snd
```

が自動的に

```lean
x.snd - y.snd
```

へ正規化される。これにより `GoldenInt` 固有の構造を早い段階で消し、`Int` 上の標準 simplifier、`ring`、cast 補題へ処理を渡せる。

後段の Euclidean division 証明で `simp only [goldenRemainder, goldenMul, golden_snd_sub, Int.cast_sub, ...]` のように明示指定されている点は、この theorem が simp database の便利補題であるだけでなく、局所的 rewrite contract としても使われていることを示している。

## 冗長・重複箇所

0141 `golden_fst_sub` と 0142 `golden_snd_sub` は形がほぼ同一であり、二座標 structure に由来する意図的な重複である。

また `goldenSub` を直接 unfold すれば同じ結果を得られるため、理論上は本 theorem 自体を省略することもできる。しかしその場合、後続証明が `goldenSub`、`goldenAdd`、`goldenNeg` の内部実装へ依存しやすくなる。

専用 projection theorem を置くことで、raw implementation と downstream proof の間に小さな安定 API を形成しているため、この重複には実用上の意味がある。

## 最適化候補

候補は次の通りである。

1. 現行どおり `fst` / `snd` の projection theorem を個別に維持する。
2. 二座標をまとめる pair-level theorem を作り、個別補題をそこから導出する。
3. `goldenSub` を常に unfold して個別 projection theorem を削除する。
4. より一般的な product / quadratic-order abstraction から座標減算補題を自動生成する。

この規模では現行方式が最も透明である。各 theorem が `rfl` で済み、simp lemma としての向きも明確だからである。

一方、同型の二座標補題が今後大量に増えるなら、生成・抽象化によって boilerplate を減らす余地はある。ただし abstraction によって definitional transparency を失うなら、FLT5 証明の監査性との trade-off を評価する必要がある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は

```lean
import Mathlib
```

を使用している。

本定理単独では高度な Mathlib theorem を直接利用せず、必要なのは `GoldenInt` とその上流の減算定義・instance、および標準整数減算である。そのため、この theorem だけを理由に `Mathlib` 全体を import する必要はないと考えられる。

ただし実際の `GoldenOrder` モジュールでは後続の `AddCommGroup`、`CommRing`、`ring` tactic、二次拡大関連の構造なども利用する。今回 Lean build は行わないため、正確な最小 import 集合は未検証である。したがって import 分割は最適化候補であり、確定事項ではない。

## Comparator challenge 化の可否

適している。

比較対象として、例えば次の三方式を用意できる。

- 現行の dedicated `@[simp]` projection theorem
- `simp [goldenSub, goldenAdd, goldenNeg]` による raw unfold
- pair-level / generic quadratic-order abstraction からの導出

評価軸は、下流証明の行数、`rfl` の維持率、simp の安定性、内部実装変更への耐性、Euclidean division のような cast を含む証明での rewrite の制御性である。

特に `simp only` を多用する厳密な証明では、専用 projection theorem がある方式と raw unfold 方式の差が明瞭に現れるため、小さいながら良い Comparator challenge になる。

## PDF・Lean source との対応

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。

本 theorem の形式的根拠は `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/GoldenOrder.lean` generated section で確認した。さらに同 standalone source の後段 `GoldenEuclidean.lean` generated section では `golden_snd_sub` が実際に `simp only` の rewrite 集合として使用されている。

ただし、この小さな projection theorem に対応する PDF の具体的ページ・節は今回直接特定していない。そのため PDF 上のページ番号や叙述位置は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
@[simp] theorem golden_fst_mul (x y : GoldenInt) :
    (x * y).fst = x.fst * y.fst + x.snd * y.snd := rfl
```

である。

0141–0142 で減算の両座標 projection が揃った。次からは `goldenMul` に埋め込まれた関係 $\varphi^2=\varphi+1$ が標準乗法 `x * y` の座標式として表面化するため、単なる coordinatewise operation から黄金整数固有の二次環構造へ一段進む。