# 0168 — `goldenConj_ofInt`

## Lean の型

```lean
/-- Conjugation fixes the embedded rational integers. -/
@[simp] theorem goldenConj_ofInt (a : ℤ) :
    goldenConj (goldenOfInt a) = goldenOfInt a := by
  ext <;> simp [goldenConj, goldenOfInt]
```

これは `theorem` であり、整数 `a : ℤ` を黄金整数環へ埋め込んだ元 `goldenOfInt a` が、共役 `goldenConj` によって固定されることを示す `@[simp]` 補題である。

## 数学的主張または宣言の意味

0162 で整数埋め込みは

```lean
def goldenOfInt (a : ℤ) : GoldenInt := ⟨a, 0⟩
```

と定義され、0163 の共役は

```lean
def goldenConj (x : GoldenInt) : GoldenInt :=
  ⟨x.fst + x.snd, -x.snd⟩
```

である。

`GoldenInt` の元を $a+b\varphi$ と読むと、共役は

$$
\overline{a+b\varphi}=(a+b)-b\varphi
$$

に対応する。整数埋め込みでは $b=0$ なので、

$$
\overline{a}=a
$$

となる。座標で書けば

$$
(a,0)\longmapsto(a+0,-0)=(a,0).
$$

したがって本 theorem は、非自明な二次共役が基礎環 `ℤ` の埋め込みを点ごとに固定することを、明示座標モデル上で確認している。

## 証明全体での役割

0166 `goldenConj_phi` では生成元が

$$
\overline{\varphi}=1-\varphi
$$

と動くことを示した。一方、本 theorem は整数軸が共役で固定されることを示す。これにより `GoldenInt` の二つの基本方向について、

- 整数部分 $a$ は固定される
- $\varphi$ 成分は非自明に変換される

という共役の構造が明確になる。

この API は、直後の `goldenNorm_ofInt`、さらに `goldenConj_invol`、`goldenConj_mul`、`goldenNorm_conj`、`golden_mul_conj` と続く共役・ノルム層の基礎に位置する。後続証明で整数埋め込みを含む共役式が現れた際、`@[simp]` によって自動的に消去できることも重要である。

今回確認した source では、本 theorem を名前で明示的に `rw` する後続箇所は確認していない。したがって役割は主として simp API と数学的インターフェースの整備である、と評価するのが安全である。

## 直接依存する定義・補題

直接依存は次である。

- `GoldenInt`
- 0162 `goldenOfInt`
- 0163 `goldenConj`
- `GoldenInt.ext`
- 整数加法・否定に対する `simp` 基本補題

0166 `goldenConj_phi` や 0167 `goldenNorm_phi` は数学的には近接しているが、本 theorem の Lean proof はそれらを利用しない。定義を直接展開して座標ごとに閉じている。

## 証明または構築の流れ

証明は

```lean
by
  ext <;> simp [goldenConj, goldenOfInt]
```

である。

`ext` により `GoldenInt` の等式を第一座標・第二座標の等式へ分解する。その後 `goldenConj` と `goldenOfInt` を展開すると、二つの目標は概念的に

$$
a+0=a
$$

と

$$
-0=0
$$

へ落ちる。これらを `simp` が閉じる。

したがって証明の構造は

```text
GoldenInt の等式
→ 座標等式へ extensionality
→ 定義展開
→ ℤ の基本簡約
```

という非常に透明なものになっている。

## Lean 固有の処理

`ext` は上流の

```lean
@[ext] theorem GoldenInt.ext {x y : GoldenInt}
    (hfst : x.fst = y.fst) (hsnd : x.snd = y.snd) : x = y := by
  ...
```

を利用して structure equality を座標 equality へ変換する。

`<;>` は `ext` が生成した全 subgoal に同じ `simp [goldenConj, goldenOfInt]` を適用する。したがって第一・第二座標を個別に記述する必要がない。

また `@[simp]` 属性により、後続の simp は

```lean
goldenConj (goldenOfInt a)
```

を直接

```lean
goldenOfInt a
```

へ正規化できる。これは共役の固定部分環を API 上でも自然な normal form に保つ。

## 冗長・重複箇所

この theorem の内容は `goldenConj` と `goldenOfInt` の定義から直接導出できるため、数学情報としては新規ではない。しかし「整数埋め込みは共役で固定」という事実は二次環の基本 API なので、名前付き `@[simp]` theorem にする価値が高い。

一方、証明中の `ext` は structure equality を明示的に二座標へ分けている。定義展開後に `simp [goldenConj, goldenOfInt]` だけで structure equality 全体を閉じられる可能性もあるが、今回は Lean build を行わないため未検証である。

また `goldenOfInt` と標準 cast `(a : GoldenInt)` は上流の `intCast := fun z => ⟨z,0⟩` と同じ座標規則を持つため、API レベルでは二重化している。raw coordinate API と Mathlib 標準 cast API の橋を明示すると、この重複の意味がより明確になる。

## 最適化候補

候補は次の通りである。

1. 現行の `ext <;> simp [goldenConj, goldenOfInt]` を維持する。
2. `simpa [goldenConj, goldenOfInt]` だけで閉じるか Lean build で確認する。
3. `rfl` が成立するほど定義的に簡約されるか確認する。
4. `goldenOfInt a = (a : GoldenInt)` の bridge theorem を追加し、標準 cast API と raw API を接続する。
5. `goldenConj` を将来的に ring endomorphism / automorphism として束ね、その `map_intCast` 系の一般則から本 theorem を得る設計を比較する。

2 と 3 は今回は未検証である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 単独では、上流の `GoldenInt`、`goldenOfInt`、`goldenConj`、extensionality、`simp` と整数の基本演算が中心的依存である。

したがって、この theorem だけを見れば Mathlib 全体は過剰である可能性が高い。しかし `GoldenOrder` モジュール全体は ring structure、`Zsqrtd`、`ring`、`omega`、`norm_num` など広い機能を利用しているため、実際の最小 import はモジュール全体で検証する必要がある。今回は Lean build を行わないため、具体的な最小 import 集合は未検証とする。

## Comparator challenge 化の可否

適している。小さな theorem なので proof style と API abstraction の差を比較しやすい。

比較候補は、

- 現行の `ext <;> simp`
- `simpa` 一発
- `rfl` が可能か
- 共役を bundled ring hom / automorphism にして一般的な `map_intCast` から導く方式

である。

比較軸は proof term の簡潔さ、定義変更への耐性、simp normal form、必要 import、一般化可能性、後続 theorem での再利用性である。特に「座標実装の透明性」と「抽象 algebra API の再利用性」の trade-off を測る良い Comparator challenge になる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `DkMath/FLT/Five/GoldenOrder.lean` generated section である。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在することを確認した。ただし、本 theorem に対応する具体的な PDF ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

Lean source 上で直後に置かれている宣言は

```lean
/-- The norm of an embedded integer is its square. -/
@[simp] theorem goldenNorm_ofInt (a : ℤ) :
    goldenNorm (goldenOfInt a) = a ^ 2 := by
  simp [goldenNorm, goldenOfInt]
```

である。したがって依存順の次は **0169 `goldenNorm_ofInt`** とする。共役が整数軸を固定することを確認した直後に、同じ整数埋め込みのノルムが平方 $a^2$ になることを API として公開する段階へ進む。