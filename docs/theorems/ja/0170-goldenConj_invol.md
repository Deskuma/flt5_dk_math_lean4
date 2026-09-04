# 0170 — `goldenConj_invol`

## Lean の型

```lean
/-- Conjugation is an involution. -/
theorem goldenConj_invol (x : GoldenInt) :
    goldenConj (goldenConj x) = x := by
  ext <;> simp [goldenConj]
```

これは `theorem` であり、黄金整数上の共役 `goldenConj` を二回適用すると元の値へ戻ることを示す。

## 数学的主張または宣言の意味

0163 の共役は

```lean
def goldenConj (x : GoldenInt) : GoldenInt :=
  ⟨x.fst + x.snd, -x.snd⟩
```

と定義されている。

`GoldenInt` の元を

$$
x=a+b\varphi
$$

と読むと、共役は生成元に対して

$$
\varphi\mapsto1-\varphi
$$

と作用し、座標では

$$
(a,b)\mapsto(a+b,-b)
$$

となる。

これをもう一度適用すると、

$$
(a+b,-b)\mapsto((a+b)+(-b),-(-b))=(a,b)
$$

なので、

$$
\overline{\overline{x}}=x
$$

が成立する。本 theorem は、この二次共役が位数2の対称操作であることを任意の `GoldenInt` に対して確立する。

## 証明全体での役割

0166 `goldenConj_phi` では生成元 $\varphi$ が $1-\varphi$ へ送られること、0168 `goldenConj_ofInt` では整数軸が共役で固定されることを確認した。本 theorem はそれらの局所的な挙動を任意の黄金整数へ拡張し、共役が真に involution であることを示す。

これは共役を単なる座標関数ではなく、二次環の非自明な自己対称として扱うための基本性質である。直後の `goldenConj_mul` は共役が乗法を保存することを証明するため、0170 と 0171 を合わせると、後に bundled ring automorphism として表現できる性質の主要部分が揃う。

また、後続の `goldenNorm_conj` や `golden_mul_conj` の数学的背景としても、共役が可逆で自己逆であることは重要である。ただし今回確認した source 近傍では、これらの theorem が `goldenConj_invol` を直接 rewrite に使用しているわけではなく、各々を座標計算で証明している。

## 直接依存する定義・補題

直接依存は次である。

- `GoldenInt`
- 0163 `goldenConj`
- `GoldenInt.ext`
- `GoldenInt` の `fst` / `snd` 座標
- 整数加法と否定に対する `simp` 基本補題

0166 `goldenConj_phi` や 0168 `goldenConj_ofInt` は数学的には前段の具体例だが、Lean proof の直接依存ではない。

依存関係は概念的に

$$
\texttt{goldenConj},\ \texttt{GoldenInt.ext}
\longrightarrow
\texttt{goldenConj_invol}
$$

である。

## 証明または構築の流れ

証明は

```lean
by
  ext <;> simp [goldenConj]
```

だけである。

`ext` により `GoldenInt` の等式を第一座標と第二座標の二つの整数等式へ分解する。`goldenConj` を二回展開すると、第一座標は

$$
(a+b)+(-b)=a
$$

第二座標は

$$
-(-b)=b
$$

となる。

そのため proof flow は

```text
goldenConj (goldenConj x) = x
→ GoldenInt.ext で fst / snd に分解
→ goldenConj を二回展開
→ ℤ の加法・二重否定を simp
→ 両座標が一致
```

となる。

## Lean 固有の処理

`ext` は `GoldenInt.ext` を利用し、structure equality を座標 equality へ還元する。ここでは `cases x` を手動で行う必要がない。

続く `<;>` は生成されたすべての goal に同じ `simp [goldenConj]` を適用する。`simp` は共役の定義を展開し、

```lean
x.fst + x.snd + -x.snd
```

や

```lean
-(-x.snd)
```

を標準整数算術へ正規化する。

本 theorem 自体には `@[simp]` 属性が付いていない。したがって `goldenConj (goldenConj x)` を常に自動簡約したい設計なら `@[simp]` 付与は一つの候補になる。ただし simp set への追加は rewriting の方向と将来の bundled API を考慮して判断すべきである。

## 冗長・重複箇所

数学的内容は `goldenConj` の座標定義から直ちに従うため、証明そのものは非常に短い。一方、この theorem を名前付きで持つ価値は高い。

0166 `goldenConj_phi` と 0168 `goldenConj_ofInt` はそれぞれ生成元と整数軸の挙動を記録しており、本 theorem は全体空間での involution 性を記録する。これらは重複というより、局所 API と大域 API の役割分担である。

より構造化した設計では、共役を `GoldenInt ≃+* GoldenInt` のような ring equivalence として bundle すれば、乗法保存・加法保存・単位保存・全単射性を一つの structure にまとめられる。その場合 `goldenConj_invol` は `symm_apply_apply` 型の一般 theorem から導出できる可能性がある。

## 最適化候補

候補は次である。

1. 現行の `ext <;> simp [goldenConj]` を維持する。
2. `@[simp]` を付与し、二重共役を自動正規化する。
3. `cases x` と `rfl` / `simp` を使う、より低レベルな coordinate proof と比較する。
4. `goldenConj` を additive / multiplicative homomorphism として段階的に bundle する。
5. 最終的に `GoldenInt ≃+* GoldenInt` として共役自己同型を定義し、involution を equivalence API から得る。

現行 proof は短く、座標実装の透明性も高いため、局所的な proof-term 最適化の必要性は低い。最も意味のある最適化は、後続で共役の構造的性質が増える場合の bundled API 化である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自体が必要とするのは、上流の `GoldenInt`、`GoldenInt.ext`、`goldenConj`、整数加法・否定の simplifier infrastructure が中心である。

したがって theorem 単独では `Mathlib` 全体は過剰である可能性が高い。ただし `GoldenOrder` モジュール全体では `CommRing`、`Zsqrtd`、`ring`、`omega`、`norm_num` などを利用しているため、実際の最小 import はモジュール単位の Lean build で検証する必要がある。今回は Lean build を行わないため、最小 import 集合は確定しない。

## Comparator challenge 化の可否

適している。特に「明示座標の一行 proof」と「bundled automorphism」の比較が明瞭である。

比較候補は、

- 現行の `ext <;> simp [goldenConj]`
- `cases x` による直接座標 proof
- `@[simp]` 付き theorem
- additive equivalence としての共役
- ring equivalence としての共役

である。

比較軸は proof-term の短さ、simp normal form、後続 theorem の再利用性、typeclass / structure API との親和性、一般 quadratic-order への拡張可能性である。

特に、座標透明性を維持したまま、どの時点で抽象的な automorphism API へ昇格させるのが最も downstream proof を簡潔にするかを測る良い Comparator challenge になる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `DkMath/FLT/Five/GoldenOrder.lean` generated section である。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在することを確認した。ただし、本 theorem に対応する具体的な PDF ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

Lean source 上で直後に置かれている宣言は

```lean
/-- Conjugation respects multiplication. -/
theorem goldenConj_mul (x y : GoldenInt) :
    goldenConj (goldenMul x y) =
      goldenMul (goldenConj x) (goldenConj y) := by
  ext <;> simp [goldenConj, goldenMul] <;> ring
```

である。

したがって依存順の次は **0171 `goldenConj_mul`** とする。0170 で共役が自己逆であることを確立した後、次は共役が乗法を保存する

$$
\overline{xy}=\overline{x}\,\overline{y}
$$

を証明し、二次共役を環自己同型として理解するための次の主要条件へ進む。