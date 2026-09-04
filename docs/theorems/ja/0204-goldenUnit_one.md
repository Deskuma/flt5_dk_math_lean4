# 0204 — `goldenUnit_one`

## Lean の型

```lean
theorem goldenUnit_one : GoldenUnit goldenOne := by
  apply goldenUnit_of_norm_eq_one
  norm_num [goldenNorm, goldenOne]
```

これは `theorem` であり、黄金整数環の乗法単位元 `goldenOne` が `GoldenUnit` であることを示す。

## 数学的主張・宣言の意味

`goldenOne` は黄金整数環の単位元で、座標では

```lean
def goldenOne : GoldenInt := ⟨1, 0⟩
```

に対応する。したがって黄金ノルム

$$
N(a+b\varphi)=a^2+ab-b^2
$$

を適用すると

$$
N(1)=1^2+1\cdot0-0^2=1
$$

となる。

0199 `goldenUnit_of_norm_eq_one` は一般に

$$
N(x)=1\Longrightarrow GoldenUnit(x)
$$

を証明しているため、本 theorem はその最も基本的な具体例である。

もちろん数学的には $1\cdot1=1$ なので、`goldenOne` 自身を逆元 witness として `GoldenUnit` を直接構成することもできる。現行 proof はそれを再構成せず、直前までに整備された unit-by-norm API を再利用する。

## 証明全体での役割

0198–0202 で

$$
GoldenUnit(x)\iff N(x)=\pm1
$$

という unit criterion が実質的に完成し、0203 では生成元 $\varphi$ に norm `-1` branch を適用した。0204 は norm `1` branch を単位元自身へ適用する対になる concrete certificate である。

本 theorem は小さいが、後続の `goldenUnit_pow` では自然数帰納法の基底ケースとして直接使われる。すなわち

$$
x^0=1
$$

に対して `goldenUnit_one` が unit 性を供給し、帰納段階では `goldenUnit_mul` を使って unit の冪が unit であることを閉じる。

したがって 0204 は単なる自明な sanity check ではなく、unit closure block の base-case API という明確な役割を持つ。

## 直接依存する定義・補題

現行 proof が直接依存するのは次の通りである。

- 0199 `goldenUnit_of_norm_eq_one`
- 0164 `goldenNorm`
- `goldenOne`
- `norm_num`

概念的な依存は一段だけである。

$$
N(1)=1
\Longrightarrow
GoldenUnit(1)
$$

また、`GoldenUnit` 自体は 0198 で

```lean
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧
    goldenMul eta epsilon = goldenOne
```

と定義されているので、直接証明するなら witness に `goldenOne` を選べばよい。

## 証明の流れ

proof は二段階だけである。

```lean
apply goldenUnit_of_norm_eq_one
```

により goal

```lean
GoldenUnit goldenOne
```

を

```lean
goldenNorm goldenOne = 1
```

へ変換する。

続いて

```lean
norm_num [goldenNorm, goldenOne]
```

で `goldenOne = ⟨1,0⟩` とノルム定義を展開し、閉じた整数計算

$$
1^2+1\cdot0-0^2=1
$$

を処理して終了する。

## Lean 固有の処理

`apply goldenUnit_of_norm_eq_one` は theorem の結論を現在の goal に照合し、暗黙引数 `x` を `goldenOne` に特殊化して、仮定 `goldenNorm goldenOne = 1` を新しい subgoal として残す。

`norm_num [goldenNorm, goldenOne]` は両定義を unfold し、structure projection、整数冪、加減乗算を正規化する。変数を含まない閉じた式なので `ring` や `omega` は不要である。

この proof style は 0203 `goldenUnit_phi` と完全に対称で、具体元のノルムだけを closed computation で確認し、unit 性そのものは一般 theorem に委譲している。

## 冗長・重複箇所

数学的には `1` が unit であることは任意の monoid で自明なので、黄金整数専用 theorem としては重複度が高い。また `GoldenUnit` が Mathlib 標準 `IsUnit` と接続されれば、一般 theorem `isUnit_one` 相当から導ける可能性がある。

現行 API 内でも、`GoldenUnit` の定義を直接使えば

```lean
refine ⟨goldenOne, ?_, ?_⟩
```

として両側の積を閉じる証明が可能である。一方、現行 proof は unit-by-norm criterion の再利用を優先しており、0199 の concrete application example としては一貫している。

さらに `goldenNorm goldenOne = 1` を専用 `@[simp]` theorem として公開すれば、ここでの `norm_num [goldenNorm, goldenOne]` を再計算せずに済む。ただしこの closed computation が他でも頻出するかを見て API 増加とのバランスを取るべきである。

## 最適化候補

1. **直接 witness を構成する**
   - `goldenOne` 自身を逆元として `GoldenUnit` を閉じる。
   - unit-by-norm block への依存を減らせる。

2. **`goldenNorm_one` を公開する**
   - `N(1)=1` の closed computation を再利用可能にする。

3. **`GoldenUnit` と Mathlib `IsUnit` を接続する**
   - 一般 algebra API の unit-one theorem を使える可能性がある。

4. **unit criterion の iff theorem を公開する**
   - `GoldenUnit x ↔ goldenNorm x = 1 ∨ goldenNorm x = -1` があれば、具体 unit 証明を `simp` ベースに寄せやすい。

5. **0203/0204 を concrete unit examples としてまとめる**
   - 数学的には `φ` と `1` の unit certificate が並ぶので、小さな API block として整理すると読みやすい。

現行 proof は十分短く、最適化の主眼は proof 行数より標準 unit API との統合にある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が直接使う Mathlib 表面は主に `norm_num` と基本 tactic machinery だけである。

依存先 `goldenUnit_of_norm_eq_one`、`goldenNorm`、`goldenOne` は同一 generated development の上流宣言である。`GoldenDivisibility.lean` 全体では整数整除、共役、ノルム、ring tactic なども使うため、module 全体の最小 import は本 theorem 単独より広い。

今回は Lean build を行わないので、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 `apply goldenUnit_of_norm_eq_one` + `norm_num`
- B: `GoldenUnit` witness に `goldenOne` を直接与える
- C: `goldenNorm_one` を別 theorem 化して再利用
- D: `IsUnit` bridge 経由で一般 `1` の unit theorem を使う
- E: unit criterion iff を `simp` で使う

比較軸は proof 長、直接依存、数学的自明性の表現、専用 API と標準 Mathlib API の再利用率、将来の refactor 耐性、downstream readability である。

A と B の比較は特に明快で、「既に構築した norm criterion を再利用するか」「単位元の定義的自明性を直接使うか」という proof architecture の違いを測れる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

現在の 0203 日英正本文書では、本 theorem が次宣言として次の形で記録されている。

```lean
theorem goldenUnit_one : GoldenUnit goldenOne := by
  apply goldenUnit_of_norm_eq_one
  norm_num [goldenNorm, goldenOne]
```

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0205 `goldenUnit_neg`** である。

```lean
theorem goldenUnit_neg {x : GoldenInt} (hx : GoldenUnit x) : GoldenUnit (-x) := by
  apply goldenUnit_of_norm_eq_one_or_neg_one
  rw [show goldenNorm (-x) = goldenNorm x by simp [goldenNorm]]
  exact goldenNorm_eq_one_or_neg_one_of_unit hx
```

0203–0204 で具体的な unit の基底例を確認した後、0205 からは unit の演算閉性へ進む。まず $x$ が unit なら $-x$ も unit であることを、ノルムが符号反転で不変であることと unit criterion を用いて示す。