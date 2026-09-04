# 0200 — `goldenUnit_of_norm_eq_neg_one`

## Lean の型

```lean
theorem goldenUnit_of_norm_eq_neg_one {x : GoldenInt} (h : goldenNorm x = -1) :
    GoldenUnit x := by
  refine ⟨-goldenConj x, ?_, ?_⟩
  · have hm : goldenMul x (-goldenConj x) =
        -(goldenMul x (goldenConj x)) := by
      change x * (-goldenConj x) = -(x * goldenConj x)
      exact mul_neg _ _
    rw [hm, golden_mul_conj, h]
    rfl
  · have hc : goldenMul (-goldenConj x) x =
        goldenMul x (-goldenConj x) := by
      change (-goldenConj x) * x = x * (-goldenConj x)
      exact mul_comm _ _
    rw [hc]
    have hm : goldenMul x (-goldenConj x) =
        -(goldenMul x (goldenConj x)) := by
      change x * (-goldenConj x) = -(x * goldenConj x)
      exact mul_neg _ _
    rw [hm, golden_mul_conj, h]
    rfl
```

これは `theorem` であり、黄金整数 `x` のノルムが `-1` なら、`x` が `GoldenUnit`、すなわち黄金整数環の単元であることを示す。

## 数学的主張

仮定は

$$
N(x)=-1
$$

である。0176 `golden_mul_conj` により

$$
x\overline{x}=N(x)
$$

なので、

$$
x\overline{x}=-1
$$

となる。したがって共役そのものではなく符号を反転した

$$
-\overline{x}
$$

を逆元候補に取れば、

$$
x(-\overline{x})=-(x\overline{x})=-(-1)=1
$$

を得る。`GoldenInt` は可換環なので左側から掛けても同じであり、`-goldenConj x` が両側逆元になる。

## 証明全体での役割

0199 `goldenUnit_of_norm_eq_one` が $N(x)=1$ の場合を扱ったのに対し、本 theorem は $N(x)=-1$ の分岐を埋める。

この直後の `goldenUnit_of_norm_eq_one_or_neg_one` は両者をまとめ、

$$
N(x)=1\ \text{or}\ N(x)=-1
\Longrightarrow
GoldenUnit(x)
$$

を与える。そのさらに後の `goldenNorm_eq_one_or_neg_one_of_unit` が逆向きを証明することで、黄金整数における単元判定

$$
GoldenUnit(x)
\iff
N(x)=\pm1
$$

が完成する。

この判定は `goldenUnit_phi`、`goldenUnit_neg`、`goldenUnit_mul`、`goldenUnit_pow`、最終的な `GoldenRelPrime` の基礎になる。

## 直接依存する定義・補題

直接依存は次の通りである。

- 0198 `GoldenUnit`
- 0163 `goldenConj`
- 0176 `golden_mul_conj`
- `goldenNorm`
- `CommRing GoldenInt` が供給する `mul_neg` と `mul_comm`

概念的には

$$
N(x)=-1
+\bigl(x\overline{x}=N(x)\bigr)
+\text{sign correction}
+\text{commutativity}
\Longrightarrow
x^{-1}=-\overline{x}.
$$

## 証明の流れ

最初に

```lean
refine ⟨-goldenConj x, ?_, ?_⟩
```

として `GoldenUnit` の逆元 witness に `-goldenConj x` を選ぶ。

第一方向では、まず

```lean
have hm : goldenMul x (-goldenConj x) =
    -(goldenMul x (goldenConj x)) := by
  change x * (-goldenConj x) = -(x * goldenConj x)
  exact mul_neg _ _
```

を作り、raw `goldenMul` 上の積を標準環の `mul_neg` による符号外出しへ変換する。

その後

```lean
rw [hm, golden_mul_conj, h]
rfl
```

で

$$
-(x\overline{x})=-N(x)=1
$$

へ落として閉じる。

第二方向では、まず可換性で積の順序を

```lean
have hc : goldenMul (-goldenConj x) x =
    goldenMul x (-goldenConj x) := by
  change (-goldenConj x) * x = x * (-goldenConj x)
  exact mul_comm _ _
```

と揃え、その後第一方向と同じ `hm` を再構築して同じ rewrite を行う。

## Lean 固有の処理

`change` が二度重要な役割を持つ。

1. raw operation `goldenMul` を標準記法 `*` として見せ、`mul_neg` を使う。
2. 左右逆元の順序を標準乗法へ変換し、`mul_comm` を使う。

`rw [hm, golden_mul_conj, h]` の最後で goal は整数的な符号計算を含む定義的等式へ落ちるため、`rfl` で閉じる。

0199 では `simpa` を中心に証明したのに対し、0200 は符号補正が入るため、`mul_neg` を明示した局所 lemma `hm` を置いている点が相違である。

## 冗長・重複箇所

最も明確な重複は `hm` が左右の branch で完全に二度書かれている点である。

```lean
have hm : goldenMul x (-goldenConj x) =
    -(goldenMul x (goldenConj x)) := by
  change x * (-goldenConj x) = -(x * goldenConj x)
  exact mul_neg _ _
```

これは `refine` 前後で一度だけ局所 lemma として作れば再利用できる。

また、`GoldenUnit` が可換環上で両側逆元を要求するため、第二 branch は第一 branch と `mul_comm` から機械的に従う。0199 と同様、Mathlib 標準 `IsUnit` を中心にすればこの重複を一般 API に委譲できる可能性がある。

## 最適化候補

1. **`hm` を一度だけ構築する**
   - 最も局所的で安全な簡約候補。

2. **右逆元等式を先に一つ作る**
   - `have hr : goldenMul x (-goldenConj x) = goldenOne := ...` とし、左逆元は可換性で導く。

3. **0199 と 0200 を共通化する**
   - ノルム値 `s ∈ {1,-1}` と符号補正をまとめる補助 lemma を作れば、二 theorem の構造的重複を減らせる。

4. **`GoldenUnit` を標準 `IsUnit` に寄せる**
   - generic unit API と inverse witness の再利用が期待できる。

5. **共役を `RingEquiv` として bundle する**
   - 既に加法・乗法・冪・involution の性質が揃っているため、unit criterion をより構造的に記述できる。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が直接使う主要な表面は、existential/conjunction 構築、`change`、`rw`、可換環の `mul_neg` と `mul_comm` である。

高度な解析・整数論 API は本 theorem 自身では不要だが、同一 `GoldenDivisibility` module では整数整除、ノルム計算、`norm_num` などを使用するため、module 全体の最小 import はより広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行の explicit witness + 重複 `hm`
- B: `hm` を一度だけ局所化
- C: 右逆元を一度作り、左逆元を可換性で導く
- D: 0199 と 0200 を共通補助 lemma に統合
- E: Mathlib `IsUnit` 中心の実装
- F: 座標を直接展開して inverse equality を証明

比較軸は proof size、raw/standard API crossing の回数、重複度、数学的 provenance、generic API 再利用度、refactor 耐性、監査性である。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

今回 GitHub 上の正本 source で 0200 の全文を確認し、その直後に `goldenUnit_of_norm_eq_one_or_neg_one` が続くことも確認した。

対象ブランチには日本語・英語 PDF が存在するが、本 theorem に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0201 `goldenUnit_of_norm_eq_one_or_neg_one`** である。

```lean
theorem goldenUnit_of_norm_eq_one_or_neg_one {x : GoldenInt}
    (h : goldenNorm x = 1 ∨ goldenNorm x = -1) : GoldenUnit x :=
  h.elim goldenUnit_of_norm_eq_one goldenUnit_of_norm_eq_neg_one
```

0199 と 0200 で norm `1` / `-1` の二分岐が揃ったので、0201 はその論理和を `Or.elim` でまとめ、norm `±1` から unit への方向を完成させる。