# 0195 — `goldenConj_sub`

## Lean の型

```lean
theorem goldenConj_sub (x y : GoldenInt) :
    goldenConj (x - y) = goldenConj x - goldenConj y := by
  calc
    goldenConj (x - y) = goldenConj (x + -y) := by rfl
    _ = goldenConj x + goldenConj (-y) := goldenConj_add _ _
    _ = goldenConj x + -goldenConj y := by rw [goldenConj_neg]
    _ = goldenConj x - goldenConj y := by rw [sub_eq_add_neg]
```

これは `theorem` であり、黄金整数の共役 `goldenConj` が減算を保存することを示す。

## 数学的主張

`GoldenInt` の元を

$$
x=a+b\varphi,\qquad y=c+d\varphi
$$

と書く。本 theorem は

$$
\overline{x-y}=\overline{x}-\overline{y}
$$

を主張する。

0193 `goldenConj_add` で

$$
\overline{x+y}=\overline{x}+\overline{y}
$$

が、0194 `goldenConj_neg` で

$$
\overline{-y}=-\overline{y}
$$

が既に証明されている。したがって

$$
\overline{x-y}
=\overline{x+(-y)}
=\overline{x}+\overline{-y}
=\overline{x}-\overline{y}
$$

と導かれる。

座標定義 `goldenConj (a,b) = (a+b,-b)` を直接展開しても同じ結果になるが、現行 proof は直前の加法・否定保存 theorem を再利用し、より構造的に証明している。

## 証明全体での役割

`GoldenDivisibility.lean` では、元とその共役の共通因子を調べる relative-primality argument が後段に現れる。その際、中心的な式の一つが

```lean
beta - goldenConj beta
```

である。

0191 `goldenDivides_sub` は「共通因子は差も割る」ことを保証し、0195 は「共役が差を保存する」ことを保証する。したがって、この二本は element/conjugate の差を黄金整数の整除・共役 API の両側から扱うための対になる基礎補題である。

また共役 API 全体では、

- 0170 `goldenConj_invol` — involution
- 0171 `goldenConj_mul` — 乗法保存
- 0193 `goldenConj_add` — 加法保存
- 0194 `goldenConj_neg` — 否定保存
- 0195 `goldenConj_sub` — 減算保存

が揃う。これらは `goldenConj` が実質的に環自己同型として振る舞うことを個別 theorem の形で公開している。

## 直接依存する定義・補題

proof が直接使う named theorem は次の二つである。

- 0193 `goldenConj_add`
- 0194 `goldenConj_neg`

加えて、標準の減算展開

```lean
sub_eq_add_neg
```

と、`GoldenInt` の減算が `x + -y` と definitionally 接続されていることに依存する。

型・項の構成上は次にも依存する。

- `GoldenInt`
- 0163 `goldenConj`
- `Sub GoldenInt`
- `Add GoldenInt`
- `Neg GoldenInt`

概念的な依存は

$$
\texttt{goldenConj\_add}
+\texttt{goldenConj\_neg}
\longrightarrow
\texttt{goldenConj\_sub}
$$

である。

## 証明の流れ

現行 proof は `calc` chain で数学的導出をそのまま記述している。

```lean
calc
  goldenConj (x - y) = goldenConj (x + -y) := by rfl
  _ = goldenConj x + goldenConj (-y) := goldenConj_add _ _
  _ = goldenConj x + -goldenConj y := by rw [goldenConj_neg]
  _ = goldenConj x - goldenConj y := by rw [sub_eq_add_neg]
```

1. `x - y` を definitionally `x + -y` と見る。
2. `goldenConj_add` で共役を加法の内側へ分配する。
3. `goldenConj_neg` で `goldenConj (-y)` を `-goldenConj y` に変える。
4. `sub_eq_add_neg` で加法と否定を標準減算記法へ戻す。

0193・0194 と違い、ここでは `ext` や座標展開を行わない。直前までに整備した morphism-like API をそのまま合成している点が特徴である。

## Lean 固有の処理

最初の行

```lean
goldenConj (x - y) = goldenConj (x + -y) := by rfl
```

が `rfl` で閉じるのは、`Sub GoldenInt` が raw subtraction を通じて加法と否定へ definitionally 接続されているためである。

`calc` の `_` は直前の右辺を引き継ぐため、変形の意味が読みやすい。第二段では theorem `goldenConj_add _ _` を直接与え、第三・第四段では `rw` による局所 rewrite を使っている。

特に最後の

```lean
rw [sub_eq_add_neg]
```

は等式の右辺 `goldenConj x - goldenConj y` を加法・否定形へ展開して、左側の `goldenConj x + -goldenConj y` と一致させる。

この proof は tactic automation に強く依存せず、どの algebraic law をどの順番で使っているかが proof term 表面に残る。

## 冗長・重複箇所

0195 は数学的には 0193 と 0194 の組合せから直ちに従うため、独立情報としては冗長である。

また `goldenConj` を `RingHom` または `RingEquiv` として bundle していれば、減算保存は generic theorem `map_sub` に相当する API から自動的に得られる。

一方、後段で差 `beta - goldenConj beta` が実際に重要なため、named theorem `goldenConj_sub` を置くことには実用上の価値がある。downstream が加法・否定へ手動展開せず、直接「共役は差を保存する」と読めるからである。

したがって theorem-level では意図的な API 冗長性、structure-level では bundle 不足という二つの見方ができる。

## 最適化候補

1. **現行 `calc` proof を維持する**
   - 数学的導出と Lean proof がほぼ一対一で、監査性が高い。

2. **`simpa [sub_eq_add_neg]` で短縮する**
   - `goldenConj_add` と `goldenConj_neg` を simp rewrite に使えば一行化できる可能性がある。
   - exact な simp behavior は Lean build 未実施のため未検証。

3. **座標 proof に戻す**
   - `ext <;> simp [goldenConj] <;> ring` のような direct proof も考えられるが、0193・0194 の再利用を失う。

4. **`goldenConj` を `RingHom` として bundle する**
   - `map_add`、`map_neg`、`map_sub`、`map_mul` を generic API で扱える。

5. **`RingEquiv GoldenInt GoldenInt` として bundle する**
   - 0170 `goldenConj_invol` を inverse law として使い、自己同型として共役 API 全体を統合できる。

局所 proof の最適化余地は小さく、最大の改善候補は共役 API 全体の bundle 化である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem が直接使う表面は小さい。

- `calc`
- equality / rewriting
- `sub_eq_add_neg`
- `GoldenInt` の加法・否定・減算
- `goldenConj_add`
- `goldenConj_neg`

`ring`、`norm_num`、整除、ノルム tactic は本 theorem 自身では不要である。

ただし `GoldenDivisibility.lean` module 全体では整除、整数ノルム、unit、relative primality まで扱うため、module 全体の最小 import はより広い。今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行の構造的 `calc` proof
- B: `simpa [sub_eq_add_neg]` を使う短縮 proof
- C: `ext` + `simp` + `ring` の直接座標 proof
- D: `RingHom` 化して generic `map_sub` を利用
- E: `RingEquiv` 化して automorphism API を利用

比較軸は、proof 行数、数学的 provenance、座標実装の可視性、抽象化コスト、downstream 再利用性、refactor 耐性である。

A と C を比較すると、「前段 theorem を再利用する構造証明」と「座標を再計算する証明」の差が明瞭になる。D / E は局所 theorem の短さより、共役 API 全体の設計品質を測る比較になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

正本 source では次の連続した並びを確認できる。

```lean
theorem goldenConj_add (x y : GoldenInt) :
    goldenConj (x + y) = goldenConj x + goldenConj y := by
  ext <;> simp [goldenConj] <;> ring

theorem goldenConj_neg (x : GoldenInt) :
    goldenConj (-x) = -goldenConj x := by
  ext <;> simp [goldenConj, add_comm]

theorem goldenConj_sub (x y : GoldenInt) :
    goldenConj (x - y) = goldenConj x - goldenConj y := by
  calc
    goldenConj (x - y) = goldenConj (x + -y) := by rfl
    _ = goldenConj x + goldenConj (-y) := goldenConj_add _ _
    _ = goldenConj x + -goldenConj y := by rw [goldenConj_neg]
    _ = goldenConj x - goldenConj y := by rw [sub_eq_add_neg]
```

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0196 `goldenConj_pow`** である。

```lean
theorem goldenConj_pow (x : GoldenInt) (n : ℕ) :
    goldenConj (x ^ n) = goldenConj x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ]
      change goldenConj (goldenMul (x ^ n) x) = _
      rw [goldenConj_mul, ih]
      rw [pow_succ, ← golden_mul_eq]
```

0193–0195 で加法群側の互換性が揃った後、0196 は 0171 `goldenConj_mul` を帰納的に繰り返し、共役が自然数冪を保存することを示す。後続の norm / unit / fifth-power arguments で共役を冪の内側へ移すための API になる。