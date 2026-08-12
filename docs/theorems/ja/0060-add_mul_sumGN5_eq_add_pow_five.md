# 0060 — `add_mul_sumGN5_eq_add_pow_five`

## 1. Lean の型

```lean
theorem add_mul_sumGN5_eq_add_pow_five (u v : ℕ) :
    (u + v) * SumGN5 u v = u ^ 5 + v ^ 5 := by
  by_cases h : v ≤ u
  · rw [SumGN5, if_pos h]
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
    subst u
    simp only [Nat.add_sub_cancel_left]
    ring
  · rw [SumGN5, if_neg h]
    have huv : u ≤ v := Nat.le_of_not_ge h
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le huv
    subst v
    simp only [Nat.add_sub_cancel_left]
    ring
```

## 2. 数学的主張

任意の自然数 `u`,`v` に対し、前号で定義した `SumGN5` は第五冪和の正の residual であり、

$$
(u+v)\,\operatorname{SumGN5}(u,v)=u^5+v^5
$$

を満たす。通常の交代符号因数分解

$$
u^5+v^5=(u+v)(u^4-u^3v+u^2v^2-uv^3+v^4)
$$

を、`Nat.sub` を安全に扱う piecewise 表現へ移した等式である。

## 3. 証明全体での役割

sum orientation では `Fermat5Equation u v w` から `u^5+v^5=w^5` を持つ。この定理により

$$
(u+v)\,SumGN5(u,v)=w^5
$$

へ書き換えられ、difference orientation の `gap * GN5 = fifth power` と同じ「carrier × residual = fifth power」という形へ揃う。後続の exact five-adic packet 構成が sum / difference の両方を同じ抽象層で扱える理由の一つである。

## 4. 直接依存する定義・補題

直接のユーザー定義依存は 0059 `SumGN5`。Lean / Mathlib 側では `by_cases`、`Nat.exists_eq_add_of_le`、`Nat.le_of_not_ge`、`Nat.add_sub_cancel_left`、`ring` を使う。

## 5. 証明の流れ

1. `v ≤ u` か否かで `SumGN5` の定義枝に合わせて場合分けする。
2. `v ≤ u` 側では `u = v + d` を得て `u` を置換する。
3. `u-v` が `d` に簡約されるよう `Nat.add_sub_cancel_left` を使う。
4. 残った多項式恒等式を `ring` で閉じる。
5. 反対側では `¬ v ≤ u` から `u ≤ v` を得て `v = u + d` と置き、同じ処理を左右交換して行う。

## 6. Lean 固有の処理

数学的には単なる多項式因数分解だが、`ℕ` では `u-v` が切り詰め減算なので、`ring` に直接渡すだけでは符号付き差として扱えない。そこで順序仮定から `Nat.exists_eq_add_of_le` を使い、差を新変数 `d` に置換してから半環上の純粋な多項式恒等式へ落としている。

`subst u` / `subst v` 後の `simp only [Nat.add_sub_cancel_left]` が、自然数減算という表現上の障害を除去する核心である。

## 7. 冗長・重複箇所

二枝の証明は左右を交換したほぼ同一形である。`SumGN5` 自体が piecewise なので、この重複は定義構造をそのまま追う結果でもある。

## 8. 最適化候補

共通 helper として、`a,d : ℕ` に対する正係数多項式の因数分解補題を一つ証明し、二枝では置換だけ行う形にすれば `ring` の重複を減らせる。あるいは `SumGN5` の対称性補題を先に用意すれば片枝を他方へ移送する設計も可能である。ただし現状は短く、監査時に二つの `Nat.sub` 枝が明示される利点がある。

## 9. 必要 Mathlib import と import 最適化候補

確認できた `Flt5DkMath/FLT5StandAlone.lean` は全体で `import Mathlib` を使用する。今回の定理は特に `ring` tactic と自然数の順序・減算補題を必要とする。元の分割 `SignedFiveAdic.lean` の正確な import 行は対象ブランチでは取得できなかったため、最小 import の具体名は未確認であり推測しない。少なくとも `SumGN5` 単体よりは `ring` 用 import が必要になる。

## 10. Comparator challenge 化の可否

適している。比較案は、A: 現行の二枝 + `ring`、B: 共通 helper 多項式を介する証明、C: `ℤ` 上の標準因数分解から `ℕ` へ移送する証明。比較基準は証明行数、cast 数、`Nat.sub` 補助補題数、import 数、後続再利用性でよい。

## 11. 根拠と推測

確定根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された生成済み `SignedFiveAdic.lean` 部分であり、定理型と証明本体を確認した。既存 PDF の検索は今回 GitHub コネクタの検索系で上流エラーとなったため、PDF のページ番号や本文内容は推測で補っていない。

## 12. 次に読むべき定理

次は

```lean
theorem sumGN5_pos
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    0 < SumGN5 u v
```

である。因数分解恒等式の次に、sum residual が実際に正であることを保証し、後続の five-adic packet に必要な正値条件を供給する。
