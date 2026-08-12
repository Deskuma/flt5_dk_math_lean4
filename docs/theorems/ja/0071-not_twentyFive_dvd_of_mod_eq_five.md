# 0071 — `not_twentyFive_dvd_of_mod_eq_five`

## Lean の型

```lean
private theorem not_twentyFive_dvd_of_mod_eq_five
    {n : ℕ} (hmod : n % 25 = 5) :
    ¬ 25 ∣ n := by
  intro h25
  have hzero : n % 25 = 0 := Nat.mod_eq_zero_of_dvd h25
  omega
```

この宣言は `private` であり、`SignedFiveAdic.lean` 内部で剰余情報 `n % 25 = 5` を「25 では割れない」という非可除性へ変換する局所補題である。

## 数学的主張

自然数 `n` が

$$
n\bmod 25=5
$$

を満たすなら、

$$
25\nmid n
$$

である。

もし逆に $25\mid n$ なら、剰余は $0$ でなければならない。しかし仮定では剰余が $5$ なので矛盾する。

## 証明全体での役割

0068 は `ZMod 25` 上の等式から `n % 25 = 5` を得た。0069–0070 は同じ情報から `5 ∣ n` を取り出した。本補題 0071 は反対側の境界、すなわち

$$
25\nmid n
$$

を取り出す。

したがって 0070 と 0071 を合わせると

$$
5\mid n,\qquad 25\nmid n
$$

となり、直後の `padicValNat_five_eq_one_of_dvd_not_sq` が

$$
v_5(n)=1
$$

へ変換する。

実際の FLT5 証明では difference orientation の `GN5 (w-v) v` と sum orientation の `SumGN5 u v` の双方で本補題が使われ、residual の 5-adic valuation が 1 であることを確定する入力になる。

## 直接依存する定義・補題

- `Nat.mod_eq_zero_of_dvd` — `25 ∣ n` から `n % 25 = 0` を得る。
- `omega` — `hmod : n % 25 = 5` と `hzero : n % 25 = 0` の数値矛盾を閉じる。
- 否定命題 `¬ 25 ∣ n` の導入に使う `intro`。

前号 0070 そのものを証明中に直接呼ぶわけではないが、後続 valuation 補題へ渡す二条件の片方として対になっている。

## 証明の流れ

1. 目標 `¬ 25 ∣ n` に対し、`intro h25` で反対仮定 `25 ∣ n` を置く。
2. `Nat.mod_eq_zero_of_dvd h25` により

   $$
   n\bmod 25=0
   $$

   を得る。
3. 元の仮定

   $$
   n\bmod 25=5
   $$

   と両立しないので、`omega` が矛盾を閉じる。

## Lean 固有の処理

数学的には「25 の倍数の剰余は 0」という一行の議論である。Lean ではこの変換を `Nat.mod_eq_zero_of_dvd` が明示的に担当する。

`omega` は可除性そのものを扱っているのではなく、可除性を剰余等式へ変換した後の

```lean
hmod  : n % 25 = 5
hzero : n % 25 = 0
```

という自然数等式の不整合だけを処理する。そのため証明の数論的データフローは比較的透明である。

## 冗長・重複箇所

証明は 4 行で、論理的重複はほぼない。

ただし最後の `omega` は定数 `0 ≠ 5` の矛盾を処理するには強い。`rw [hmod] at hzero` の後に `norm_num at hzero` とするなど、より局所的な tactic で閉じる余地がある。

また命題は 25 と 5 に固定されているが、本質は一般の modulus `m` と非零 residue `r` に対する

```lean
n % m = r → r ≠ 0 → ¬ m ∣ n
```

という一般 bridge である。

## 最適化候補

第一候補は `omega` をより小さな正規化へ置き換えること。例えば `rw [hmod] at hzero` 後に `norm_num at hzero` とすれば、何を矛盾させているかがさらに明示的になる可能性がある。

第二候補は一般補題化である。`n % m = r` と `r ≠ 0` から `¬ m ∣ n` を得る helper を一つ持てば、25/5 固定の局所補題を薄い特殊化にできる。

第三候補は 0068–0071 の bridge 群を API として整理し、`(n : ZMod 25) = 5` から直接

$$
5\mid n\land 25\nmid n
$$

を返す統合補題を設ける案である。証明本文は短くなるが、現行の分解は各表現変換を一段ずつ監査できる利点がある。

## 必要 Mathlib import と import 最適化候補

生成済み `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用している。本補題自身が直接必要とするのは自然数の剰余・可除性 API と `omega` tactic である。

したがって最小 import 候補は Nat の modular arithmetic と `Mathlib.Tactic.Omega` 相当である。ただし対象ブランチ上では分割元 `DkMath/FLT/Five/SignedFiveAdic.lean` の正確な import 行を直接確認できていないため、具体的な最小 import 名は未確認の推測である。

`omega` を `norm_num` などへ置換する場合は必要 tactic import も変わり得る。本回では Lean ビルドを行っていないため import 縮小案は未検証である。

## Comparator challenge 化の可否

適している。小さな命題なので証明スタイルを比較しやすい。

- 現行: `Nat.mod_eq_zero_of_dvd` + `omega`
- 候補 A: `Nat.mod_eq_zero_of_dvd` + rewrite + `norm_num`
- 候補 B: 一般補題 `mod_eq_nonzero → not_dvd` を作って特殊化
- 候補 C: 0068 から `ZMod` 等式を直接利用して `25 ∤ n` を示す経路

比較軸は tactic の強さ、剰余と可除性の変換の可視性、一般化可能性、0070 と対にした API 設計の明瞭さである。

## 根拠と推測

定理名、型、完全な証明本体、および直後に `padicValNat_five_eq_one_of_dvd_not_sq` が続くことは、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` で確認した。また後続の difference / sum 両枝が本補題を直接呼ぶことも同ソースで確認した。

生成済み standalone の manifest では元モジュールとして `DkMath/FLT/Five/SignedFiveAdic.lean` が列挙されている。一方、対象ブランチ上で分割元ファイルの import 行は直接確認できていないため、最小 import に関する記述は推測として区別した。

既存の日英 PDF における本補題の具体的対応ページは本回確認できておらず、PDF 固有の説明やページ番号は推測で補っていない。

## 次に読むべき定理

```lean
theorem padicValNat_five_eq_one_of_dvd_not_sq
    {n : ℕ} (h5 : 5 ∣ n) (h25 : ¬ 25 ∣ n) :
    padicValNat 5 n = 1
```

0070 と 0071 が用意した「5 は割るが 25 は割らない」という二条件を、次の定理が exact 5-adic valuation `1` へ変換する。