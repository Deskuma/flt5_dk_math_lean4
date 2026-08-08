# 0070 — `five_dvd_of_eq_five_add_twentyFive_mul`

## Lean の型

```lean
private theorem five_dvd_of_eq_five_add_twentyFive_mul
    {n M : ℕ} (h : n = 5 + 25 * M) :
    5 ∣ n := by
  use 1 + 5 * M
  omega
```

この宣言は `private` であり、`SignedFiveAdic.lean` 内部で明示的な剰余分解 `n = 5 + 25*M` を通常の可除性 `5 ∣ n` へ変換する局所補題である。

## 数学的主張

自然数 `n,M` が

$$
n=5+25M
$$

を満たすなら、

$$
5\mid n
$$

である。

実際、

$$
n=5+25M=5(1+5M)
$$

なので、可除性の witness として

$$
1+5M
$$

を取ればよい。

## 証明全体での役割

0068 で `ZMod 25` の等式を `n % 25 = 5` に戻し、0069 でそれを

$$
n=5+25M
$$

へ展開した。本補題 0070 は、その明示分解から residual が少なくとも 5 を一因子として持つことを取り出す。

流れは

```text
(residual : ZMod 25) = 5
             ↓ 0068
      residual % 25 = 5
             ↓ 0069
      residual = 5 + 25*M
             ↓ 0070
          5 ∣ residual
```

である。

ただし exact valuation `v₅(residual)=1` を得るには `5 ∣ residual` だけでは足りない。直後の `not_twentyFive_dvd_of_mod_eq_five` が `25 ∤ residual` を与え、その二条件を `padicValNat_five_eq_one_of_dvd_not_sq` が統合する。

## 直接依存する定義・補題

- 自然数の可除性 `Dvd.dvd`
- 存在 witness を与える `use`
- 線形自然数算術を閉じる `omega`

数学的には特別な既出補題を必要とせず、0069 が生成した等式 `h` だけを入力とする。

## 証明の流れ

1. `5 ∣ n` の witness として `1 + 5 * M` を指定する。
2. 残る目標は、可除性の定義展開後の等式

   $$
   n=5(1+5M)
   $$

   に相当する。
3. 仮定 `h : n = 5 + 25*M` と算術恒等式を `omega` に渡して閉じる。

## Lean 固有の処理

Lean の `5 ∣ n` は、内部的にはある自然数 `c` が存在して `n = 5 * c` となることを要求する。`use 1 + 5 * M` はその witness を直接与えている。

このため証明の構成的内容は明瞭で、`omega` は witness 発見には使われていない。`omega` が担当するのは

$$
5+25M=5(1+5M)
$$

という単純な Presburger 算術の正規化だけである。

## 冗長・重複箇所

証明は 2 行であり、論理的重複はほぼない。

ただし `omega` はこの程度の等式にはやや強い tactic である。`simp [h, Nat.mul_add, Nat.mul_assoc]` や `rw [h]` の後に `ring` 系で処理するなど、より局所的な方法へ置き換えられる可能性がある。

また 5 と 25 に特有の命題に見えるが、本質は一般の `a,b,M` に対する

```lean
a ∣ a + a * b * M
```

型の可除性である。その一般性を使うなら、既存の `dvd_add`・`dvd_mul_of_dvd_left` 系 API で tactic を使わず証明できる。

## 最適化候補

第一候補は `omega` を除き、可除性 API だけで証明することである。例えば `h` で `n` を置換した後、`5 ∣ 5` と `5 ∣ 25*M` を合成すればよい。

第二候補は 0069 と統合し、`n % 25 = 5` から直接 `5 ∣ n` を示す helper を設けることである。実用上はこちらが短いが、現在の 0069→0070 の分離は「剰余式 → 明示分解 → 可除性」というデータ変換を監査しやすい。

第三候補は modulus/residue を一般化し、`n % (p*p) = p` から `p ∣ n` を得る一般補題へ抽象化する案である。ただし本 FLT5 層では `p=5` 固定の可読性にも価値がある。

## 必要 Mathlib import と import 最適化候補

生成済み `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用している。本補題自身に必要なのは自然数の可除性と `omega` tactic だけである。

したがって最小 import 候補は Nat の基本可除性 API と `Mathlib.Tactic.Omega` 相当である。ただし対象ブランチ上では分割元 `DkMath/FLT/Five/SignedFiveAdic.lean` の正確な import 行を直接確認できていないため、具体的な最小 import 名は未確認の推測である。

また tactic-free 証明へ変更できれば `Omega` 依存自体を本補題から除ける可能性がある。本回では Lean ビルドを行っていないため、import 縮小案は未検証である。

## Comparator challenge 化の可否

非常に適している。命題が小さいため、証明スタイルの差が明確に出る。

- 現行: 明示 witness + `omega`
- 候補 A: `rw [h]` 後に可除性 API だけで閉じる
- 候補 B: `⟨1 + 5*M, ...⟩` を直接構成し、算術正規化だけ tactic に任せる
- 候補 C: 一般補題 `n % (p*p) = p → p ∣ n` の特殊化

比較軸は tactic 依存度、算術構造の可視性、一般化可能性、前後の bridge との接続の明瞭さである。

## 根拠と推測

定理名、型、完全な証明本体、および直後に `not_twentyFive_dvd_of_mod_eq_five` と `padicValNat_five_eq_one_of_dvd_not_sq` が続くことは、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` で確認した。

GitHub コード検索は本回一時的に 502 upstream error を返したため、standalone ソースを直接取得して依存順を確認した。既存の日英 PDF における本補題の具体的対応ページは確認できておらず、PDF 固有の説明やページ番号は推測で補っていない。

## 次に読むべき定理

```lean
private theorem not_twentyFive_dvd_of_mod_eq_five
    {n : ℕ} (hmod : n % 25 = 5) :
    ¬ 25 ∣ n
```

0070 が `5 ∣ n`、次の補題が `25 ∤ n` を与えることで、five-adic valuation をちょうど 1 に固定するための二条件が揃う。
