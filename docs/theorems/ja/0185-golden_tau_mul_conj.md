# 0185 — `golden_tau_mul_conj`

## Lean の型

```lean
theorem golden_tau_mul_conj :
    goldenMul goldenTau (goldenConj goldenTau) = goldenOfInt 5 := by
  rw [golden_mul_conj, goldenNorm_tau]
```

これは `theorem` であり、distinguished ramifier `goldenTau` とその共役の積が、黄金整数環に埋め込まれた整数 `5` に等しいことを示す。

## 数学的主張

`goldenTau` は

```lean
def goldenTau : GoldenInt := ⟨2, 1⟩
```

であり、数学的には

$$
\tau=2+\varphi
$$

を表す。0163 の共役は

$$
\overline{a+b\varphi}=(a+b)-b\varphi
$$

なので、

$$
\overline{\tau}=\overline{2+\varphi}=3-\varphi.
$$

本 theorem は

$$
\tau\overline{\tau}=5
$$

を `GoldenInt` 内部の等式として表している。0176 `golden_mul_conj` で任意の黄金整数について

$$
x\overline{x}=N(x)
$$

が既に証明され、0184 `goldenNorm_tau` で

$$
N(\tau)=5
$$

が確定しているので、本 theorem はこの二つを `x=τ` で合成した特殊化である。

座標で直接確認しても、`goldenTau = ⟨2,1⟩`、`goldenConj goldenTau = ⟨3,-1⟩` なので、その積は `⟨5,0⟩ = goldenOfInt 5` となる。

## 証明全体での役割

0177–0185 では、5 の ramification を担う具体的元を黄金整数環の内部で固定している。

- `goldenSqrtFive = 2φ-1` は平方が `5`、ノルムが `-5`。
- `goldenTau = 2+φ` は `φ * goldenSqrtFive` と一致する。
- `goldenNorm_tau` により `N(τ)=5`。
- 本 theorem により `5` が実際に `τ` とその共役の積として黄金整数環内で分解される。

したがって本 theorem は、単なるノルム値の数値証明から、環内部の **明示的な ramified factorization** へ移る橋である。

直後の `exists_goldenTau_factor_of_five_dvd` では、整数側の条件 `5 ∣ 2*M+N` から `goldenTau` 因子を具体的に抽出する。そこでは「`τ` が norm-five element である」という情報だけでなく、`5` 自体が `τ` と共役因子へ分かれるという本 theorem の見方が、5-adic exceptional branch の幾何を理解する上で重要になる。

## 直接依存する定義・補題

Lean proof が直接使用する named theorem は二つである。

- 0176 `golden_mul_conj`
- 0184 `goldenNorm_tau`

また型と項の構成上、次の定義に依存する。

- `GoldenInt`
- 0178 `goldenTau`
- 0163 `goldenConj`
- 0124 `goldenMul`
- 0162 `goldenOfInt`

直接の証明依存は極めて短く、概念的には

$$
\texttt{golden\_mul\_conj}
+\texttt{goldenNorm\_tau}
\longrightarrow
\texttt{golden\_tau\_mul\_conj}
$$

である。

さらに数学的背景として、0183 `goldenTau_eq_phi_mul_sqrtFive`、0181 `goldenSqrtFive_sq`、0182 `goldenNorm_sqrtFive`、0167 `goldenNorm_phi` が `τ` と ramified square root の関係を説明する。

## 証明の流れ

現行 proof は二回の rewrite だけである。

```lean
by
  rw [golden_mul_conj, goldenNorm_tau]
```

1. `golden_mul_conj` を使い、左辺を

$$
goldenOfInt(goldenNorm\ goldenTau)
$$

へ書き換える。
2. `goldenNorm_tau` を使って `goldenNorm goldenTau` を `5` へ書き換える。
3. 両辺が同じ `goldenOfInt 5` になり、rewrite が目標を閉じる。

証明中には座標展開も `ring` も `norm_num` も現れない。0176 と 0184 で既に確立した API を純粋に再利用する、非常に構造的な証明である。

## Lean 固有の処理

`rw [golden_mul_conj, goldenNorm_tau]` は theorem の左から右への rewrite を順に適用する。

最初の rewrite では `golden_mul_conj goldenTau` が暗黙に特殊化され、

```lean
goldenMul goldenTau (goldenConj goldenTau)
```

が

```lean
goldenOfInt (goldenNorm goldenTau)
```

へ変わる。次の rewrite で内部の norm が `5` になり、目標は反射的等式へ落ちる。

この proof は definitional equality だけではなく、上流 theorem を API として利用している点が重要である。0184 の direct coordinate proof と対照的に、本 theorem は既存構造を再利用する proof style を選んでいる。

## 冗長・重複箇所

数学的には、本 theorem は 0176 `golden_mul_conj` と 0184 `goldenNorm_tau` の完全な特殊化なので、新しい独立情報はほとんどない。

理論上は downstream で毎回

```lean
rw [golden_mul_conj, goldenNorm_tau]
```

と書けば済むため、named theorem を置かない設計も可能である。

しかし `τ * conj τ = 5` は ramification block の中心的な読み方であり、名前付き theorem にすることで次の利点がある。

- `5` の分解を一目で参照できる。
- downstream が norm API の内部経路を知らずに済む。
- `goldenTau` を distinguished ramifier と呼ぶ数学的意味が theorem 名として残る。
- 将来 `goldenTau` や norm 実装が変わっても、factorization API の表面を保ちやすい。

したがって情報論的には重複でも、API と証明可読性の観点では有用な冗長性である。

## 最適化候補

候補は次の四つである。

1. **現行 proof を維持する**
   - 2 theorem の再利用だけで最短かつ構造的。

2. **`simpa` 形式へまとめる**
   - 概念的には

```lean
simpa [goldenNorm_tau] using golden_mul_conj goldenTau
```

   のような一行化が考えられる。ただし exact な simp behavior は今回 build 未検証である。

3. **直接座標計算に置き換える**
   - `goldenTau`、`goldenConj`、`goldenMul` を展開して `decide` / `norm_num` / `ring` で閉じる。
   - 依存は浅くなるが、0176・0184 の再利用を失い数学的構造が見えにくくなる。

4. **ramification API を bundle する**
   - `τ`、`N(τ)=5`、`τ*conj τ=5`、factor extraction を一つの構造または namespace API として整理する。
   - 後続の five-adic exceptional branch が長くなるなら検討価値がある。

現状では、現行 proof は短さと数学的 provenance の両方を満たしており、最適化の必要性は低い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身は tactic として `rw` しか使わず、直接必要な表面は小さい。

- equality rewrite machinery
- `GoldenInt` とその raw operations
- `golden_mul_conj`
- `goldenNorm_tau`

`ring`、`norm_num`、解析 API などは本 theorem 自身では使用しない。

ただし上流 theorem の証明は `ring` や `norm_num` を利用しているため、`GoldenOrder` module 全体の最小 import はそれらに支配される。今回 Lean build は行わないので、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。小さな theorem だが proof architecture の比較が明瞭である。

比較候補は次の通り。

- A: 現行 `rw [golden_mul_conj, goldenNorm_tau]`
- B: `simpa ... using golden_mul_conj goldenTau`
- C: `decide` 等による closed coordinate proof
- D: `ext` + `simp` + `ring` による明示座標 proof
- E: `τ=φ√5` と既知の factorization / norm facts を経由する proof

比較軸は、proof term の短さ、直接依存、数学的 provenance、upstream 変更への頑健性、tactic 依存度、downstream API としての読みやすさである。

特に A と C の比較は、「既存 theorem を再利用する構造証明」と「具体座標を再計算する証明」の差を測るよい Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenOrder.lean` generated section である。

直前の 0184 文書および正本 source では、次の並びが確認できる。

```lean
theorem goldenNorm_tau : goldenNorm goldenTau = 5 := by
  norm_num [goldenNorm, goldenTau]

theorem golden_tau_mul_conj :
    goldenMul goldenTau (goldenConj goldenTau) = goldenOfInt 5 := by
  rw [golden_mul_conj, goldenNorm_tau]
```

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0186 `exists_goldenTau_factor_of_five_dvd`** である。

この次段では、整数座標に現れる `5` の整除条件から、黄金整数環内部で `goldenTau` が実際に因子として現れることを構成的に取り出す。

0184 が

$$
N(\tau)=5
$$

を与え、0185 が

$$
\tau\overline{\tau}=5
$$

を環内部の積へ昇格したので、0186 では「整数として 5 が見える」ことを「黄金整数として τ が割る」ことへ変換する段階に入る。