# 0243 — `SignedGoldenRamifierStrippedPacket.norm_sub_conj_eq`

## Lean の型

```lean
/-- The packet coordinate makes the conjugate-difference norm explicit. -/
theorem SignedGoldenRamifierStrippedPacket.norm_sub_conj_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    goldenNorm (p.beta - goldenConj p.beta) =
      -((5 : ℤ) ^ 15 * (p.exceptional.powerSplit.a : ℤ) ^ 20) := by
  rw [goldenNorm_sub_conj, p.beta_snd]
  ring
```

これは `theorem` であり、0231 `SignedGoldenRamifierStrippedPacket` が保持する第二座標の明示式を、0242 `goldenNorm_sub_conj` に代入して、`beta` とその共役との差のノルムを完全な整数冪積へ特殊化する。

## 数学的主張

0242 では任意の黄金整数 $x=a+b\varphi$ に対して

$$
N(x-\overline{x})=-5b^2
$$

が証明された。

一方、ramifier を一度取り除いた packet `p` は field `beta_snd` として

$$
p.\beta_{\mathrm{snd}}
=-5^7 a^{10}
$$

を保持する。ここで $a$ は `p.exceptional.powerSplit.a` を整数へ coercion したものと読む。

したがって、

$$
N(\beta-\overline{\beta})
=-5\left(-5^7a^{10}\right)^2
$$

となり、平方によって符号が消えるので、

$$
N(\beta-\overline{\beta})
=-5^{15}a^{20}
$$

を得る。本 theorem はこの exact mass identity を Lean 上で公開する。

## 証明全体での役割

`SignedGoldenConjugateCoprime.lean` の目的は、stripped element `beta` とその共役 `goldenConj beta` が黄金整数環で相対素であることを証明することにある。

共通因子 `d` が `beta` と `conj beta` の双方を割るなら、0191 `goldenDivides_sub` により

$$
d\mid(\beta-\overline{\beta})
$$

も従う。0192 `goldenNorm_dvd_of_goldenDivides` によって、そのノルムは整数側で

$$
N(d)\mid N(\beta)
$$

かつ

$$
N(d)\mid N(\beta-\overline{\beta})
$$

を満たす。

packet には既に

$$
N(\beta)=b^5
$$

が保存されている。本 theorem はもう一方を

$$
N(\beta-\overline{\beta})=-5^{15}a^{20}
$$

という明示的な整数 mass に変える。

そして正本 source の直後の 0244 `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj` では、`b^5` と $5^{15}a^{20}$ の coprimality を利用して、共通因子ノルムの `natAbs` が `1` であることを導き、最終的にその共通因子が `GoldenUnit` であることを示す。

したがって 0243 は、黄金整数の共通因子問題を整数の coprimality 問題へ落とすための **第二の整数 mass certificate** である。

## 直接依存する定義・補題

直接の Lean proof が使用するものは非常に少ない。

- 0242 `goldenNorm_sub_conj`
- 0231 `SignedGoldenRamifierStrippedPacket.beta_snd`
- `ring`

statement 側では次の定義・field に依存する。

- `SignedGoldenRamifierStrippedPacket`
- `GoldenInt`
- `goldenNorm`
- `goldenConj`
- `p.beta`
- `p.exceptional.powerSplit.a`

概念的な依存は

$$
N(x-\overline{x})=-5x_{\mathrm{snd}}^2
$$

と

$$
\beta_{\mathrm{snd}}=-5^7a^{10}
$$

の合成だけである。

## 証明の流れ

proof は二段階である。

```lean
rw [goldenNorm_sub_conj, p.beta_snd]
ring
```

1. `goldenNorm_sub_conj` により左辺を

$$
-5\cdot p.\beta_{\mathrm{snd}}^2
$$

へ書き換える。
2. `p.beta_snd` により第二座標を

$$
-5^7a^{10}
$$

へ置換する。
3. 残った整数多項式・冪式を `ring` で正規化し、

$$
-5^{15}a^{20}
$$

へ一致させる。

数学的には、

$$
-5(-5^7a^{10})^2
=-5\cdot5^{14}a^{20}
=-5^{15}a^{20}
$$

という計算そのものである。

## Lean 固有の処理

この theorem は namespace-qualified method-style 名

```lean
SignedGoldenRamifierStrippedPacket.norm_sub_conj_eq
```

を持つ。そのため `p : SignedGoldenRamifierStrippedPacket u v w` に対して downstream では

```lean
p.norm_sub_conj_eq
```

として参照できる。

`rw [goldenNorm_sub_conj, p.beta_snd]` では、最初の rewrite が generic theorem を `x := p.beta` に特殊化し、次の rewrite が structure field に保存された packet 固有の coordinate certificate を展開する。

最後の `ring` は整数環 `ℤ` 上で符号、積、自然数冪を正規化する。ここでは divisibility、valuation、gcd などの数論 tactic は必要なく、0242 と packet field が必要な数学情報を既に分離しているため純粋な polynomial normalization だけで閉じる。

## 冗長・重複箇所

0243 は数学的には 0242 の直接 specialization であり、新しい一般法則は導入していない。理論上 downstream で毎回

```lean
rw [goldenNorm_sub_conj, p.beta_snd]
ring
```

と書けば本 theorem を省略できる。

しかし named theorem として残す価値は高い。

- downstream の relative-primality proof が packet の coordinate algebra を再展開せずに済む。
- `beta` と共役との差が持つ five-adic mass を theorem 名から直接探索できる。
- 0241 generic factorization、0242 generic norm formula、0243 packet specialization という三層 API が明確になる。
- `beta_snd` の内部形が将来変更されても consumer 側の interface を固定しやすい。

一方で、`p.beta_snd` と本 theorem はどちらも同じ `a` の巨大冪を明示するため、representation が変わると両方を更新する必要がある。この点は packet により抽象的な valuation certificate を保持する設計との比較対象になる。

## 最適化候補

1. **現行の specialization theorem を維持する**

   proof は2行で、generic theorem と packet field の役割分担も非常に明瞭である。

2. **符号付き exact equality と絶対値 / `natAbs` 版を分離する**

   0244 が本当に利用するのは共通因子ノルムが

$$
5^{15}a^{20}
$$

を割るという正の整数 mass である。したがって、

```lean
goldenNorm (...).natAbs = 5 ^ 15 * ...
```

のような consumer-facing lemma を追加すれば `Int.dvd_neg` や cast 処理を減らせる可能性がある。

3. **valuation certificate を追加する**

   exact equality に加えて、例えば `5`-adic valuation や prime-support 情報を named theorem として提供すれば、後続の coprimality proof の意図がより明瞭になる可能性がある。

4. **0241–0243 を namespace API として整理する**

   generic factorization、generic norm identity、packet specialization を naming convention で統一すると探索性が上がる。

5. **packet の `beta_snd` field から導出 field へ移す設計を比較する**

   `beta_snd` を一次 certificate とし本 theorem を派生させる現行方式と、必要な mass identity を packet に直接保持する方式を比較できる。

現行設計は局所 proof が極めて短く、数学的 provenance も追いやすいため、大きな変更の必要性は低い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が直接必要とする Mathlib 表面は主に

- equality rewriting `rw`
- ring normalization `ring`

である。

主要依存は project 内の 0242 と packet structure にある。

宣言単独では `Mathlib` 全体よりかなり小さい import で足りる可能性が高い。一方、同じ `SignedGoldenConjugateCoprime.lean` の直後の theorem は `Nat.Coprime`、整数整除、`natAbs`、cast、`omega` などを使うため、module 全体の最小 import は本 theorem 単独より広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 `rw [goldenNorm_sub_conj, p.beta_snd]; ring`
- B: `calc` で各数学段階を明示する proof
- C: `goldenNorm`、`goldenConj`、`beta_snd` を直接展開する座標 proof
- D: `norm_num` / `ring_nf` 中心の closed arithmetic proof
- E: exact equality ではなく `natAbs` / valuation certificate を直接証明する consumer-oriented API

比較軸は proof 長、依存深度、数学的 provenance、定義展開量、後続 0244 での cast / sign 処理量、API 安定性である。

特に A と E の比較は、**数学的に最も自然な符号付きノルム恒等式** と **後続 proof が最も使いやすい非負 mass certificate** のどちらを公開 API の中心に置くべきかを測る良い課題になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` generated section である。

正本 source では 0242 の直後に本 theorem があり、さらに直後に

```lean
theorem SignedGoldenRamifierStrippedPacket.beta_relPrime_conj
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    GoldenRelPrime p.beta (goldenConj p.beta) := by
  ...
```

が続くことを確認した。

既存の日英 PDF に対応する具体的ページ・節番号は今回直接特定していないため、PDF ページ番号は推測しない。

## 次に読むべき宣言

依存順の次は **0244 `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj`** である。

この theorem は、任意の共通因子 `d` について、

$$
N(d)\mid b^5
$$

と

$$
N(d)\mid -5^{15}a^{20}
$$

を得る。packet の power-split が保持する coprimality によって

$$
|N(d)|=1
$$

を導き、unit–norm criterion により `GoldenUnit d` を結論する。

したがって 0244 は 0241–0243 で準備した conjugate-difference machinery をまとめて回収し、

$$
GoldenRelPrime(\beta,\overline{\beta})
$$

を完成させる、この module の中心 theorem である。