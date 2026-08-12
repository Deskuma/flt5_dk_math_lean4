# 0061 — `sumGN5_pos`

## 1. Lean の型

```lean
theorem sumGN5_pos
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    0 < SumGN5 u v := by
  by_cases h : v ≤ u
  · rw [SumGN5, if_pos h]
    have hv4 : 0 < v ^ 4 := pow_pos hv 4
    omega
  · rw [SumGN5, if_neg h]
    have hu4 : 0 < u ^ 4 := pow_pos hu 4
    omega
```

## 2. 数学的主張

正の自然数 `u`,`v` に対して、0059 で定義した第五冪和 residual `SumGN5 u v` は正である。

$$
0<u,\quad 0<v
\Longrightarrow
0<\operatorname{SumGN5}(u,v).
$$

`SumGN5` は順序に応じて二つの非負係数多項式のいずれかとして表される。`v ≤ u` 側では最後の項が $v^4>0$、反対側では最後の項が $u^4>0$ なので、多項式全体も正になる。

## 3. 証明全体での役割

この定理は sum orientation における residual の非零性を供給する。後続の `nonempty_signedFiveAdicPacket_of_normalForm` の `sumGap` 枝では、

```lean
have hresPos : 0 < SumGN5 u v := sumGN5_pos hPack.hx hPack.hy
```

として直接使われる。

その正値性から `hresPos.ne'` を得て、`padicValNat_carrier_shape_of_mul_eq_fifth` に渡すことで、積

$$
(u+v)\,SumGN5(u,v)=w^5
$$

に対する五進付値の加法則を安全に適用できる。したがって本定理は、0060 の因数分解恒等式を「exact five-adic packet が実際に扱える非零 residual」へ昇格させる小さいが必要な橋である。

## 4. 直接依存する定義・補題

ユーザー定義として直接依存するのは 0059 `SumGN5`。

Lean / Mathlib 側では次を使う。

- `by_cases h : v ≤ u`
- `rw [SumGN5, if_pos h]` / `rw [SumGN5, if_neg h]`
- `pow_pos`
- `omega`

0060 `add_mul_sumGN5_eq_add_pow_five` には論理的には依存していない。正値性は因数分解等式からではなく `SumGN5` の定義そのものから証明される。

## 5. 証明の流れ

1. `v ≤ u` か否かで `SumGN5` の定義枝を確定する。
2. `v ≤ u` 側では、仮定 `hv : 0 < v` から `pow_pos hv 4` により `0 < v^4` を得る。
3. 展開された `SumGN5` の他の項はすべて自然数なので非負であり、正の末項 `v^4` を含むことから `omega` が全体の正値性を閉じる。
4. `¬ v ≤ u` 側では同様に `hu : 0 < u` から `0 < u^4` を得て、末項 `u^4` を使って `omega` で閉じる。

## 6. Lean 固有の処理

数学的には「非負項の和に正の項が一つ含まれる」というだけである。しかし `SumGN5` は `if v ≤ u then ... else ...` という piecewise 定義なので、Lean ではまず `by_cases` と `rw` で枝を露出させる必要がある。

`pow_pos hv 4` / `pow_pos hu 4` は、末項が厳密に正であることを明示する証拠である。その後の `omega` は自然数上の加法・乗法定数係数と順序条件から、他項を個別に非負証明せずに結論を閉じている。

ここでは 0060 と異なり `Nat.sub` を消去するための `Nat.exists_eq_add_of_le` は不要である。減算を含む項がどの値であっても自然数であり、末項の正値性だけで十分だからである。

## 7. 冗長・重複箇所

二枝は完全に対称であり、違いは正値性の証人が `v^4` か `u^4` かだけである。`SumGN5` の piecewise 定義を直接展開する設計のため、この二重化は自然に生じている。

また、局所名 `hv4` / `hu4` は証明意図を明確にする一方、短さだけを求めれば `have : 0 < v ^ 4 := pow_pos hv 4` のようにも書ける。

## 8. 最適化候補

最も自然な最適化は `SumGN5` の対称性補題を先に用意し、一方の枝だけを本質的に証明して他方を左右交換で移送する方法である。ただし、そのためだけに対称性 API を追加すると本定理単体ではむしろ構造が重くなる。

別案として、非負項列に正項が含まれることを `positivity` 系 tactic で処理できるか比較する価値がある。現行の `pow_pos` + `omega` は短く、どの項が正値性を担っているかも明示されるので、監査性は高い。

## 9. 必要 Mathlib import と import 最適化候補

対象ブランチの生成済み `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用していることを確認した。本定理で実際に必要なのは、自然数順序、`pow_pos`、`omega` tactic、そして `SumGN5` を含むローカルモジュールである。

元の分割 `DkMath/FLT/Five/SignedFiveAdic.lean` の正確な import 行は standalone artifact からは確定できないため、具体的な最小 import 名は未確認であり、ここでは推測しない。import 最適化を行うなら、まず `omega` を提供する tactic import と `pow_pos` の由来を `#print` / import tracing で分離して測るのがよい。

## 10. Comparator challenge 化の可否

適している。小さな補題なので実装比較が明瞭である。

- A: 現行の `by_cases` + `pow_pos` + `omega`
- B: `positivity` を中心にした証明
- C: `SumGN5` の対称性補題を利用して片枝だけ証明
- D: 0060 の因数分解恒等式と $u^5+v^5>0$ から積の正値性を逆算する証明

比較基準は証明行数、piecewise 展開回数、必要 import、automation 依存度、意図の読みやすさ、後続 API 再利用性でよい。D は数学的には迂回であり、自然数の積から因子正値性を取り出す追加条件が必要なので、現行法より不利になる可能性が高い。

## 11. 根拠と推測

確定根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された生成済み `DkMath/FLT/Five/SignedFiveAdic.lean` 部分である。そこから定理型・証明本体、および後続 `nonempty_signedFiveAdicPacket_of_normalForm` の `sumGap` 枝で `sumGN5_pos hPack.hx hPack.hy` が直接使用されることを確認した。

standalone artifact は `import Mathlib` であることも確認した。一方、分割元ファイルの最小 import と、既存日英 PDF 内で本補題に対応する具体的ページは今回確定していないため、それらについては推測で補っていない。

## 12. 次に読むべき定理

依存順で次に読むべき未解説補題は、同じ `SignedFiveAdic.lean` 内で直後に置かれる private lemma、

```lean
private theorem five_not_dvd_left_of_coprime_of_dvd_add
    {u v : ℕ} (hcop : Nat.Coprime u v) (h5sum : 5 ∣ u + v) :
    ¬ 5 ∣ u
```

である。sum orientation の法 $25$ residual 計算に向け、`Nat.Coprime u v` と $5\mid u+v$ から $5\nmid u$ を取り出す入口になる。