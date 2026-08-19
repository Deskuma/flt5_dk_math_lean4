# 0149 — `goldenFiveNonsquare`

## Lean の型

```lean
instance goldenFiveNonsquare : Zsqrtd.Nonsquare 5 := by
  refine ⟨fun n h => ?_⟩
  have hn : n < 3 := by
    by_contra hn
    have h3 : 3 ≤ n := Nat.le_of_not_gt hn
    have h9 : 9 ≤ n * n := by nlinarith
    omega
  interval_cases n <;> norm_num at h
```

これは theorem ではなく、`Zsqrtd.Nonsquare 5` の typeclass instance である。`Zsqrtd 5` を扱うために、自然数 `5` が平方数ではないことを Lean の型クラス探索へ供給する。

## 数学的主張・宣言の意味

数学的内容は

$$
\nexists n\in\mathbb N,\quad n^2=5
$$

である。すなわち $5$ は自然数平方ではない。実際、$2^2=4<5<9=3^2$ なので平方数になり得ない。

この事実自体は初等的だが、`Zsqrtd 5` 側では重要な構造条件になる。`Zsqrtd.Nonsquare 5` が登録されることで、後続の `Zsqrtd` の零積性質を利用でき、`goldenDoubleEmbedding` を通じて `GoldenInt` の零因子排除へ接続される。

## 証明全体での役割

直前の 0148 `goldenDoubleEmbedding` は

```lean
def goldenDoubleEmbedding (x : GoldenInt) : Zsqrtd 5 :=
  ⟨2 * x.fst + x.snd, x.snd⟩
```

によって黄金整数を `Zsqrtd 5` 側へ移す。本 instance は、その受け皿 `Zsqrtd 5` に対して $5$ が非平方であることを供給する。

その後の流れは source 上で

```text
goldenDoubleEmbedding
→ goldenFiveNonsquare
→ goldenDoubleEmbedding_injective
→ goldenDoubleEmbedding_mul
→ GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero
→ NoZeroDivisors GoldenInt
→ IsDomain GoldenInt
```

となる。特に `GoldenInt.eq_zero_or_eq_zero_of_mul_eq_zero` では、埋め込み後の積が零であることから `Zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero` を使ってどちらかの因子が零であると結論している。したがって本 instance は、黄金整数環を単なる `CommRing` から整域へ押し上げるための外部構造条件である。

## 直接依存する定義・補題

直接依存するものは次である。

- Mathlib の `Zsqrtd.Nonsquare`
- 自然数上の大小関係と乗法
- `Nat.le_of_not_gt`
- `nlinarith`
- `omega`
- `interval_cases`
- `norm_num`

`goldenDoubleEmbedding` 自体は本 instance の証明項には現れないが、証明全体での利用目的という意味では直前の構造的依存である。

## 証明・構築の流れ

証明は二段階である。

まず、平方が $5$ になると仮定された自然数 `n` が `3` 未満でなければならないことを示す。

```lean
have hn : n < 3 := by
  by_contra hn
  have h3 : 3 ≤ n := Nat.le_of_not_gt hn
  have h9 : 9 ≤ n * n := by nlinarith
  omega
```

`n ≥ 3` なら $n^2≥9$ となり、平方が $5$ であるという仮定 `h` と両立しない。

次に `n < 3` から `n=0,1,2` の有限場合分けへ落とす。

```lean
interval_cases n <;> norm_num at h
```

それぞれの平方は $0,1,4$ なので、いずれも $5$ ではなく矛盾する。

## Lean 固有の処理

`refine ⟨fun n h => ?_⟩` は `Zsqrtd.Nonsquare 5` が要求する非平方性の field を直接構築している。ここでは typeclass instance なので、後続 theorem が `Zsqrtd.Nonsquare 5` を明示引数として渡さなくても typeclass resolution により自動取得できる。

`nlinarith` は `3 ≤ n` から非線形項 `n*n` の下界を作るために使われ、`omega` は自然数算術上の矛盾を閉じる。最後の `interval_cases` は小さい有限区間へ case split し、`norm_num` が各具体値を計算する。

## 冗長・重複箇所

数学的には $2^2<5<3^2$ だけで十分なので、現在の proof はやや tactic-driven である。`n < 3` を先に証明してから `0,1,2` を列挙するため、初等事実に対して複数 tactic を組み合わせている。

一方、`Zsqrtd.Nonsquare 5` を明示的 instance として一度登録する設計自体には重複はなく、後続で同じ非平方性を再証明しないという点で適切である。

## 最適化候補

候補は次の通りである。

1. Mathlib に `5` の非平方性を直接与える既存 instance / theorem があれば再利用する。
2. `n^2 = 5` から parity や平方の mod 5 / mod 8 性質を用いる一般補題へ寄せる。
3. 現行の有限場合分けを保ちつつ、`omega` と `nlinarith` の役割を減らしてより短い算術 proof にする。
4. `Zsqrtd.Nonsquare d` を頻繁に必要とするなら、素数 $p$ に対する一般的な非平方条件から instance を生成する補助層を設ける。

ただし本宣言は短く局所的であり、一般化によって依存が増えるなら現行 proof の方が監査しやすい可能性もある。

## 必要 Mathlib import と import 最適化候補

standalone source は `import Mathlib` を使用している。本宣言には少なくとも `Zsqrtd` とその `Nonsquare` 型クラス、および `nlinarith`、`omega`、`interval_cases`、`norm_num` の tactic 群が必要である。

最小 import は今回 Lean build を行っていないため未検証である。候補としては `Zsqrtd` の定義モジュールと各 tactic import の組合せに縮小できる可能性があるが、正確な最小集合は推測として扱う。

## Comparator challenge 化の可否

適している。小さいが、同じ `Zsqrtd.Nonsquare 5` を次の複数方式で構築できる。

- 現行の大小評価 + `interval_cases`
- modular arithmetic による平方剰余の否定
- 素数の平方性に関する一般 theorem の再利用
- `decide` / `native_decide` に頼らない明示算術 proof

比較軸は proof の短さ、依存 tactic 数、一般化可能性、Mathlib API への依存度、可読性である。特に「具体的な小定数を局所算術で閉じるか、一般 theorem を再利用するか」を比較する良い課題になる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenOrder.lean` generated section である。そこでは `goldenDoubleEmbedding` の直後に本 instance が置かれ、次に `goldenDoubleEmbedding_injective` が続く。

対象ブランチには日本語・英語 PDF も存在するが、この補助 instance に対応する具体的ページは今回直接特定していない。そのため PDF ページ番号・節番号は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
theorem goldenDoubleEmbedding_injective :
    Function.Injective goldenDoubleEmbedding := by
  intro x y h
  have hsnd : x.snd = y.snd := congrArg Zsqrtd.im h
  have hfst : 2 * x.fst + x.snd = 2 * y.fst + y.snd :=
    congrArg Zsqrtd.re h
  apply GoldenInt.ext
  · omega
  · exact hsnd
```

である。0149 で受け皿 `Zsqrtd 5` の非平方条件が整い、0150 では doubled embedding が情報を失わないこと、すなわち injective であることを証明する。