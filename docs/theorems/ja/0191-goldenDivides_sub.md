# 0191 — `goldenDivides_sub`

## Lean の型

```lean
theorem goldenDivides_sub {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hdy : GoldenDivides d y) :
    GoldenDivides d (x - y) := by
  rw [goldenDivides_iff_dvd] at hdx hdy ⊢
  exact dvd_sub hdx hdy
```

これは `theorem` であり、同じ黄金整数 `d` が `x` と `y` の両方を割るなら、その差 `x - y` も割ることを示す。

## 数学的主張

数学的内容は通常の整除の差に対する閉性そのものである。

$$
d\mid x,\qquad d\mid y
$$

ならば

$$
d\mid(x-y).
$$

`GoldenDivides` の定義を直接展開すれば、ある `q₁,q₂ : GoldenInt` が存在して

$$
x=dq_1,\qquad y=dq_2
$$

となる。したがって

$$
x-y=dq_1-dq_2=d(q_1-q_2),
$$

ゆえに `q₁ - q₂` を商として `GoldenDivides d (x - y)` が成立する。

現行 Lean proof はこの witness を直接構成せず、0188 `goldenDivides_iff_dvd` によって専用整除を Mathlib 標準の `∣` へ移し、一般 theorem `dvd_sub` を再利用する。

## 証明全体での役割

0187–0191 は `GoldenDivides` の基礎 API を整える小さなブロックである。

- 0187 `GoldenDivides` — raw `goldenMul` による整除の定義
- 0188 `goldenDivides_iff_dvd` — 標準 `∣` との完全同値
- 0189 `goldenDivides_refl` — 反射性
- 0190 `goldenDivides_trans` — 推移性
- 0191 `goldenDivides_sub` — 共通因子が差も割ること

本 theorem はこの中でも downstream との接続が特に明瞭である。`GoldenDivisibility.lean` の後段では、ある `d` が `beta` と `goldenConj beta` の両方を割るとき、

```lean
have hddiff : GoldenDivides d (p.beta - goldenConj p.beta) :=
  goldenDivides_sub hdbeta hdconj
```

の形で両者の差へ共通因子を運ぶ。この差は共役構造により座標的に単純化され、さらに norm divisibility を通じて整数側の制約へ押し戻される。

したがって本 theorem は、黄金整数環内の「共通因子」を、元と共役の差というより制御しやすい対象へ輸送するための基本工具である。FLT5 の相対素性 argument ではこの一段が重要になる。

## 直接依存する定義・補題

直接依存は次の通りである。

- `GoldenInt`
- 0187 `GoldenDivides`
- 0188 `goldenDivides_iff_dvd`
- Mathlib 標準 theorem `dvd_sub`
- `Sub GoldenInt` / `goldenSub` により与えられた減算構造

proof script が明示的に使用する named theorem は `goldenDivides_iff_dvd` と `dvd_sub` である。

概念的には

$$
\texttt{GoldenDivides}
\xleftrightarrow{\texttt{goldenDivides\_iff\_dvd}}
\text{standard divisibility}
\xrightarrow{\texttt{dvd\_sub}}
\texttt{GoldenDivides}
$$

という transport になっている。

## 証明の流れ

現行 proof は二段階だけである。

```lean
by
  rw [goldenDivides_iff_dvd] at hdx hdy ⊢
  exact dvd_sub hdx hdy
```

1. `hdx : GoldenDivides d x` を `d ∣ x` へ変換する。
2. `hdy : GoldenDivides d y` を `d ∣ y` へ変換する。
3. goal `GoldenDivides d (x - y)` も `d ∣ x - y` へ変換する。
4. Mathlib の `dvd_sub hdx hdy` をそのまま適用して閉じる。

つまり `GoldenDivides` の existential witness、`goldenMul`、`goldenSub` の内部座標式を一切展開せず、標準 algebra theorem を再利用している。

## Lean 固有の処理

```lean
rw [goldenDivides_iff_dvd] at hdx hdy ⊢
```

の `⊢` は現在の goal も rewrite 対象に含める。結果として、

```lean
hdx : GoldenDivides d x
hdy : GoldenDivides d y
⊢ GoldenDivides d (x - y)
```

が一度に

```lean
hdx : d ∣ x
hdy : d ∣ y
⊢ d ∣ x - y
```

へ揃う。

`goldenDivides_iff_dvd` は proposition-level の `↔` theorem なので `rw` で命題そのものを書き換えられる。0190 と同じ transport pattern を使い、今回は `dvd_trans` ではなく `dvd_sub` へ接続している。

また goal に現れる `x - y` は既に `Sub GoldenInt` instance を介した標準減算なので、`dvd_sub` がそのまま適用できる。raw `goldenSub` へ戻す処理は不要である。

## 冗長・重複箇所

`goldenDivides_sub` は Mathlib の `dvd_sub` を domain-specific 名で包んだ薄い wrapper theorem であり、0188 がある以上、論理的な新規性は小さい。

直接定義から証明するなら、二つの quotient witness を取り出して `q₁ - q₂` を新しい witness として構成できる。また標準 `∣` だけを使う設計なら、本 theorem 自体を持たず downstream で `dvd_sub` を直接呼ぶこともできる。

それでも専用 theorem を置く利点はある。

- downstream を `GoldenDivides` 語彙のまま保てる
- `GoldenDivides` から標準 `dvd` への transport を局所化できる
- 共役因子の差を取る argument が theorem 名から読みやすい
- raw witness 構成を downstream から隠せる

特に本 theorem は後段で実際に `beta - goldenConj beta` へ共通因子を運ぶため、単なる wrapper 以上に proof narrative 上の意味を持つ。

## 最適化候補

1. **現行 proof を維持する**
   - 最短級で、0188 bridge と Mathlib 再利用が明示的。

2. **直接 witness を構成する**
   - `GoldenDivides` の意味は最も可視になる。
   - 一方で quotient の差、分配律、raw/standard multiplication の橋を扱う必要があり、proof burden は増える。

3. **標準 `∣` に全面統一する**
   - 0189–0191 の wrapper 群を削減できる。
   - ただし黄金整数専用の証明語彙と監査性は弱くなる。

4. **bridge theorem を simp 正規化へ利用する**
   - boilerplate をさらに減らせる可能性がある。
   - proposition-level simp が予想以上に広く作用しないかは要検証。

5. **共通因子差分 API としてまとめる**
   - 後続で `x - conj x` 型の利用が繰り返されるなら、より domain-specific な補題へ一段まとめる余地がある。

局所的には現行 proof は十分に簡潔で、変更の必要性は低い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem 自身が直接必要とする表面は小さい。

- `GoldenInt`
- `GoldenDivides`
- `goldenDivides_iff_dvd`
- 標準 divisibility relation
- `dvd_sub`
- `rw` tactic

`ring`、`norm_num`、`omega`、解析系 API は本 theorem 自身では使用しない。

ただし `GoldenDivisibility.lean` 全体では、直後にノルム整除、共役、冪、unit 関連 theorem を扱うため、module 全体の最小 import は本 theorem 単独より広い。今回は Lean build を行わないので、正確な細粒度 import 集合は未検証であり、最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 `rw [...] at hdx hdy ⊢; exact dvd_sub hdx hdy`
- B: `GoldenDivides` を展開し quotient witness `q₁ - q₂` を直接構成
- C: `simpa` を中心に `dvd_sub` を transport
- D: `GoldenDivides` を廃止し標準 `∣` のみを使用

比較軸は、

- proof/source 行数
- raw semantics の可視性
- Mathlib 標準 API 再利用度
- bridge theorem への依存
- refactor 耐性
- downstream readability
- 共役差分 argument との親和性

である。

特に A と B の比較は、domain-specific existential を直接操作する証明と、成熟した一般 algebra API へ transport する証明の違いを明瞭に示す。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

正本 source では次の順序を確認できる。

```lean
theorem goldenDivides_trans {d x y : GoldenInt} ...

theorem goldenDivides_sub {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hdy : GoldenDivides d y) :
    GoldenDivides d (x - y) := by
  rw [goldenDivides_iff_dvd] at hdx hdy ⊢
  exact dvd_sub hdx hdy

/-- Norm carries golden divisibility to integer divisibility. -/
theorem goldenNorm_dvd_of_goldenDivides ...
```

対象ブランチには `FLT5-main-ja-v0-r1.pdf` と `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的な PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0192 `goldenNorm_dvd_of_goldenDivides`** である。

```lean
/-- Norm carries golden divisibility to integer divisibility. -/
theorem goldenNorm_dvd_of_goldenDivides {d x : GoldenInt}
    (h : GoldenDivides d x) : goldenNorm d ∣ goldenNorm x := by
  rcases h with ⟨q, rfl⟩
  rw [goldenNorm_mul]
  exact dvd_mul_right _ _
```

0191 までで `GoldenDivides` の基礎法則が整った。0192 からは黄金整数環内の整除を整数ノルムの整除へ射影し、後続の unit・relative-primality argument に必要な整数側の制約へ移る段階に入る。
