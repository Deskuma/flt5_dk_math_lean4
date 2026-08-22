# 0190 — `goldenDivides_trans`

## Lean の型

```lean
theorem goldenDivides_trans {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hxy : GoldenDivides x y) :
    GoldenDivides d y := by
  rw [goldenDivides_iff_dvd] at hdx hxy ⊢
  exact dvd_trans hdx hxy
```

これは `theorem` であり、0187 で定義した黄金整数専用の整除関係 `GoldenDivides` が推移的であることを示す。

## 数学的主張

数学的内容は通常の整除の推移性そのものである。

$$
d\mid x,\qquad x\mid y
$$

ならば

$$
d\mid y
$$

である。

`GoldenDivides` の定義を直接展開すれば、ある `q₁,q₂ : GoldenInt` が存在して

$$
x=dq_1,
\qquad
y=xq_2
$$

となる。これを代入すると

$$
y=(dq_1)q_2=d(q_1q_2)
$$

なので、商 `q₁q₂` を witness として `GoldenDivides d y` が得られる。

現行 Lean proof はこの witness 合成を直接書かず、0188 `goldenDivides_iff_dvd` で三つの proposition を Mathlib 標準整除へ移し、一般 theorem `dvd_trans` を再利用する。

## 証明全体での役割

0187–0191 付近は、`GoldenDivides` を domain-specific な整除 API として使えるようにする基礎法則層である。

- 0187 `GoldenDivides` — raw `goldenMul` による整除の定義
- 0188 `goldenDivides_iff_dvd` — 標準 `∣` との完全同値
- 0189 `goldenDivides_refl` — 反射性
- 0190 `goldenDivides_trans` — 推移性
- 0191 `goldenDivides_sub` — 共通因子が差も割ること

本 theorem は、複数段階の factorization を一本の `GoldenDivides` へ合成するための基本工具である。

FLT5 の後段では、ある黄金整数因子を別の factorization や共役関係へ伝播させる場面が現れる。専用整除 API の推移性を theorem 名として持つことで、downstream は raw quotient witness の積を毎回構築せずに済む。

数学的には極めて一般的な法則だが、0188 の bridge を実際の proof architecture へ回収する重要な一段である。

## 直接依存する定義・補題

直接依存は次の通りである。

- `GoldenInt`
- 0187 `GoldenDivides`
- 0188 `goldenDivides_iff_dvd`
- Mathlib 標準 theorem `dvd_trans`

proof script では `goldenDivides_iff_dvd` と `dvd_trans` を明示的に使用する。

概念的な依存は

$$
\texttt{GoldenDivides}
\xleftrightarrow{\texttt{goldenDivides\_iff\_dvd}}
\text{standard divisibility}
\xrightarrow{\texttt{dvd\_trans}}
\texttt{GoldenDivides}
$$

である。

## 証明の流れ

現行 proof は二段階だけである。

```lean
by
  rw [goldenDivides_iff_dvd] at hdx hxy ⊢
  exact dvd_trans hdx hxy
```

1. `rw [goldenDivides_iff_dvd] at hdx hxy ⊢` により、仮定と目標を同時に標準整除へ変換する。
2. 変換後は

```lean
hdx : d ∣ x
hxy : x ∣ y
⊢ d ∣ y
```

という一般的な整除の推移性だけが残る。
3. `dvd_trans hdx hxy` で閉じる。

この proof は `GoldenDivides` の existential witness を一度も展開しない。専用 API を標準 algebra API へ transport し、その一般 theorem を利用してから戻す設計である。

## Lean 固有の処理

`rw [goldenDivides_iff_dvd] at hdx hxy ⊢` の `⊢` は現在の goal も rewrite 対象に含める記法である。

したがって一つの `rw` で、

```lean
hdx : GoldenDivides d x
hxy : GoldenDivides x y
⊢ GoldenDivides d y
```

が

```lean
hdx : d ∣ x
hxy : x ∣ y
⊢ d ∣ y
```

へ一括変換される。

`goldenDivides_iff_dvd` は `↔` theorem なので proposition-level rewrite が可能である。0189 では goal だけを書き換えたが、0190 では仮定二本と goal の三箇所を同じ bridge でそろえる点が Lean 的な見どころである。

その後の `exact dvd_trans hdx hxy` は、型が完全に標準 `Dvd.dvd` にそろっているため追加の `simpa` や coercion 処理を必要としない。

## 冗長・重複箇所

`goldenDivides_trans` は Mathlib の `dvd_trans` を domain-specific 名で包んだ薄い wrapper theorem である。

0188 が存在する以上、論理的には downstream で必要なたびに

```lean
rw [goldenDivides_iff_dvd] at ...
exact dvd_trans ...
```

と書けば済む。

また `GoldenDivides` の定義を直接展開し、二つの quotient witness を乗算しても同じ theorem を証明できる。

それでも wrapper を置く利点は、

- downstream を `GoldenDivides` 語彙だけで読める
- raw witness 合成を隠蔽できる
- Mathlib の標準整除へ transport する実装詳細を局所化できる
- 将来 `GoldenDivides` の内部表現を変更しても theorem 名を維持できる

ことである。

したがって数学的には重複だが、API boundary と監査性のための意図的な冗長性と評価できる。

## 最適化候補

1. **現行 proof を維持する**
   - 短く、標準 theorem 再利用も明示的で、保守性が高い。

2. **`simpa [goldenDivides_iff_dvd]` 系に圧縮する**
   - より短い proof が書ける可能性はあるが、`rw ... at ... ⊢` の方が transport の構造を読みやすい。

3. **定義から quotient witness を直接合成する**
   - `GoldenDivides` の数学的意味は最も可視になる。
   - 一方で `goldenMul` の結合律や標準乗法 bridge を明示する必要が生じ、現行より proof burden が増える可能性が高い。

4. **`GoldenDivides` を標準 `∣` に統一する**
   - 0189–0191 の wrapper theorem 群自体を削減できる。
   - ただし domain-specific な証明監査語彙は失われる。

5. **0188 を simp theorem として使う設計を検討する**
   - 自動 transport が便利になる可能性がある。
   - proposition-level simp の向きと広がりは慎重に評価すべきである。

局所的には現行 proof が十分に最小かつ明瞭で、変更の必要性は低い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem 自身が必要とする表面は小さい。

- `GoldenInt`
- `GoldenDivides`
- `goldenDivides_iff_dvd`
- 標準 divisibility relation
- `dvd_trans`
- `rw` tactic

`ring`、`norm_num`、`omega`、解析系 API は本 theorem 自身では使用しない。

ただし `GoldenDivisibility.lean` 全体では直後に `dvd_sub`、ノルム整除、共役、unit 関連 theorem を使用するため、module 全体の最小 import はより広い。今回は Lean build を行わないので、正確な細粒度 import 集合は未検証であり、最適化候補としてのみ扱う。

## Comparator challenge 化の可否

適している。小さい theorem なので proof architecture の差を比較しやすい。

- A: 現行 `rw [...] at hdx hxy ⊢; exact dvd_trans hdx hxy`
- B: `GoldenDivides` を直接展開して quotient witness を積で合成
- C: `simpa` を中心に標準 `dvd_trans` を transport
- D: `GoldenDivides` を廃止して標準 `∣` の theorem をそのまま使用

比較軸は、

- proof term / source 行数
- raw semantics の可視性
- Mathlib 標準 API 再利用度
- bridge theorem への依存
- refactor 耐性
- downstream readability

である。

特に A と B は、「domain-specific existential を直接操作するか、標準 algebra theorem へ輸送するか」という Lean 設計の違いをよく示す Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

正本 source では次の順序が確認できる。

```lean
theorem goldenDivides_refl (x : GoldenInt) : GoldenDivides x x := by
  rw [goldenDivides_iff_dvd]

theorem goldenDivides_trans {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hxy : GoldenDivides x y) :
    GoldenDivides d y := by
  rw [goldenDivides_iff_dvd] at hdx hxy ⊢
  exact dvd_trans hdx hxy

theorem goldenDivides_sub {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hdy : GoldenDivides d y) :
    GoldenDivides d (x - y) := by
  ...
```

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、本 theorem に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0191 `goldenDivides_sub`** である。

```lean
theorem goldenDivides_sub {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hdy : GoldenDivides d y) :
    GoldenDivides d (x - y) := by
  rw [goldenDivides_iff_dvd] at hdx hdy ⊢
  exact dvd_sub hdx hdy
```

0190 が整除の推移性を標準 `dvd_trans` へ委譲したのに対し、0191 は共通因子が差 `x-y` も割ることを標準 `dvd_sub` へ委譲する。これは後段で元と共役の共通因子から差の整除を導く議論に直接つながる。