# 0192 — `goldenNorm_dvd_of_goldenDivides`

## Lean の型

```lean
/-- Norm carries golden divisibility to integer divisibility. -/
theorem goldenNorm_dvd_of_goldenDivides {d x : GoldenInt}
    (h : GoldenDivides d x) : goldenNorm d ∣ goldenNorm x := by
  rcases h with ⟨q, rfl⟩
  rw [goldenNorm_mul]
  exact dvd_mul_right _ _
```

これは `theorem` であり、黄金整数環 `GoldenInt` 内で `d` が `x` を割るなら、その整数値ノルム `goldenNorm d` が `goldenNorm x` を割ることを示す。

## 数学的主張

`GoldenDivides d x` は

$$
d\mid x
$$

を黄金整数環の raw API で表し、定義上はある `q : GoldenInt` が存在して

$$
x=dq
$$

となることを意味する。

黄金ノルムは 0174 `goldenNorm_mul` により乗法的なので、

$$
N(x)=N(dq)=N(d)N(q).
$$

したがって整数環 `ℤ` において

$$
N(d)\mid N(x)
$$

が成立する。

本 theorem は、この極めて標準的な「環内の整除を乗法的ノルムで整数整除へ送る」原理を、`GoldenInt` の明示 API として実装している。

## 証明全体での役割

0187–0191 までは `GoldenDivides` 自体の基本法則を整備していた。

- 0187 `GoldenDivides` — raw `goldenMul` による整除の定義
- 0188 `goldenDivides_iff_dvd` — Mathlib 標準 `∣` との同値
- 0189 `goldenDivides_refl` — 反射性
- 0190 `goldenDivides_trans` — 推移性
- 0191 `goldenDivides_sub` — 共通因子が差も割ること

0192 はそこから一段進み、黄金整数環内部の因子情報を整数側へ射影する最初の theorem である。

これは後続の unit・relative-primality argument で重要になる。黄金整数 `d` が二つの因子を共通に割るとき、0191 でその差も割ることを得た後、0192 により

$$
N(d)\mid N(\text{difference})
$$

という整数整除へ落とせる。すると `N(d)` は通常の整数算術・素因数・大きさ・`±1` 判定で制約できる。

つまり 0192 は、

$$
\text{golden divisibility}
\longrightarrow
\text{integer divisibility of norms}
$$

という重要な「次元降下」の入口である。

## 直接依存する定義・補題

直接依存は次の通りである。

- `GoldenInt`
- 0187 `GoldenDivides`
- 0164 `goldenNorm`
- 0174 `goldenNorm_mul`
- Mathlib 標準の整数整除
- Mathlib theorem `dvd_mul_right`

proof script で明示的に名前を出しているのは `goldenNorm_mul` と `dvd_mul_right` である。

概念的には

$$
\texttt{GoldenDivides } d\ x
\Rightarrow x=dq
\xrightarrow{\ N(x)=N(d)N(q)\ }
N(d)\mid N(x)
$$

という一段の transport である。

## 証明の流れ

現行 proof は三段階である。

```lean
by
  rcases h with ⟨q, rfl⟩
  rw [goldenNorm_mul]
  exact dvd_mul_right _ _
```

1. `h : GoldenDivides d x` を展開し、商 `q` と等式 `x = goldenMul d q` を取り出す。
2. `rfl` pattern によって `x` 自体を `goldenMul d q` に置換する。
3. `goldenNorm_mul` により

$$
goldenNorm(goldenMul\ d\ q)=goldenNorm(d)\cdot goldenNorm(q)
$$

へ書き換える。
4. `dvd_mul_right _ _` により、整数 `goldenNorm d` がその右倍 `goldenNorm d * goldenNorm q` を割ることを閉じる。

ここでは 0188 `goldenDivides_iff_dvd` を経由せず、`GoldenDivides` の existential witness を直接使っている点が 0189–0191 と対照的である。

## Lean 固有の処理

```lean
rcases h with ⟨q, rfl⟩
```

は、`GoldenDivides d x` の定義

```lean
def GoldenDivides (d x : GoldenInt) : Prop :=
  ∃ q : GoldenInt, x = goldenMul d q
```

から witness `q` を取り出し、同時に equality proof を `rfl` pattern で消費する。

この結果、goal の `x` はその場で `goldenMul d q` に置換されるため、別途 `rw [hq]` を書く必要がない。

続く

```lean
rw [goldenNorm_mul]
```

は 0174 の norm multiplicativity を使い、`GoldenInt` の問題を `ℤ` の積へ変換する。

最後の

```lean
exact dvd_mul_right _ _
```

では Lean が穴 `_` を goal から推論し、一般 theorem を具体化している。proof は座標展開・`ring`・`norm_num` を一切使わず、既存 API の組合せだけで閉じる。

## 冗長・重複箇所

本 theorem は「乗法的写像は整除を保存する」という一般原理の特殊化であり、数学的には非常に標準的である。

また `goldenNorm` は現状 `ℤ` 値の plain function であり、`MonoidHom` として bundle されていないため、この保存則を専用 theorem として手書きしている。

もし `goldenNorm` を適切な multiplicative map として bundle できれば、一般的な `map_dvd` 型の議論へ寄せられる可能性がある。ただし `goldenNorm` は値域が `ℤ` で、符号を持つ二次ノルムであるため、どの既存構造へ載せるのが最も自然かは設計検討が必要である。

一方、現行 theorem は短く、FLT5 の downstream で必要な意味を theorem 名に直接露出しているため、専用 API としての価値は高い。

## 最適化候補

1. **現行 proof を維持する**
   - witness を直接利用し、依存が浅く、数学的にも透明。

2. **標準 `dvd` bridge を経由する**
   - 0188 `goldenDivides_iff_dvd` を使って `d ∣ x` へ移し、factor witness を標準 API から取り出す方法。
   - ただし現行より一段遠回りになる可能性が高い。

3. **`goldenNorm` を multiplicative map として bundle する**
   - `goldenNorm_mul`、`goldenNorm_pow`、整除保存などを一般 API から導ける可能性がある。
   - 今後ノルム関連 theorem が増えるなら有力。

4. **絶対ノルムへの API を分離する**
   - Euclidean-domain 側では `Int.natAbs (goldenNorm x)` を使うため、符号付き norm と非負 norm の役割を明確に分ける設計も検討できる。

5. **downstream 専用の common-divisor norm lemma を追加する**
   - relative-primality 証明で同じ形が繰り返されるなら、`GoldenDivides d x → GoldenDivides d y → ...` を一段上で束ねる余地がある。

局所的には現行 proof が十分に簡潔で、変更圧力は低い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem 自身が直接必要とする表面は小さい。

- existential elimination (`rcases`)
- `GoldenDivides`
- `goldenNorm`
- `goldenNorm_mul`
- integer divisibility
- `dvd_mul_right`
- `rw`

`ring`、`norm_num`、`omega`、解析 API は本 theorem 自身では使用しない。

ただし同じ `GoldenDivisibility.lean` では共役、冪、unit、整数ノルム判定などを続けて扱うため、module 全体の最小 import は本 theorem 単独より広い。今回は Lean build を行わないため、正確な細粒度 import 集合は未検証であり、最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 `rcases` + `goldenNorm_mul` + `dvd_mul_right`
- B: 0188 を経由して標準 `dvd` witness を使う
- C: `goldenNorm` を multiplicative map として bundle し一般 theorem から導く
- D: raw 座標まで展開して直接整数式を証明する

比較軸は、

- proof/source 行数
- 直接依存の深さ
- norm の構造化度
- raw coordinate への依存度
- Mathlib 標準 API 再利用度
- downstream readability
- 将来の一般 quadratic-order 化への適合性

である。

特に A と C の比較は、「必要な theorem を薄く直接証明する」設計と「ノルムを algebraic morphism として先に bundle する」設計の trade-off を測る良い Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

正本 source では次の順序を確認できる。

```lean
theorem goldenDivides_sub {d x y : GoldenInt} ...

/-- Norm carries golden divisibility to integer divisibility. -/
theorem goldenNorm_dvd_of_goldenDivides {d x : GoldenInt}
    (h : GoldenDivides d x) : goldenNorm d ∣ goldenNorm x := by
  rcases h with ⟨q, rfl⟩
  rw [goldenNorm_mul]
  exact dvd_mul_right _ _

theorem goldenConj_add (x y : GoldenInt) :
    goldenConj (x + y) = goldenConj x + goldenConj y := by
  ext <;> simp [goldenConj] <;> ring
```

対象ブランチには日本語・英語 PDF も存在するが、本 theorem に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0193 `goldenConj_add`** である。

```lean
theorem goldenConj_add (x y : GoldenInt) :
    goldenConj (x + y) = goldenConj x + goldenConj y := by
  ext <;> simp [goldenConj] <;> ring
```

0192 で整除を整数ノルムへ射影した後、source は共役の加法・否定・減算・冪に対する互換性を整備するブロックへ入る。0193 はその最初で、共役が加法を保存することを明示する theorem である。
