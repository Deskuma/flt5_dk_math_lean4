# 0202 — `goldenNorm_eq_one_or_neg_one_of_unit`

## Lean の型

```lean
theorem goldenNorm_eq_one_or_neg_one_of_unit {x : GoldenInt}
    (h : GoldenUnit x) : goldenNorm x = 1 ∨ goldenNorm x = -1 := by
  rcases h with ⟨y, hxy, _⟩
  have hn : goldenNorm x * goldenNorm y = 1 := by
    rw [← goldenNorm_mul, hxy]
    norm_num [goldenNorm, goldenOne]
  exact Int.eq_one_or_neg_one_of_mul_eq_one hn
```

これは `theorem` であり、黄金整数 `x` が `GoldenUnit` なら、その整数値ノルムが `1` または `-1` であることを示す。

## 数学的主張

主張は

$$
GoldenUnit(x)\Longrightarrow N(x)=1\ \lor\ N(x)=-1
$$

である。

`GoldenUnit x` は、ある `y : GoldenInt` が存在して

$$
xy=1,\qquad yx=1
$$

を満たすことを表す。0174 `goldenNorm_mul` の乗法性から

$$
N(x)N(y)=N(xy)=N(1)=1
$$

を得る。`N(x),N(y)` は整数なので、整数の積が `1` なら各因子は `1` または `-1` であり、特に

$$
N(x)=\pm1
$$

となる。

0201 `goldenUnit_of_norm_eq_one_or_neg_one` は逆向き

$$
N(x)=\pm1\Longrightarrow GoldenUnit(x)
$$

を与えるため、0201 と本 theorem を合わせると黄金整数の unit criterion

$$
GoldenUnit(x)\iff N(x)=\pm1
$$

が完成する。

## 証明全体での役割

0198–0202 は黄金整数の単元をノルムで判定する block である。

- 0198 `GoldenUnit` — 両側逆元の存在として単元を定義する。
- 0199 `goldenUnit_of_norm_eq_one` — `N(x)=1` なら単元。
- 0200 `goldenUnit_of_norm_eq_neg_one` — `N(x)=-1` なら単元。
- 0201 `goldenUnit_of_norm_eq_one_or_neg_one` — `N(x)=±1` から単元への方向を統合する。
- 0202 本 theorem — 単元から `N(x)=±1` への逆方向を与える。

この逆向きがあることで、後続の `goldenUnit_neg` や `goldenUnit_mul` では unit hypothesis を一度整数ノルムの符号条件へ射影し、整数算術を行った後、0201 で再び `GoldenUnit` へ戻せる。

最終的な `GoldenRelPrime` では「すべての共通因子が unit」であることを示すため、unit を整数ノルム `±1` へ翻訳できる本 theorem は、golden divisibility と整数算術の重要な橋になる。

## 直接依存する定義・補題

直接依存は次の通りである。

- 0198 `GoldenUnit`
- 0174 `goldenNorm_mul`
- `goldenOne`
- `goldenNorm`
- `Int.eq_one_or_neg_one_of_mul_eq_one`
- `norm_num`

証明では `GoldenUnit` の witness `y` と片側の積等式 `hxy` だけを使用する。`GoldenUnit` は両側逆元を要求するが、ノルム積を `1` とするためには一方向の等式だけで十分である。

概念的な依存は

$$
GoldenUnit(x)\Longrightarrow \exists y,\ xy=1\Longrightarrow N(x)N(y)=1\Longrightarrow N(x)=\pm1
$$

である。

## 証明の流れ

### 1. unit witness を取り出す

```lean
rcases h with ⟨y, hxy, _⟩
```

`GoldenUnit x` から逆元候補 `y` と

```lean
hxy : goldenMul x y = goldenOne
```

を取り出す。逆向きの積等式はこの proof では不要なので `_` で捨てる。

### 2. ノルム積が 1 であることを示す

```lean
have hn : goldenNorm x * goldenNorm y = 1 := by
  rw [← goldenNorm_mul, hxy]
  norm_num [goldenNorm, goldenOne]
```

まず `← goldenNorm_mul` により `N(x)N(y)` を `N(xy)` へ戻す。次に `hxy` で `xy=1` と書き換え、`goldenOne` のノルムが `1` であることを `norm_num` で閉じる。

### 3. 整数の積が 1 であることから符号を判定する

```lean
exact Int.eq_one_or_neg_one_of_mul_eq_one hn
```

整数 lemma により、`goldenNorm x * goldenNorm y = 1` から `goldenNorm x` が `1` または `-1` であることを得る。

## Lean 固有の処理

`rcases h with ⟨y, hxy, _⟩` は existential witness と conjunction を同時に分解する。`GoldenUnit` は

```lean
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧
    goldenMul eta epsilon = goldenOne
```

なので、最後の `_` は第二の逆元等式を意図的に捨てている。

`rw [← goldenNorm_mul, hxy]` では `goldenNorm_mul` を逆向きに使う。目標に現れる整数積を黄金整数の積のノルムへ戻すことで、unit witness の等式 `hxy` を適用可能な形にする。

最後の `Int.eq_one_or_neg_one_of_mul_eq_one` は、ノルムの値域が `ℤ` であることを直接利用する離散的な結論である。

## 冗長・重複箇所

0201 と 0202 は互いに逆向きの theorem なので、API としては

```lean
GoldenUnit x ↔ goldenNorm x = 1 ∨ goldenNorm x = -1
```

という iff theorem にまとめる余地がある。

また `GoldenUnit` は両側逆元を保持するが、本 theorem は一方向しか利用しない。`GoldenInt` は可換環なので数学的には片側逆元で十分であり、これは raw bootstrap API に由来する冗長性である。

`N(1)=1` も毎回 `norm_num [goldenNorm, goldenOne]` で再計算しているため、使用頻度が高いなら専用 simp theorem `goldenNorm_one` を置く候補がある。

## 最適化候補

1. 0201 と 0202 を `GoldenUnit x ↔ N(x)=±1` の iff theorem で束ねる。
2. `GoldenUnit x ↔ IsUnit x` を証明し Mathlib 標準 unit API と接続する。
3. `goldenNorm` を multiplicative map として bundle し、一般の unit-image lemma を再利用する。
4. `goldenNorm_one` を専用 simp theorem として公開する。
5. 可換環であることを利用し、片側逆元中心の unit API と比較する。

現行 proof は短く、整数ノルムへ射影する意図も明瞭なので、局所的な proof 圧縮の優先度は高くない。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が直接利用する主な Mathlib 表面は、`Int.eq_one_or_neg_one_of_mul_eq_one`、`norm_num`、existential / conjunction elimination、equality rewriting である。

宣言単独なら Mathlib 全体より小さい import で足りる可能性が高いが、`GoldenDivisibility.lean` 全体では整数整除、共役、ノルム算術、ring tactic 等も使用する。今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行の witness 展開 + `goldenNorm_mul` + integer lemma
- B: Mathlib `IsUnit` を使う一般環論 proof
- C: `goldenNorm` を multiplicative map として bundle して導く proof
- D: 0201/0202 を bidirectional unit criterion として一括設計
- E: `GoldenUnit` を片側逆元で再設計した場合の proof

比較軸は proof 長、依存深度、Mathlib 標準 API 再利用率、数学的透明性、raw coordinate API との整合、downstream rewrite usability である。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

リポジトリ上の 0201 日本語正本でも、本 theorem の Lean 型と proof が次宣言として記録されている。今回も 0202 日英が未作成であることを確認してから対象を選択した。

対象ブランチには日本語・英語 PDF が存在するが、本 theorem に対応する具体的ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0203 `goldenUnit_phi`** である。

```lean
theorem goldenUnit_phi : GoldenUnit goldenPhi := by
  apply goldenUnit_of_norm_eq_neg_one
  norm_num [goldenNorm, goldenPhi]
```

0202 までで unit と norm `±1` の双方向 criterion が完成する。0203 からはその criterion を具体的な黄金整数へ適用し、まず生成元 `φ` 自身が unit であることを確定する段階へ進む。
