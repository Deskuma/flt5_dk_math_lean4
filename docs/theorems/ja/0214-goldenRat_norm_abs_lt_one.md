# 0214 — `goldenRat_norm_abs_lt_one`

## Lean の型

```lean
theorem goldenRat_norm_abs_lt_one
    {u v : ℚ}
    (hu : |u| ≤ (1 : ℚ) / 2)
    (hv : |v| ≤ (1 : ℚ) / 2) :
    |u ^ 2 + u * v - v ^ 2| < 1 := by
  have h := goldenRat_norm_abs_le_five_sixteen hu hv
  norm_num at h ⊢
  linarith
```

これは `theorem` であり、最近接整数丸めによって得られる square fundamental cell

$$
|u|\le\frac12,\qquad |v|\le\frac12
$$

上で、黄金ノルム二次形式

$$
Q(u,v)=u^2+uv-v^2
$$

の絶対値が厳密に `1` 未満であることを示す。

## 数学的主張

0213 `goldenRat_norm_abs_le_five_sixteen` では、同じ仮定から鋭い一様評価

$$
|Q(u,v)|\le\frac5{16}
$$

が既に証明されている。

本 theorem は新しい二次形式評価を行うのではなく、単に

$$
\frac5{16}<1
$$

を使って

$$
|Q(u,v)|<1
$$

へ強める。

したがって数学的には

$$
|Q(u,v)|\le\frac5{16}<1
$$

という一行の推移律である。

ただし証明全体では、この `1` が決定的な閾値になる。Euclidean division では remainder の norm を divisor の norm と丸め誤差 norm の積として表し、誤差側が `1` 未満であることから remainder の絶対 norm が divisor より真に小さくなる。

## 証明全体での役割

`GoldenEuclidean.lean` の流れでは、0214 は **定量評価から Euclidean contraction への境界 theorem** である。

上流では、

1. 0209 `GoldenRat` で有理 quotient 座標を用意する。
2. 0210 `goldenRatNorm` で黄金ノルム二次形式を `ℚ²` 上へ拡張する。
3. 0211–0212 で各座標を最近接整数へ丸め、誤差を `[-1/2,1/2]^2` に入れる。
4. 0213 でその cell 上の絶対 norm を `5/16` 以下へ抑える。
5. **0214 本 theorem** で `5/16 < 1` を使い strict contraction を得る。

下流では `golden_remainder_size_lt` が

```lean
have hcell : |goldenRatNorm (A - round A, B - round B)| < 1 := by
  simpa [goldenRatNorm] using goldenRat_norm_abs_lt_one hA hB
```

と本 theorem を直接使用する。

その後 `goldenRemainder_norm_rat_identity` により remainder norm を

$$
N(r)=N(y)\,Q(\text{rounding error})
$$

の形へ分解し、`|Q|<1` から

$$
|N(r)|<|N(y)|
$$

を得る。

したがって 0213 が「鋭い幾何学的 bound」、0214 が「Euclidean-domain API が要求する strict inequality」への変換を担当している。

## 直接依存する定義・補題

直接依存は非常に小さい。

- 0213 `goldenRat_norm_abs_le_five_sixteen`
- `norm_num`
- `linarith`
- 有理数 `ℚ` の線形順序体構造

statement 自体は `goldenRatNorm` を名前で使わず、0213 と同じ多項式

$$
u^2+uv-v^2
$$

を直接記述している。

概念的な依存は

$$
\texttt{goldenRat\_norm\_abs\_le\_five\_sixteen}
\Longrightarrow
\frac5{16}\text{ bound}
\Longrightarrow
<1
$$

だけである。

## 証明の流れ

### 1. 0213 の sharp bound を取得する

```lean
have h := goldenRat_norm_abs_le_five_sixteen hu hv
```

これにより

$$
|u^2+uv-v^2|\le\frac5{16}
$$

を得る。

### 2. 数値定数を正規化する

```lean
norm_num at h ⊢
```

`norm_num` は有理定数 `5/16`、`1/2` などを算術的に正規化し、`5/16 < 1` が solver に扱いやすい形になるよう goal と仮定を整理する。

ここでは 0213 の本質的な非線形評価は既に終わっているため、新しい `nlinarith` は不要である。

### 3. 線形推論で strict inequality を閉じる

```lean
linarith
```

`h : |Q| ≤ 5/16` と `5/16 < 1` から

$$
|Q|<1
$$

を導く。

## Lean 固有の処理

この theorem では 0213 と異なり、絶対値の展開、平方完成、`sq_nonneg`、`nlinarith` は一切現れない。

`have h := ...` で 0213 の theorem result を局所仮定として保存し、`norm_num at h ⊢` で仮定と目標の両方を同時に数値正規化している。

その後の `linarith` は、すでに線形な大小関係だけを扱う。つまり proof architecture は

```text
hard nonlinear estimate (0213)
→ numeric normalization
→ linear strictness step (0214)
```

と明確に分離されている。

この分離は Lean 上でも有利で、鋭い bound の proof を変更しても、0214 以下は `≤ 5/16` という interface だけを見ればよい。

## 冗長・重複箇所

論理的には 0214 は 0213 と `5/16 < 1` の即時帰結なので、独立 theorem として持たず、下流で

```lean
have h := goldenRat_norm_abs_le_five_sixteen hA hB
linarith
```

と直接書くことも可能である。

しかし専用 theorem にする利点は大きい。

- Euclidean division が必要とする条件 `|Q|<1` を直接 API として表現できる。
- downstream は sharp constant `5/16` を知る必要がない。
- 将来 0213 の bound を別の `c<1` に変更しても、0214 以下の proof interface を維持できる。
- `golden_remainder_size_lt` の数学的読み方が明瞭になる。

したがって 0213 と 0214 は情報的には近いが、「sharp estimate」と「consumer-facing contraction theorem」という役割分担がある。

もう一つの API-level 重複は、0210 `goldenRatNorm` があるにもかかわらず、本 theorem でも二次式を直接再記述している点である。0213 と同じ statement shape を保つことで証明再利用は単純だが、名前付き norm API との接続は下流の `simpa [goldenRatNorm]` に委ねられている。

## 最適化候補

1. **`goldenRatNorm` を statement に使う**

```lean
|goldenRatNorm (u, v)| < 1
```

とすれば 0210 との構造的接続が直接見える。

2. **0213 から `lt_of_le_of_lt` で閉じる**

例えば概念的には

```lean
exact lt_of_le_of_lt
  (goldenRat_norm_abs_le_five_sixteen hu hv)
  (by norm_num)
```

とすれば `linarith` 依存を消せる可能性がある。正確な elaboration は今回 build 未検証である。

3. **一般 contraction helper を作る**

`|Q| ≤ c` と `c < 1` から `|Q| < 1` を得る一般形は自明なので、専用 helper を増やす価値は低い。

4. **0213/0214 を二層 API として意図的に維持する**

現行設計は sharp mathematics と downstream interface を分けており、これはむしろ良い分割と評価できる。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem 自身が直接必要とする主要機能は、

- `ℚ`
- ordered field inequalities
- `norm_num`
- `linarith`

である。

0213 のように `abs_le`、`sq_nonneg`、`nlinarith` を直接必要とはしない。ただし同一 `GoldenEuclidean.lean` module ではそれらに加えて `round`、`field_simp`、`ring`、casts、`EuclideanDomain`、well-founded measure なども使うため、module 単位の最小 import はかなり広い。

今回は Lean build を行わないため、正確な最小 import module 名は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。小さな theorem なので proof-style の差が測りやすい。

候補は次の通り。

- A: 現行 `have` + `norm_num` + `linarith`
- B: `lt_of_le_of_lt` + `norm_num`
- C: `nlinarith [goldenRat_norm_abs_le_five_sixteen hu hv]`
- D: `goldenRatNorm` を statement にした API 版
- E: 0213 を介さず cell bound から直接 `<1` を証明

比較軸は、proof term の短さ、solver 依存度、0213 の sharp constant を保つ可読性、downstream interface の明瞭さ、将来の bound 改良への頑健性である。

特に A と B の比較は、「算術 solver に任せるか、order transitivity を proof term として明示するか」という小さく明確な Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

source では 0213 の直後に本 theorem があり、その直後に

```lean
/-- A nonzero golden integer has nonzero norm. -/
theorem goldenNorm_ne_zero_of_ne_zero {y : GoldenInt} (hy : y ≠ 0) :
    goldenNorm y ≠ 0 := by
  ...
```

が続く。

また `golden_remainder_size_lt` が本 theorem を直接利用して、最近接整数丸め誤差の norm が `1` 未満であることを得ている。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、本 theorem に対応する具体的ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0215 `goldenNorm_ne_zero_of_ne_zero`** である。

```lean
theorem goldenNorm_ne_zero_of_ne_zero {y : GoldenInt} (hy : y ≠ 0) :
    goldenNorm y ≠ 0 := by
  intro hn
  have hm : goldenMul y (goldenConj y) = 0 := by
    rw [golden_mul_conj, hn]
    rfl
  rcases mul_eq_zero.mp hm with hy0 | hc0
  · exact hy hy0
  · apply hy
    rw [← goldenConj_invol y, hc0]
    rfl
```

0214 までで丸め誤差側の strict contraction が完成した。0215 では非零 divisor の norm が非零であることを示し、後続の有理 quotient 座標で `goldenNorm y` を分母として安全に除算できるようにする。
