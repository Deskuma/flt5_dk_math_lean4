# 0229 — `exists_golden_quotient_remainder`

## Lean の型

```lean
theorem exists_golden_quotient_remainder
    (x y : GoldenInt) (hy : y ≠ 0) :
    ∃ q r : GoldenInt,
      x = q * y + r ∧
      (r = 0 ∨ goldenEuclideanSize r < goldenEuclideanSize y) := by
  refine ⟨goldenQuotient x y, goldenRemainder x y, ?_, ?_⟩
  · simp [goldenRemainder, golden_mul_eq]
  · exact Or.inr (golden_remainder_size_lt x hy)
```

これは `theorem` であり、非零の除数 `y` に対して、黄金整数環の quotient `q` と remainder `r` が存在し、

$$
x=qy+r
$$

かつ

$$
r=0\quad\text{または}\quad
\operatorname{size}(r)<\operatorname{size}(y)
$$

を満たすことを一つの existential package として公開する。

## 数学的主張

主張は黄金整数環における通常の Euclidean division の存在である。

非零 `y` に対して、すでに前段で具体的に

$$
q:=\operatorname{goldenQuotient}(x,y),
$$

$$
r:=\operatorname{goldenRemainder}(x,y)=x-qy
$$

が構成されている。

0223 `golden_quotient_mul_add_remainder` に相当する再構成則により

$$
x=qy+r
$$

が成立し、0228 `golden_remainder_size_lt` により

$$
\operatorname{size}(r)<\operatorname{size}(y)
$$

が成立する。したがって remainder が `0` かどうかを場合分けする必要すらなく、常に右側の strict-decrease 分岐を選べる。

この theorem は、その二つの既存事実を existential witness として束ねる最終包装である。

## 証明全体での役割

0209–0228 の `GoldenEuclidean.lean` では、Euclidean division を構成するための部品が順に準備された。

- `GoldenRat` と `goldenRatNorm` で有理商座標と二次ノルムを導入。
- 最近接整数丸めにより quotient error を fundamental cell に入れる。
- `goldenRat_norm_abs_lt_one` で cell 上の norm contraction を得る。
- `goldenQuotientCoords` で $x/y$ の有理座標を作る。
- `goldenQuotient` でそれを黄金整数格子へ丸める。
- `goldenRemainder` で $r=x-qy$ を定義する。
- `goldenEuclideanSize` で $|N(x)|$ を自然数値 measure にする。
- 0227 で remainder norm の exact identity を作る。
- 0228 で strict decrease を証明する。

0229 は、これらを初めて **一つの Euclidean division statement** として外へ出す。

したがって 0229 自身は新しい解析的評価や代数恒等式を証明する theorem ではない。ここまでに構築した quotient、remainder、再構成則、strict decrease を existential API にまとめる「組み上げ工程」である。

その直後の `goldenEuclideanDomain : EuclideanDomain GoldenInt` は、同じ quotient / remainder / measure を typeclass instance へ登録する。0229 はその直前に、人間が読む数学的な Euclidean division の形を明示する役割を持つ。

## 直接依存する定義・補題

主な直接依存は次の通りである。

- 0220 `goldenQuotient`
- 0221 `goldenRemainder`
- 0224 `goldenEuclideanSize`
- 0228 `golden_remainder_size_lt`
- 0159 `golden_mul_eq`
- `GoldenInt`

statement は標準乗法 `q * y` を用いる一方、`goldenRemainder` の定義内部では raw multiplication `goldenMul` を使うため、再構成 proof では `golden_mul_eq` が raw / standard API の橋になる。

概念的な依存は

$$
q:=goldenQuotient(x,y),
$$

$$
r:=goldenRemainder(x,y),
$$

$$
x=qy+r,
$$

$$
y\neq0\Longrightarrow size(r)<size(y)
$$

をまとめて

$$
\exists q,r,\ x=qy+r\land(r=0\lor size(r)<size(y))
$$

へ package するだけである。

## 証明の流れ

### 1. witness を具体的に選ぶ

```lean
refine ⟨goldenQuotient x y, goldenRemainder x y, ?_, ?_⟩
```

existential witness を抽象的に探すのではなく、すでに構成済みの canonical quotient / remainder をそのまま採用する。

これにより残る goal は二つだけになる。

1. `x = q * y + r`
2. `r = 0 ∨ size r < size y`

### 2. quotient-remainder identity を閉じる

```lean
· simp [goldenRemainder, golden_mul_eq]
```

`goldenRemainder x y` を

$$
x-goldenMul(q,y)
$$

へ展開し、`golden_mul_eq` で `goldenMul q y` を標準 `q * y` へ変換する。

その後 `simp` が

$$
q y + (x-q y)=x
$$

という加法群上の恒等式を閉じる。

0223 `golden_quotient_mul_add_remainder` と同じ数学内容をここで再利用しているが、現行 proof は theorem 名を呼ばず定義展開 + simp で再計算している。

### 3. strict-decrease 分岐を選ぶ

```lean
· exact Or.inr (golden_remainder_size_lt x hy)
```

0228 は非零 `y` に対して常に

$$
size(r)<size(y)
$$

を与えるため、disjunction の右側を `Or.inr` で選べばよい。

つまり `r = 0` を判定する必要はない。

## Lean 固有の処理

`refine ⟨..., ..., ?_, ?_⟩` は、二重 existential と conjunction を一度に constructor で構築している。

statement の論理構造は概念的には

```lean
Exists fun q =>
  Exists fun r =>
    And
      (x = q * y + r)
      (Or (r = 0) (goldenEuclideanSize r < goldenEuclideanSize y))
```

であり、最初の `refine` が `q` と `r` を埋め、残る二つの proof field を `?_` として生成する。

`Or.inr` は disjunction の右 branch を明示的に選ぶ constructor である。

また `simp [goldenRemainder, golden_mul_eq]` は、Euclidean-domain 構築で繰り返し現れる raw / standard multiplication の representation boundary を吸収している。

## 冗長・重複箇所

最も明確な重複は、第一 conjunct の証明で 0223 `golden_quotient_mul_add_remainder` を直接使わず、

```lean
simp [goldenRemainder, golden_mul_eq]
```

で同じ内容を再証明している点である。

0223 は

```lean
y * goldenQuotient x y + goldenRemainder x y = x
```

という向きであり、0229 は

```lean
x = goldenQuotient x y * y + goldenRemainder x y
```

を要求するため、左右反転と可換性が必要になる。このため direct reuse より `simp` の方が短くなっている可能性が高い。

また second conjunct は

```lean
r = 0 ∨ size r < size y
```

という Euclidean-domain で典型的な形だが、0228 が非零除数に対して無条件で strict decrease を与えるため、左 branch は本 theorem では使われない。これは API shape に合わせるための論理的冗長性である。

## 最適化候補

1. **0223 を直接再利用する**
   - quotient-remainder identity の重複を避けられる。
   - ただし equality の向きと積の順序を整える補助が必要になる可能性がある。

2. **標準乗法向きの再構成 theorem を追加する**
   - `x = q * y + r` をそのまま statement とする theorem があれば、0229 の第一 branch は `exact` だけで閉じられる。

3. **Euclidean division result を structure 化する**
   - quotient、remainder、再構成、decrease certificate を一つの structure に bundle すれば、0229 と最終 instance の重複を減らせる。

4. **disjunction を外す内部 theorem を用意する**
   - 現行構成では `y ≠ 0` なら常に strict decrease なので、内部 API として

```lean
∃ q r, x = q * y + r ∧ size r < size y
```

を持ち、必要な場所で `Or.inr` に持ち上げる設計も可能である。

5. **現行の薄い packaging theorem を維持する**
   - proof が極めて短く、数学的な Euclidean division statement が明示されるため、文書性という観点では現行設計に十分な価値がある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem 自身が直接必要とする Mathlib 表面はかなり小さい。

- existential / conjunction constructor
- `Or.inr`
- `simp`
- 標準加法群・環 notation

難しい解析・算術 tactic は本 theorem 自身では使用しない。

ただし直接依存する 0228 は `round`、`exact_mod_cast`、絶対値不等式などを使い、`GoldenEuclidean.lean` 全体では `field_simp`、`ring`、`linarith`、`norm_num` 等も必要になる。

したがって宣言単独の import は小さくできても、module 全体の import 最適化は周辺 theorem に支配される。今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、候補としてのみ記録する。

## Comparator challenge 化の可否

適している。0229 は数学的には薄いが、API packaging の比較にはよい題材である。

比較候補は次の通り。

- A: 現行 `refine` + `simp` + `Or.inr`。
- B: 0223 と 0228 を theorem-level に直接合成する方式。
- C: quotient/remainder/decrease を structure に bundle する方式。
- D: standard `EuclideanDomain` API の generic division theorem を最終 instance 構築後に使う方式。
- E: disjunction を持たない stronger internal theorem を作り、外側で API shape に変換する方式。

比較軸は、proof 行数、上流 theorem 再利用率、API の読みやすさ、最終 `EuclideanDomain` instance との重複、一般 quadratic order への移植性である。

特に A と C の比較は、「薄い theorem を積み重ねる設計」と「certificate を bundle する設計」の違いを見るよい Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

直前の 0228 正本文書には、本 theorem の Lean 型と proof が次宣言として記録されている。

```lean
theorem exists_golden_quotient_remainder
    (x y : GoldenInt) (hy : y ≠ 0) :
    ∃ q r : GoldenInt,
      x = q * y + r ∧
      (r = 0 ∨ goldenEuclideanSize r < goldenEuclideanSize y) := by
  refine ⟨goldenQuotient x y, goldenRemainder x y, ?_, ?_⟩
  · simp [goldenRemainder, golden_mul_eq]
  · exact Or.inr (golden_remainder_size_lt x hy)
```

対象ブランチには日本語・英語 PDF が存在する。ただし本 theorem に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0230 `goldenEuclideanDomain`** である。

これは `noncomputable instance` として `EuclideanDomain GoldenInt` を構築し、ここまで準備した

- `goldenQuotient`
- `goldenRemainder`
- `goldenEuclideanSize`
- `goldenQuotient_zero`
- `golden_quotient_mul_add_remainder`
- `golden_remainder_size_lt`
- `goldenEuclideanSize_mul`
- `goldenEuclideanSize_pos_of_ne_zero`

などを Mathlib の Euclidean-domain typeclass fields に登録する。

0229 が「Euclidean division が存在する」という人間向けの theorem-level package なら、0230 は同じ機構を Lean の algebra hierarchy へ接続する最終 integration point である。