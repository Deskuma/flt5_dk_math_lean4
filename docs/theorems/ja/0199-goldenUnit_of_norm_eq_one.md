# 0199 — `goldenUnit_of_norm_eq_one`

## Lean の型

```lean
theorem goldenUnit_of_norm_eq_one {x : GoldenInt} (h : goldenNorm x = 1) :
    GoldenUnit x := by
  refine ⟨goldenConj x, ?_, ?_⟩
  · simpa [h, goldenOfInt, goldenOne] using golden_mul_conj x
  · have hc : goldenMul (goldenConj x) x =
        goldenMul x (goldenConj x) := by
      change goldenConj x * x = x * goldenConj x
      exact mul_comm _ _
    rw [hc]
    simpa [h, goldenOfInt, goldenOne] using golden_mul_conj x
```

これは `theorem` であり、黄金整数 `x` のノルムが `1` なら `x` が `GoldenUnit`、すなわち黄金整数環の単元であることを示す。

## 数学的主張

仮定は

$$
N(x)=1
$$

である。0176 `golden_mul_conj` により任意の黄金整数について

$$
x\overline{x}=N(x)
$$

が成り立つので、仮定から

$$
x\overline{x}=1
$$

を得る。`GoldenInt` は可換環なので

$$
\overline{x}x=x\overline{x}=1
$$

でもある。したがって `goldenConj x` が `x` の両側逆元となり、0198 `GoldenUnit` の定義を満たす。

## 証明全体での役割

0198 で単元性を「両側逆元の存在」として定義した直後、本 theorem はノルム情報から具体的な逆元 witness を構成する最初の bridge である。

この後 source では `goldenUnit_of_norm_eq_neg_one` が `N(x)=-1` の場合を扱い、両者をまとめて `goldenUnit_of_norm_eq_one_or_neg_one` が

$$
N(x)=\pm1 \Longrightarrow GoldenUnit(x)
$$

を与える。さらに逆向き `goldenNorm_eq_one_or_neg_one_of_unit` によって

$$
GoldenUnit(x) \Longrightarrow N(x)=\pm1
$$

が得られ、黄金整数における unit criterion が完成する。

この criterion は後続の `goldenUnit_phi`、`goldenUnit_mul`、`goldenUnit_pow`、そして最終的な `GoldenRelPrime` の基礎となる。

## 直接依存する定義・補題

直接依存は次の通りである。

- 0198 `GoldenUnit`
- 0163 `goldenConj`
- 0176 `golden_mul_conj`
- 0162 `goldenOfInt`
- `goldenOne`
- `CommRing GoldenInt` が供給する `mul_comm`

概念的には

$$
N(x)=1
+\bigl(x\overline{x}=N(x)\bigr)
+\text{commutativity}
\Longrightarrow
x^{-1}=\overline{x}.
$$

## 証明の流れ

最初に

```lean
refine ⟨goldenConj x, ?_, ?_⟩
```

として 0198 `GoldenUnit` の逆元 witness に `goldenConj x` を選ぶ。残る goal は左右二本の逆元等式である。

第一方向は

```lean
simpa [h, goldenOfInt, goldenOne] using golden_mul_conj x
```

で閉じる。`golden_mul_conj x` の右辺 `goldenOfInt (goldenNorm x)` を、仮定 `h : goldenNorm x = 1` で `goldenOfInt 1` にし、さらに raw `goldenOne` と一致させる。

第二方向では共役が左側にあるため、まず

```lean
have hc : goldenMul (goldenConj x) x =
    goldenMul x (goldenConj x) := by
  change goldenConj x * x = x * goldenConj x
  exact mul_comm _ _
```

で可換性を使って積の順序を反転する。その後 `rw [hc]` で第一方向と同じ形へ揃え、同じ `golden_mul_conj` を再利用する。

## Lean 固有の処理

`refine ⟨..., ?_, ?_⟩` は existential と conjunction を一度に構築している。0198 `GoldenUnit` が

```lean
∃ eta, goldenMul x eta = goldenOne ∧ goldenMul eta x = goldenOne
```

だから、witness と二つの proof hole が生成される。

`simpa ... using golden_mul_conj x` は、既存 theorem の conclusion を仮定 `h` と raw/standard API の定義展開で現在の goal に正規化する。

第二方向の `change` は raw `goldenMul` を標準 `*` に見せ替え、Mathlib の `mul_comm` を直接使える形にする。この raw/standard interface crossing は本開発で繰り返し現れる Lean 固有の処理である。

## 冗長・重複箇所

可換環なので `GoldenUnit` の定義で両側逆元を要求すること自体が数学的には冗長であり、本 theorem でも第二方向は第一方向から `mul_comm` だけで作られている。

また左右の最後の

```lean
simpa [h, goldenOfInt, goldenOne] using golden_mul_conj x
```

は重複している。局所 lemma として一度 `x * conj x = 1` を作り、左右へ再利用する構成も可能である。

さらに Mathlib 標準の `IsUnit` を中心に設計すれば、inverse witness や左右逆元の一般 API を再利用できる可能性がある。

## 最適化候補

1. **局所的な右逆元 lemma を一度だけ構築する**
   - `goldenMul x (goldenConj x) = goldenOne` を先に `have` し、第二方向は可換性で導く。

2. **`GoldenUnit` を Mathlib `IsUnit` に寄せる**
   - norm-one から `IsUnit` を得る generic algebra API が利用できれば、専用 witness 構築を薄くできる。

3. **共役を `RingEquiv` として bundle する**
   - 0193–0196 まで既に ring-map 的性質が揃っており、unit inverse と norm の関係もより構造的に記述できる。

4. **norm を multiplicative map として bundle する**
   - unit criterion を一般的な multiplicative norm argument へ寄せる余地がある。

現行 proof は依存が浅く、数学的な逆元 `conj x` が明示されるため監査性は高い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem が直接必要とする表面は、existential/conjunction 構築、`simpa`、`change`、`rw`、可換環の `mul_comm` である。

高度な解析や数論ライブラリは本 theorem 自身では不要だが、同一 module の上流で `ring`、`norm_num`、整数整除などを使用しているため、module 全体の最小 import はより広い。今回は Lean build を行わないため、厳密な最小 import 集合は未検証である。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行の explicit witness + 二方向 proof
- B: 右逆元を局所 lemma 化して重複を除く
- C: 標準 `IsUnit` API を中心に構成する
- D: `RingEquiv` として bundle した共役から構造的に導く
- E: 座標を直接展開して inverse equality を証明する

比較軸は proof size、raw/standard API crossing の回数、数学的 provenance、Mathlib generic API の再利用度、refactor 耐性、証明監査性である。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

正本 source では 0198 `GoldenUnit` の直後に本 theorem が置かれ、その次に `goldenUnit_of_norm_eq_neg_one` が続く。

対象ブランチには日本語・英語 PDF が存在するが、本 theorem に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0200 `goldenUnit_of_norm_eq_neg_one`** である。

```lean
theorem goldenUnit_of_norm_eq_neg_one {x : GoldenInt} (h : goldenNorm x = -1) :
    GoldenUnit x := by
  refine ⟨-goldenConj x, ?_, ?_⟩
  ...
```

0199 では $N(x)=1$ のとき共役そのものが逆元になった。0200 では $N(x)=-1$ の符号を補うため、`-goldenConj x` を逆元として構成する。これで norm `±1` から unit への二つの基本分岐が揃う。