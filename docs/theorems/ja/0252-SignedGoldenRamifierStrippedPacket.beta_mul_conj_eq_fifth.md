# 0252 — `SignedGoldenRamifierStrippedPacket.beta_mul_conj_eq_fifth`

## Lean の型

```lean
/-- The stripped element times its conjugate is an embedded fifth power. -/
theorem SignedGoldenRamifierStrippedPacket.beta_mul_conj_eq_fifth
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    goldenMul p.beta (goldenConj p.beta) =
      goldenPow (goldenOfInt (p.exceptional.powerSplit.b : ℤ)) 5 := by
  rw [golden_mul_conj, p.beta_norm, goldenOfInt_pow_five]
```

これは `theorem` であり、ramifier を除去済みの packet が保持する `beta` とその共役の積が、黄金整数環内部で真正な第五冪として書けることを示す。

## 数学的主張

`SignedGoldenRamifierStrippedPacket` はすでに

$$
N(\beta)=b^5
$$

を field `beta_norm` として保持している。一方、黄金整数の一般公式 0176 `golden_mul_conj` により

$$
\beta\overline{\beta}=N(\beta)
$$

である。さらに 0251 `goldenOfInt_pow_five` によって、整数側の第五冪を黄金整数環内部の第五冪へ移せる。

したがって本 theorem は

$$
\beta\overline{\beta}
=N(\beta)
=b^5
=(\operatorname{goldenOfInt} b)^5
$$

を Lean の raw API で表したものである。

右辺の基底元は

$$
z:=\operatorname{goldenOfInt}(b)
$$

なので、本 theorem により

$$
\beta\overline{\beta}=z^5
$$

という「二因子の積が第五冪」という標準的な factor-extraction 問題へ到達する。

## 証明全体での役割

0241–0247 では `beta` と `goldenConj beta` の相対素性が確立され、0245 `SignedGoldenConjugateCoprimePacket` に certificate として束ねられた。

一方、0231 `SignedGoldenRamifierStrippedPacket` は `beta_norm : goldenNorm beta = b^5` を保持している。本 theorem はこの norm 情報を、環内部の積の第五冪等式へ変換する。

これにより後続の generic contract `GoldenCoprimeFactorOfFifthPower` に必要な二つの入力が揃う。

1. `GoldenRelPrime beta (goldenConj beta)`
2. `goldenMul beta (goldenConj beta) = goldenPow z 5`

したがって 0252 は、**ノルムが第五冪である** という整数値の情報を、**相対素な二因子の積そのものが第五冪である** という環論的入力へ昇格する bridge である。

この変換が済むことで、Euclidean-domain / gcd machinery を使う generic coprime-factor theorem が `beta = epsilon * gamma^5` を返せる形になる。

## 直接依存する定義・補題

proof が直接使用する named theorem / field は三つである。

- 0176 `golden_mul_conj`
- `p.beta_norm`
- 0251 `goldenOfInt_pow_five`

statement 側では次の定義を使う。

- `SignedGoldenRamifierStrippedPacket`
- `GoldenInt`
- `goldenConj`
- `goldenMul`
- `goldenOfInt`
- `goldenPow`

概念的な依存は極めて明瞭で、

$$
\beta\overline{\beta}=N(\beta),
\qquad
N(\beta)=b^5,
\qquad
\operatorname{goldenOfInt}(b^5)=\operatorname{goldenOfInt}(b)^5
$$

の三本を合成するだけである。

## 証明の流れ

proof は一行である。

```lean
rw [golden_mul_conj, p.beta_norm, goldenOfInt_pow_five]
```

### 1. 共役積をノルムへ移す

`golden_mul_conj` により

```lean
goldenMul p.beta (goldenConj p.beta)
```

を

```lean
goldenOfInt (goldenNorm p.beta)
```

へ書き換える。

### 2. packet の norm certificate を使う

`p.beta_norm` により

```lean
goldenNorm p.beta
```

を

```lean
(p.exceptional.powerSplit.b : ℤ) ^ 5
```

へ書き換える。

### 3. 整数埋め込みの第五冪を環内部の第五冪へ変換する

0251 `goldenOfInt_pow_five` により

```lean
goldenOfInt ((p.exceptional.powerSplit.b : ℤ) ^ 5)
```

を

```lean
goldenPow (goldenOfInt (p.exceptional.powerSplit.b : ℤ)) 5
```

へ書き換え、goal が閉じる。

## Lean 固有の処理

`rw` は三つの equality theorem を左から右へ順番に適用している。

ここで重要なのは、本 theorem が座標を一切展開しないことだ。`beta` の具体座標、`goldenConj` の式、`goldenMul` の多項式、`goldenPow` の再帰はいずれも触らない。

つまり 0252 は、これまで整備してきた theorem API が十分に抽象化されていることを示す良い例である。

また `p.beta_norm` は dependent structure field projection であり、`p` の内部に保存された `exceptional.powerSplit.b` と自動的に整合する型を持つ。そのため別途 `b` を取り出して等式を運搬する必要がない。

## 冗長・重複箇所

数学的には、本 theorem は三つの既存 equality の単純合成なので、新しい独立情報は少ない。

理論上は downstream で毎回

```lean
rw [golden_mul_conj, p.beta_norm, goldenOfInt_pow_five]
```

と書けば済む。

しかし dedicated theorem を置く利点は大きい。

- generic coprime-factor theorem に渡す形を一つの名前で参照できる。
- downstream が `beta_norm` の provenance を知らなくてよい。
- `golden_mul_conj` と整数埋め込み bridge の内部経路を隠蔽できる。
- 「stripped element とその共役の積が第五冪」という数学的節目が theorem 名として残る。

したがって論理的には wrapper だが、proof graph 上では重要な interface theorem である。

## 最適化候補

1. **現行 proof を維持する**
   - 三 rewrite のみで、依存関係が明瞭。

2. **`simpa` 形式へ圧縮する**
   - `golden_mul_conj p.beta` を起点として `p.beta_norm` と 0251 を simp に渡す方法が考えられる。
   - ただし exact な simp behavior は Lean build 未実施なので未検証。

3. **標準 `*` / `^` notation 版 theorem を公開する**
   - 0159 `golden_mul_eq`、0160 `golden_pow_eq` を使って

```lean
p.beta * goldenConj p.beta =
  (goldenOfInt (...) : GoldenInt) ^ 5
```

   のような Mathlib 標準 API 寄りの statement を用意できる。

4. **norm を multiplicative map、integer embedding を `RingHom` として bundle する**
   - generic `map_pow` 等に寄せることで surrounding bridge theorem 群を減らせる可能性がある。

現行 theorem は FLT5 downstream の exact consumer shape に一致しているため、局所的な最適化優先度は低い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身の proof は `rw` のみであり、直接必要な Mathlib 表面は極めて小さい。

実質的な依存は同一 development 内の

- `GoldenInt` algebra API
- conjugation / norm API
- stripped packet
- integer embedding / power API

である。

ただし `SignedGoldenFifthPower.lean` 全体は後続で generic factorization contract を扱い、さらに別 module の Euclidean-domain machinery へ接続するため、最小 import は module 単位で評価すべきである。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。proof 自体が小さいため、API 設計差を比較しやすい。

比較候補は次の通り。

- A: 現行の三段 `rw`
- B: `simpa` + `golden_mul_conj p.beta`
- C: 標準 `*` / `^` notation に正規化して証明
- D: `RingHom` / multiplicative norm を bundle した generic API から導出
- E: 座標を直接展開する低レベル proof

比較軸は proof 長、依存深度、数学的 provenance の可視性、raw API と標準 API の境界、upstream refactor への頑健性、standalone 監査性である。

特に A と E の比較は、「確立済み theorem API を合成する証明」と「座標を再計算する証明」の差を明確に示す。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenFifthPower.lean` generated section である。

正本 source では 0251 `goldenOfInt_pow_five` の直後に本 theorem が置かれ、その次に generic contract `GoldenCoprimeFactorOfFifthPower` が続くことを確認した。

対象ブランチには `docs/pdf/FLT5-main-ja-v0-r1.pdf` と `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0253 `GoldenCoprimeFactorOfFifthPower`** である。

```lean
abbrev GoldenCoprimeFactorOfFifthPower : Prop :=
  ∀ x y z : GoldenInt,
    GoldenRelPrime x y →
    goldenMul x y = goldenPow z 5 →
    ∃ epsilon gamma : GoldenInt,
      GoldenUnit epsilon ∧
      x = goldenMul epsilon (goldenPow gamma 5)
```

これは theorem ではなく `abbrev : Prop` であり、

$$
xy=z^5,
\qquad
\operatorname{RelPrime}(x,y)
$$

ならば

$$
x=\varepsilon\gamma^5
$$

とできる、generic coprime-factor extraction contract を定義する。

0252 までで stripped packet がこの contract の入力形へ完全に変換されたので、0253 からは packet 固有の算術を離れ、Euclidean-domain 上の一般的な第五冪因子抽出インターフェースへ進む。