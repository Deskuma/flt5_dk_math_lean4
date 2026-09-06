# 0325 — `goldenZeroSectorInversionPacket`

## 宣言種別

これは theorem ではなく **`def`** である。

直前の `GoldenZeroSectorInversionPacket` structure に対し、任意の `GoldenZeroSectorCandidate` から、その candidate 上で既に証明済みの事実を各 field に詰めて certified packet を構築する定義である。

## Lean の型

```lean
/-- Every raw zero-sector candidate deterministically yields its inversion packet. -/
def goldenZeroSectorInversionPacket (p : GoldenZeroSectorCandidate) :
    GoldenZeroSectorInversionPacket where
  source := p
  H_pos := p.H_pos
  s_neg := p.s_neg
  c_pos := p.c_pos
  d_pos := p.d_pos
  s_eq := p.s_eq_neg_five_pow_mul_tenth
  H_eq := p.H_eq_tenth
  a_eq := p.a_eq_c_mul_d
  coprime_c_d := p.coprime_c_d
  five_not_dvd_d := p.five_not_dvd_d
  d_odd := p.d_odd
  discriminant_eq := p.discriminant_eq
  factor_product := p.A0_mul_B0
  factor_difference := p.B0_eq_A0_add
  factor_sum := p.factor_sum
  square_reconstruction := p.square_reconstruction
  W_pos := p.W_pos
  A_pos := p.A_pos
  A_lt_B := p.A_lt_B
  B_pos := p.B_pos
  A0_cast := p.A0_cast
  B0_cast := p.B0_cast
  A0_pos := p.A0_pos
  B0_pos := p.B0_pos
```

型としては

```lean
goldenZeroSectorInversionPacket :
  GoldenZeroSectorCandidate → GoldenZeroSectorInversionPacket
```

である。

## 数学的意味

この定義そのものは新しい数論命題を証明しない。意味は、零セクター候補 `p` について既に確立した不変量を、一つの認証済みデータとしてまとめ直すことである。

packet には特に

$$
s=-5^6c^{10},
$$

$$
H=d^{10},
$$

$$
a=cd,
$$

$$
\gcd(c,d)=1,
$$

$$
A_0B_0=4Q^5,
$$

$$
B_0=A_0+8d^5,
$$

さらに signed factors の正性・順序・cast equation などが保存される。

したがって本 `def` は「零セクター反転の結果を下流 factorization がそのまま消費できる形へ変換する」決定的な写像である。

## 証明全体での役割

0324 では packet の schema だけを定義した。本 0325 はその schema が単なる理想的インターフェースではなく、すべての `GoldenZeroSectorCandidate` から実際に構築可能であることを示す。

これにより、証明の流れは

```text
GoldenZeroSectorCandidate
        ↓
goldenZeroSectorInversionPacket
        ↓
GoldenZeroSectorInversionPacket
        ↓
SignedGoldenZeroSectorFactorization
```

と明確に分離される。

以後の factorization 側は candidate 上の長い証明列を再追跡せず、packet の field projection だけを利用できる。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate`

入力型である。

### `GoldenZeroSectorInversionPacket`

出力型である。0324 で定義された structure の全 field を本 `def` が埋める。

### 使用する上流 theorem / definition

各 field は次の既存 API に一対一対応する。

- `p.H_pos`
- `p.s_neg`
- `p.c_pos`
- `p.d_pos`
- `p.s_eq_neg_five_pow_mul_tenth`
- `p.H_eq_tenth`
- `p.a_eq_c_mul_d`
- `p.coprime_c_d`
- `p.five_not_dvd_d`
- `p.d_odd`
- `p.discriminant_eq`
- `p.A0_mul_B0`
- `p.B0_eq_A0_add`
- `p.factor_sum`
- `p.square_reconstruction`
- `p.W_pos`
- `p.A_pos`
- `p.A_lt_B`
- `p.B_pos`
- `p.A0_cast`
- `p.B0_cast`
- `p.A0_pos`
- `p.B0_pos`

本定義には独自の補助 lemma はない。

## 構築の流れ

1. `source := p` で元 candidate を保存する。
2. 符号条件 `H_pos`, `s_neg`, `c_pos`, `d_pos` をコピーする。
3. `s_eq`, `H_eq`, `a_eq` で再パラメータ化情報を保存する。
4. `coprime_c_d`, `five_not_dvd_d`, `d_odd` で算術的制約を保存する。
5. discriminant、積、差、和、平方再構成を保存する。
6. signed factors の正性と順序を保存する。
7. `A0`, `B0` の cast equation と自然数正性を保存する。

すべての field が既存 theorem の proof term なので、tactic による新規証明は発生しない。

## Lean 固有の処理

### structure literal

```lean
GoldenZeroSectorInversionPacket where
  ...
```

という structure literal によって dependent record を構築している。

### proof term の再利用

例えば

```lean
factor_product := p.A0_mul_B0
```

は theorem を「呼び出して証明をやり直す」のではなく、既に存在する proof term を structure field に格納している。

### dependent typing

`source := p` を設定した後の各 field は同じ `p` に依存する。そのため別 candidate 由来の証明を誤って混ぜることは型検査で拒否される。

### namespace / generated-source 境界

この `def` の直後で `DkMath.FLT.Five` namespace が一度閉じられ、`SignedGoldenZeroSectorInversion.lean` generated source が終了する。続く `SignedGoldenZeroSectorFactorization.lean` が packet を入力として開始する。よって本宣言はファイル境界の実質的な出口である。

## 冗長・重複箇所

field assignment はほぼすべて

```lean
field := p.corresponding_theorem
```

という単純な転記であり、コード上は冗長に見える。

ただしこれは 0324 の explicit API schema と対になる意図的な冗長性である。各 field の意味と provenance が明示され、packet の内容を読みやすくしている。

一方で structure field を追加・削除するとこの constructor も同期更新が必要になるため、保守コストは存在する。

## 最適化候補

候補としては、

1. `source` だけを保持し、他の事実を namespace theorem として都度導出する。
2. 小さな nested packet に分割し、それらを合成する。
3. 現行通り全 field を明示して、下流 proof の単純さを優先する。

が考えられる。

現行設計は 3 であり、module boundary と provenance の明示性が高い。どの field が本当に不要かは downstream 全体での利用箇所と Lean build を確認しなければ断定できないため、縮約案は **未検証** である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用する。

本 `def` 自身は新しい tactic や高度な Mathlib API を使用せず、主に

- structure construction
- project 内の既存 theorem projection
- `Nat`, `Int`, `Odd`, `Nat.Coprime`, divisibility, order, powers

を型として参照するだけである。

しかし出力 structure の field 型が広い依存閉包を持つため、正確な最小 Mathlib import 集合は本実行では Lean build を行っておらず **未確認** である。

## Comparator challenge 化の可否

**証明 tactic の Comparator challenge としては不向きだが、API 構築設計の Comparator としては適している。**

比較候補は、

- explicit structure literal
- nested packet constructor
- source-only wrapper と derived theorem API
- field assignment を補助 constructor 群へ分割する設計

である。

評価軸は、可読性、依存関係の透明性、保守コスト、downstream proof の短さ、field provenance の追跡容易性となる。

## PDF との照合

対象 branch の repository tree には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

ただし GitHub コネクタは binary PDF 本文を text として返さないため、本実行では具体的ページ・節・式番号との直接照合は **未確認** である。確認できない箇所を推測では補っていない。

## 次に読むべき宣言

次の generated source `SignedGoldenZeroSectorFactorization.lean` に入り、次の宣言は private theorem

```lean
private theorem coprime_of_odd_of_no_common_odd_prime
    {m n : ℕ} (hm : Odd m)
    (hodd : ∀ q : ℕ, Nat.Prime q → q ≠ 2 → q ∣ m → q ∣ n → False) :
    Nat.Coprime m n := by
  ...
```

である。

これは「`m` が奇数で、2 以外の共通素因子が存在しないなら `m,n` は互いに素」という factorization module の局所補題である。museum の依存順では **0326 `coprime_of_odd_of_no_common_odd_prime`** として読むのが自然である。
