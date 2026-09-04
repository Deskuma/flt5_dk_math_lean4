# 0305 — `GoldenZeroSectorCandidate.U_nonneg`

## 宣言種別

これは **`theorem`** である。

0304 `GoldenZeroSectorCandidate.d_odd` までで split base `d` に対する parity / five-adic 条件を整えた後、zero-sector inversion の補助量 `U` の符号制御へ移る最初の宣言である。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- The diagonal sum is nonnegative independently of the candidate hypotheses. -/
theorem U_nonneg (p : GoldenZeroSectorCandidate) :
    0 ≤ zeroSectorU p.r p.s := by
  unfold zeroSectorU
  positivity
```

結論は整数上の順序命題

```lean
0 ≤ zeroSectorU p.r p.s
```

である。

## 数学的意味

定義は

```lean
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s

def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

である。したがって

$$
U(r,s)=X(r,s)^2+5s^2,
$$

ただし

$$
X(r,s)=2r+s.
$$

平方は常に非負であり、$5>0$ なので $5s^2$ も非負である。従って

$$
U(r,s)\ge0
$$

が任意の整数 $r,s$ に対して成り立つ。

この theorem の重要点は、`GoldenZeroSectorCandidate` が持つ Fermat-five 由来の仮定、coprimality、符号条件、tenth-power split などを一切使わないことである。docstring の “independently of the candidate hypotheses” は文字通りで、`p` から利用しているのは座標 `p.r`, `p.s` だけである。

## 証明全体での役割

zero-sector inversion では後続で

$$
U-5s^2=X^2
$$

という square reconstruction を使い、さらに difference-of-squares や discriminant factorization へ進む。

その際 `U` が非負であることは、`U` を平方量や符号付き因子の組み合わせとして扱うための基礎的な順序情報となる。

0305 は深い数論的内容を追加する theorem ではない。むしろ、後続の代数変形で繰り返し必要になり得る「明らかな非負性」を一度 named theorem として固定し、proof state から局所的な positivity 証明を分離する役割を持つ。

また、0304 までの `d` に関する局所算術から、0305 以降は `U`, `W`, `X` といった再構成量の恒等式へ話題が切り替わる。その境界を示す宣言でもある。

## 直接依存する定義・補題

### `zeroSectorU`

本 theorem が直接 unfold する定義である。

```lean
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

この形そのものが非負性を露出している。

### `zeroSectorX`

`zeroSectorU` の内部で用いられる diagonal coordinate。

```lean
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s
```

ただし proof では `zeroSectorX` を unfold する必要はない。`(zeroSectorX p.r p.s)^2` が平方であるという形だけで `positivity` が処理できる。

### `positivity`

Mathlib の positivity tactic。平方の非負性、正の定数 `5`、積と和の非負性を自動的に合成して目標を閉じる。

本 proof の数学的依存は実質的にこれだけであり、candidate 固有 theorem への依存はない。

## 証明または構築の流れ

1. `unfold zeroSectorU` により目標を

   ```lean
   0 ≤ zeroSectorX p.r p.s ^ 2 + 5 * p.s ^ 2
   ```

   の形へ展開する。
2. `positivity` が
   - `zeroSectorX p.r p.s ^ 2 ≥ 0`
   - `p.s ^ 2 ≥ 0`
   - `5 ≥ 0`
   - 非負数の積と和は非負

   を自動認識する。
3. 追加の candidate hypothesis を使わず目標を閉じる。

紙上では「平方の和なので非負」の一行に相当する。

## Lean 固有の処理

Lean 固有のポイントは、定義を一段だけ unfold することで `positivity` が認識可能な標準形へ変換していることである。

`zeroSectorU` のままでは tactic が定義内部を自動展開する保証に依存することになるため、

```lean
unfold zeroSectorU
```

で proof interface を明示している。

一方 `zeroSectorX` は unfold していない。`positivity` にとって底の式が何であるかは不要で、任意の整数式の平方が非負であることだけで十分だからである。

この「必要な定義だけを unfold し、内部式は opaque のまま残す」形は、proof の安定性と可読性の両面でよい設計である。

## 冗長・重複箇所

本 theorem 自体にはほぼ冗長性がない。

理論上は theorem を置かず、必要な箇所ごとに

```lean
unfold zeroSectorU
positivity
```

を繰り返すこともできる。しかし後続 proof で `U` の非負性を複数回使うなら named theorem にする方が重複を減らす。

また `p : GoldenZeroSectorCandidate` は数学的には過剰な引数である。実際の主張はより一般に

```lean
theorem zeroSectorU_nonneg (r s : ℤ) : 0 ≤ zeroSectorU r s := by
  unfold zeroSectorU
  positivity
```

と書ける。

従って candidate namespace 内の theorem は general lemma の specialization と見ることができる。ただし現行 API は後続の `p.U_nonneg` という field-like notation を優先した設計と考えられる。

## 最適化候補

最も自然な最適化候補は、candidate 非依存性を型レベルにも反映して一般補題へ切り出すことである。

例えば概念的には

```lean
theorem zeroSectorU_nonneg (r s : ℤ) :
    0 ≤ zeroSectorU r s := by
  unfold zeroSectorU
  positivity
```

を先に置き、現在の theorem を

```lean
theorem U_nonneg (p : GoldenZeroSectorCandidate) :
    0 ≤ zeroSectorU p.r p.s :=
  zeroSectorU_nonneg p.r p.s
```

とする案がある。

利点は theorem の数学的強さが明確になり、candidate 外でも再利用できる点である。一方、現状は proof が二行しかないため、抽象化により declaration 数が増えるコストもある。

また `simpa [zeroSectorU] using ...` 型の書き方へ変える必要性はない。現行の `unfold` + `positivity` が最短かつ意図が明瞭である。

これらの候補は Lean build を行っていないため未検証であり、本 museum 作業ではコード変更しない。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem が直接必要とする機能は少なくとも次の系統である。

- ordered ring / integer order
- power nonnegativity
- `positivity` tactic
- `zeroSectorU`, `zeroSectorX` の定義

`ring`, `omega`, `linarith`, `norm_num`, `exact_mod_cast` などは本 proof では不要である。

ただし standalone artifact は umbrella import を使っており、本作業では Lean build を行わないため、厳密な最小 Mathlib import 集合は **未確認** である。

import 最適化を行う場合は元 source module `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` の import graph を確認し、`Mathlib` 全体ではなく algebra/order と positivity tactic に必要なモジュールへ縮小できるかをビルドで検証すべきである。

## Comparator challenge 化の可否

**可能だが、単体ではかなり易しい。**

statement と `zeroSectorU` の定義を与えれば、期待解はほぼ

```lean
unfold zeroSectorU
positivity
```

で終わる。

したがって Comparator challenge とするなら、単なる穴埋めよりも次の比較が教育的である。

- `zeroSectorX` まで unfold する必要があるか。
- `nlinarith [sq_nonneg ...]` のような手動証明と `positivity` のどちらが簡潔か。
- candidate hypothesis を使わずに証明できることを見抜けるか。

難度は初級。Lean tactic の `positivity` と「必要最小限の unfold」を学ぶ小問としては適している。

## PDF との照合

対象 branch には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

ただし GitHub コネクタの通常の text fetch では binary PDF 本文を取得できないため、本作業では PDF 内の具体的ページ・節・式番号と 0305 を直接照合できていない。従って PDF 上の位置については推測しない。

本解説の Lean code、宣言順、技術的意味、直接依存は repository 内の `Flt5DkMath/FLT5StandAlone.lean` を正本としている。

## 次に読むべき宣言

次の宣言は 0306 `GoldenZeroSectorCandidate.square_reconstruction`、種別は **`theorem`** である。

Lean 正本では `U_nonneg` の直後に

```lean
/-- The reconstructed square coordinate is retained exactly. -/
theorem square_reconstruction (p : GoldenZeroSectorCandidate) :
    zeroSectorU p.r p.s - 5 * p.s ^ 2 = zeroSectorX p.r p.s ^ 2 := by
  unfold zeroSectorU
  ring
```

と続く。

0305 が `U` の順序情報を固定したのに対し、0306 は

$$
U-5s^2=X^2
$$

という exact reconstruction identity を与える。ここから `U`, `X`, `s` の関係が単なる非負性から具体的な平方恒等式へ強化され、後続の factorization / discriminant 操作へ進む。
