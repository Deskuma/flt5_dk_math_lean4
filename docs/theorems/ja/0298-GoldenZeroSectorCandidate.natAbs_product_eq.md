# 0298 — `GoldenZeroSectorCandidate.natAbs_product_eq`

## 宣言種別

これは **`theorem`** である。

zero-sector candidate が保持する符号付き product equation

$$
s\,H(r,s)=-5^6a^{10}
$$

全体へ `Int.natAbs` を適用し、後続の自然数上の tenth-power factor comparison に直接使える magnitude identity

$$
|s|\,|H(r,s)|=5^6a^{10}
$$

を取り出す。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- Natural absolute-value form of the signed product equation. -/
theorem natAbs_product_eq (p : GoldenZeroSectorCandidate) :
    p.s.natAbs * (goldenFifthSndFactor p.r p.s).natAbs =
      5 ^ 6 * p.a ^ 10 := by
  have h := congrArg Int.natAbs p.product_eq
  simpa [Int.natAbs_mul, pow_succ] using h
```

結論は自然数 `ℕ` 上の等式である。

数学的には

$$
|p.s|\,|H(p.r,p.s)|=5^6p.a^{10}
$$

を表す。

ここで

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4
$$

は `goldenFifthSndFactor r s` である。

## 数学的意味

0290 `GoldenZeroSectorCandidate` は raw zero-sector arithmetic から得られた符号付き積

```lean
p.product_eq :
  p.s * goldenFifthSndFactor p.r p.s =
    -((5 : ℤ) ^ 6 * (p.a : ℤ) ^ 10)
```

を保存している。

この式は整数 `ℤ` 上では符号を含んでいる。一方、同じ candidate は既に

```lean
p.s_natAbs_eq : p.s.natAbs = 5 ^ 6 * p.c ^ 10
p.H_natAbs_eq : (goldenFifthSndFactor p.r p.s).natAbs = p.d ^ 10
```

という二つの自然数上の magnitude split を保持している。

後続でこれら三式を直接比較するためには、`product_eq` も `ℕ` 上の magnitude identity に変換しておくのが自然である。本 theorem がその型・符号境界を処理する。

整数の絶対値について

$$
|xy|=|x|\,|y|
$$

であり、また

$$
|-5^6a^{10}|=5^6a^{10}
$$

なので、結論は直観的には即座である。

## 証明全体での役割

0296 `s_eq_neg_five_pow_mul_tenth` と 0297 `H_eq_tenth` は individual factor の符号を確定し、

$$
s=-5^6c^{10},
\qquad
H=d^{10}
$$

を与えた。

本 0298 は別方向から、元の product equation 全体の magnitude を取り出す。

$$
|s|\,|H|=5^6a^{10}.
$$

ここへ candidate field の

$$
|s|=5^6c^{10},
\qquad
|H|=d^{10}
$$

を代入すると

$$
(5^6c^{10})d^{10}=5^6a^{10}.
$$

正の共通因子 $5^6$ を消去すれば

$$
(cd)^{10}=a^{10}.
$$

自然数のべきの単射性から

$$
a=cd
$$

を得る。これは直後の 0299 `GoldenZeroSectorCandidate.a_eq_c_mul_d` が実行する内容である。

従って本 theorem は、signed zero-sector equation と chosen tenth-power split を同じ `ℕ` の乗法世界へ揃え、base factorization `a=c*d` を可能にする bridge である。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate.product_eq`

0290 の structure field で、本 theorem の唯一の DkMath 側の直接入力である。

概念的には

$$
p.s\,H(p.r,p.s)=-5^6p.a^{10}
$$

を保持する。

### `congrArg`

等式

```lean
x = y
```

へ関数 `f` を両辺適用して

```lean
f x = f y
```

を得る Lean の基本補題である。

本 theorem では

```lean
congrArg Int.natAbs p.product_eq
```

により、符号付き整数等式全体へ `Int.natAbs : ℤ → ℕ` を適用する。

### `Int.natAbs_mul`

整数積の natural absolute value が積に分配されることを与える。

概念的には

$$
\operatorname{natAbs}(xy)=\operatorname{natAbs}(x)\operatorname{natAbs}(y).
$$

これにより左辺が theorem の目標形へ正規化される。

### `pow_succ`

現行証明の `simpa` 正規化に含まれている。

右辺の負号・積・べきに `Int.natAbs` を適用した結果を、自然数の

```lean
5 ^ 6 * p.a ^ 10
```

へ整形する過程で利用される。

ここで `pow_succ` がなぜ simp set に明示的に必要かは、現行 Lean コード上で確認できるが、これを除去しても通るかどうかは Lean build を行っていないため未確認である。

## 証明または構築の流れ

1. `p.product_eq` を取得する。
2. `congrArg Int.natAbs` で等式の両辺へ natural absolute value を適用し、`h` を作る。
3. 左辺の `natAbs` of product を `Int.natAbs_mul` で積へ分解する。
4. 右辺の負号および整数べきの natural absolute value を simp が自然数べきへ正規化する。
5. `simpa [Int.natAbs_mul, pow_succ] using h` で目標形へ一致させる。

証明本体は二行だが、「等式そのものを関数で写し、その後 target algebra へ正規化する」という非常に典型的な Lean の構成である。

## Lean 固有の処理

数学では単に「両辺の絶対値を取る」と書くところを、Lean では

```lean
congrArg Int.natAbs p.product_eq
```

と表現する。

ここで重要なのは `Int.abs` ではなく `Int.natAbs` を選んでいる点である。`natAbs` の値域は `ℕ` なので、結果の theorem はそのまま `p.s_natAbs_eq` と `p.H_natAbs_eq` に rewrite できる。

つまり本 theorem は単なる符号除去だけでなく、後続計算のために **整数世界から自然数世界へ型を移す** 役割も担う。

また、右辺には負号と整数 cast が含まれているが、それらの細かな正規化は `simpa` に委ねられている。このため表面上は短いが、simp lemma 群への依存は比較的強い。

## 冗長・重複箇所

0296–0297 も absolute value と符号を扱うが、本 theorem は目的が異なる。

- 0296: `|s|` と `s<0` から signed exact equation を復元する。
- 0297: `|H|` と `H>0` から signed exact equation を復元する。
- 0298: signed product equation 全体から `ℕ` 上の magnitude equation を作る。

従って概念上は同じ absolute-value 層に属するものの、0298 を 0296–0297 から機械的に置き換えるのは必ずしも良くない。0298 は `product_eq` から直接導かれるため、individual sign theorems への依存を持たず、`a_eq_c_mul_d` に必要な magnitude information を最短経路で供給している。

一方、`pow_succ` を simp list に明示する部分はやや実装依存に見える。Mathlib の simp set の変化や別正規化によって不要になる可能性はある。

## 最適化候補

1. `have h := ...` を置かず、

```lean
simpa [Int.natAbs_mul, pow_succ] using
  congrArg Int.natAbs p.product_eq
```

のように一式へ圧縮できる可能性がある。
2. `[pow_succ]` を除いても `simpa [Int.natAbs_mul]` だけで通るかは検証候補である。
3. 逆に、simp 依存を減らして右辺の `natAbs` 正規化を明示的な補題で分解すれば、Mathlib 更新に対してより安定する可能性がある。ただし現行二行証明の可読性は高い。
4. 0299 の用途だけを考えるなら `natAbs_product_eq` を局所 `have` に埋め込むことも可能だが、signed equation から magnitude equation への変換は独立した意味を持つため、named theorem として残す価値がある。

これらは Lean build を行っていないため **未検証** である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

standalone の generated-source manifest では本宣言は

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

に属する。

本 theorem 自体の主要な外部機能は

- `congrArg`
- `Int.natAbs`
- `Int.natAbs_mul`
- `pow_succ`
- `simpa`

である。

`linarith`, `nlinarith`, `ring`, `omega`, `positivity`, `norm_num`, `exact_mod_cast` は本 theorem 自体では使わない。

最小 import 候補としては整数の absolute-value API、べき、simp 基盤を含む個別 Mathlib module へ縮小できる可能性がある。しかし指定に従い Lean build は実行していないため、厳密な最小 import 集合は **未確認** である。実際の source module 全体の依存と、本 theorem 単体の理論上の最小 import は区別すべきである。

## Comparator challenge 化の可否

**非常に適している。** 難度は低～中程度である。

例えば

```lean
theorem challenge (p : GoldenZeroSectorCandidate) :
    p.s.natAbs * (goldenFifthSndFactor p.r p.s).natAbs =
      5 ^ 6 * p.a ^ 10 := by
  ...
```

だけを提示し、`p.product_eq` から導かせる。

評価点は、

- 「両辺に `Int.natAbs` を適用する」を `congrArg` で表現できるか
- `Int.natAbs_mul` を発見できるか
- `Int.natAbs : ℤ → ℕ` を選ぶことで後続 field と型が一致することを理解できるか
- `simpa` がどこまで符号・cast・べきを正規化するか把握できるか

である。

短い証明なので Comparator では tactic choice と API 発見能力の差が明瞭に出る。

## PDF との対応

対象 branch の repository tree には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

GitHub コネクタでは両 PDF の blob の存在までは確認できたが、通常テキスト取得経路では binary 本文を解析できなかった。また raw PDF の直接取得も今回の環境では成功しなかった。そのため PDF 内の具体的ページ番号・節番号・本 theorem に相当する説明位置は **確認できていない**。

従って本稿では現行 Lean 正本 `Flt5DkMath/FLT5StandAlone.lean` を技術的内容の最優先根拠とし、PDF の未確認部分について推測は行わない。

## 次に読むべき宣言

次は **0299 `GoldenZeroSectorCandidate.a_eq_c_mul_d`**。種別は `theorem` である。

Lean 正本では本 0298 の直後にあり、冒頭は次の形である。

```lean
/-- The original tenth-power base is exactly the product of the split bases. -/
theorem a_eq_c_mul_d (p : GoldenZeroSectorCandidate) : p.a = p.c * p.d := by
  have hprod := p.natAbs_product_eq
  rw [p.s_natAbs_eq, p.H_natAbs_eq] at hprod
  have hpows : (p.c * p.d) ^ 10 = p.a ^ 10 := by
    ...
```

本 theorem の magnitude product identity に二つの split

$$
|s|=5^6c^{10},
\qquad
|H|=d^{10}
$$

を代入し、共通因子 $5^6$ を消去して tenth powers を比較し、最終的に

$$
a=cd
$$

を復元する。
