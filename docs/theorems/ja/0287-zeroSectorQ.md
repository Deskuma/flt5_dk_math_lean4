# 0287 — `zeroSectorQ`

## 宣言種別

これは **`def`** である。

theorem ではなく、zero-sector inversion で現れる積 `A * B` を「定数係数 × 5 乗」の形にまとめるための自然数値の補助量 `Q` を定義する宣言である。

## Lean の型

```lean
/-- The fifth-power mass `Q = 5^5*c^8` in `A*B = 4*Q^5`. -/
def zeroSectorQ (c : ℕ) : ℕ :=
  5 ^ 5 * c ^ 8
```

Lean 上の完全な型は

```lean
zeroSectorQ : ℕ → ℕ
```

である。

入力 `c : ℕ` に対して

$$
Q=5^5c^8
$$

を返す。

## 数学的意味

この定義の狙いは、zero-sector で既に得られている tenth-power split の変数 `c` を、後続の inversion factorization に適した **5 乗の質量** に再編成することにある。

`zeroSectorQ c` 自体は単なる積

$$
5^5c^8
$$

だが、その 5 乗は

$$
Q^5=(5^5c^8)^5=5^{25}c^{40}
$$

となる。

したがって後続の積等式

$$
A B = 4Q^5
$$

では、`c` に由来する高い冪を一つの fifth-power block として扱える。

ここで重要なのは、`Q` が新しい独立変数ではないことである。`Q` は `c` から決定的に作られる略記であり、後続証明で repeatedly appearing expression `5 ^ 5 * c ^ 8` を一つの名前に封じ込めている。

## 証明全体での役割

0282 `zeroSectorX` から 0286 `zeroSectorB` までは、

$$
X=2r+s,
\qquad
U=X^2+5s^2,
\qquad
W=4d^5,
$$

$$
A=U-W,
\qquad
B=U+W
$$

という inversion 座標と対称因子を構成した。

本宣言 0287 は、それらとは異なり `r,s,d` 側の座標を定義するものではない。0281 `zeroSector_tenthPower_split` で生じた `c` 側の冪構造を、`A * B` の積に合わせてまとめる役を持つ。

実際、後続 theorem `factor_product` では正本コード上、

```lean
4 * (zeroSectorQ p.c : ℤ) ^ 5
```

という形が右辺に現れ、証明の最後で

```lean
unfold zeroSectorQ
push_cast
ring
```

によって `Q` の定義を展開している。

したがって本定義は、**zero-sector arithmetic で得た tenth-power data と inversion factor pair `(A,B)` を fifth-power factorization の言語で接続する名前付き境界** と見るのが適切である。

## 直接依存する定義・補題

本宣言そのものが直接依存する DkMath 固有の定義・補題はない。

```lean
def zeroSectorQ (c : ℕ) : ℕ :=
  5 ^ 5 * c ^ 8
```

は `Nat` 上の数値リテラル、乗算、冪だけで閉じている。

ただし **意味上の依存** としては、直前までの zero-sector 証明で得られた tenth-power split の `c` が入力である。特に正本の後続 `factor_product` では `p.c` が渡されるため、`c` は inversion candidate の構成データの一部として使われる。

## 構築の流れ

`def` なので証明 tactic は存在しない。Lean は右辺をそのまま定義値として登録する。

1. `c : ℕ` を受け取る。
2. `5 ^ 5 : ℕ` を作る。
3. `c ^ 8 : ℕ` を作る。
4. それらを乗算し、`ℕ` 値として返す。

数学的には

$$
c
\longmapsto
5^5c^8
$$

という写像である。

## Lean 固有の処理

本体では coercion は発生しない。入力・出力ともに `ℕ` だからである。

一方、後続 theorem `factor_product` では `A` と `B` が `ℤ` 値なので、

```lean
(zeroSectorQ p.c : ℤ)
```

という coercion が必要になる。そこで定義展開後に `push_cast` を使い、自然数の積・冪を整数へ押し上げて `ring` が処理できる多項式形へする。

この意味で、本宣言そのものは型変換を含まないが、**後続で `ℕ` 側の fifth-power mass を `ℤ` 側の inversion factors に接続することを前提にした定義** である。

## 冗長・重複箇所

宣言本体に冗長性はほとんどない。

```lean
5 ^ 5 * c ^ 8
```

を何度も直接書く代わりに `zeroSectorQ` と名前を付けることで、後続の `factor_product`、`A0_mul_B0`、`coprime_Q_d`、factor split 系で同じ量を共有できる。

むしろこの `def` は重複削減のための抽象化である。

ただし名前 `zeroSectorQ` だけから指数 `5` と `8` の由来は読み取れない。docstring の

```text
The fifth-power mass `Q = 5^5*c^8` in `A*B = 4*Q^5`.
```

が実質的に重要な仕様説明になっている。

## 最適化候補

### 1. 定義自体

現状のままで十分に最小である。`simp` 用 lemma を追加する必要も通常はない。`rfl` で展開可能だからである。

### 2. 後続証明用 API

後続で coercion 展開が頻出するなら、例えば

```lean
lemma zeroSectorQ_cast (c : ℕ) :
    (zeroSectorQ c : ℤ) = 5 ^ 5 * (c : ℤ) ^ 8 := by
  simp [zeroSectorQ]
```

のような補題を置く余地はある。

ただし現行正本では `unfold zeroSectorQ; push_cast; ring` で十分に処理できており、専用 lemma が本当に重複削減になるかは後続使用回数を見て判断すべきである。

### 3. 数学的名前

`Q` は短く downstream algebra には便利だが、単独では意味が弱い。theorem museum の解説上は「fifth-power mass」と補うのが妥当である。source docstring もこの表現を採用している。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本宣言単体で必要なのは自然数の乗算と冪という極めて基本的な機能だけなので、`import Mathlib` は明らかに広い。

ただしこの theorem museum 作業では Lean build を行わない指示であり、`zeroSectorQ` を含む元 module `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` の **実際の最小 import 集合は検証していない**。したがって具体的な import 削減先は断定しない。

## Comparator challenge 化の可否

**単独では challenge 化の価値は低い。**

理由は `def` そのものが

```lean
5 ^ 5 * c ^ 8
```

という一行の略記だからである。

ただし次のような downstream identity を challenge にするなら有意義である。

```lean
4 * (zeroSectorQ c : ℤ) ^ 5 = ...
```

特に `factor_product` 内の `zeroSectorQ` 展開部分は、自然数から整数への cast、冪、環正規化をまとめた小さな Comparator challenge として切り出せる。

判定は **定義単独: 不向き / 後続の fifth-power identity と組み合わせるなら適する** である。

## PDF との対応

対象 branch には日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在することを確認した。

ただし GitHub コネクタの通常のテキスト取得では PDF binary 本文を解析可能な形で取得できないため、本宣言と PDF の具体的ページ・節番号の対応は **未確認** である。ここでは Lean 正本のコードと repository 上で確認できる生成構造を根拠とし、PDF 内の位置については推測しない。

## 次に読むべき宣言

次は 0288 `sixteen_mul_goldenFifthSndFactor_eq` である。種別は **`theorem`**。

正本では `zeroSectorQ` の直後に現れる。

```lean
theorem sixteen_mul_goldenFifthSndFactor_eq (r s : ℤ) :
    16 * goldenFifthSndFactor r s =
      zeroSectorU r s ^ 2 - 80 * s ^ 4 := by
  unfold goldenFifthSndFactor zeroSectorU zeroSectorX
  ring
```

これはこれまで導入した座標 `X,U` を、元の quartic factor `goldenFifthSndFactor` に初めて戻して結び付ける exact diagonalization identity である。

したがって依存順では、0282–0287 の「座標・質量の定義列」を終え、0288 からそれらが実際に成立させる代数恒等式の証明段階へ移る。