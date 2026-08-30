# 0286 — `zeroSectorB`

## 宣言種別

これは **`def`** である。

theorem ではなく、zero-sector inversion で用いる上側の因子 `B` を定義する宣言である。直前の 0285 `zeroSectorA` が

$$
A=U-W
$$

を定義したのに対し、本宣言は

$$
B=U+W
$$

を定義する。

これにより

$$
A=U-W,
\qquad
B=U+W
$$

という対称な inversion factor pair が完成する。

## Lean の型

```lean
/-- The upper inversion factor `B = U+W`. -/
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

Lean 上の完全な型は

```lean
zeroSectorB : ℤ → ℤ → ℕ → ℤ
```

である。

`r,s` は整数、`d` は自然数、結果は整数である。`d : ℕ` から `ℤ` への cast は直接この定義には現れず、0284 `zeroSectorW` の内部で処理される。

## 数学的意味

0282–0284 の定義

$$
X=2r+s,
$$

$$
U=X^2+5s^2,
$$

$$
W=4d^5
$$

を代入すると、`zeroSectorB` は

$$
B=U+W
$$

すなわち

$$
B=(2r+s)^2+5s^2+4d^5
$$

である。

0285 `zeroSectorA` と合わせると

$$
A=U-W,
\qquad
B=U+W
$$

となり、中心 `U` のまわりに偏差 `W` を対称に配置した二因子が得られる。

この形の主要な利点は、差の平方公式と和差公式がそのまま使えることである。

$$
AB=(U-W)(U+W)=U^2-W^2,
$$

$$
B-A=2W=8d^5,
$$

$$
A+B=2U.
$$

したがって `B` は単なる式の略記ではなく、zero-sector の二次量 `U` と fifth-power 偏差 `W` を factorization に適した対称座標へ変換する上側因子である。

## 証明全体での役割

`zeroSectorB` は 0285 `zeroSectorA` と対になって inversion factor pair を完成させる。

Lean 正本では、この二つを用いて直後の theorem `factor_product_twenty` が

$$
AB=20s^4
$$

を証明する。証明の最初の段階では定義を展開して

$$
AB=U^2-W^2
$$

へ落とし、そこから zero-sector candidate が持つ対角恒等式を用いて右辺を $20s^4$ に正規化する。

続く `factor_product` では、0281 の tenth-power split に由来する `s` の表示を使って

$$
AB=4Q^5
$$

へ変換する。ここで `Q=5^5c^8` が導入される。

さらに正本では `B` に対して正値性が証明され、後に

```lean
def B0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorB p.r p.s p.d).natAbs
```

のように自然数因子へ移される。この自然数化された上側因子は、後続の fifth-power factorization / inversion packet で構造データとして利用される。

つまり 0286 は、**0285 で始まった対称 factor pair を完成させ、積・差・和の三つの exact relation を利用可能にする境界** である。

## 直接依存する定義・補題

### 0283 `zeroSectorU`

```lean
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

本定義の中心量

$$
U=X^2+5s^2
$$

を供給する。

### 0284 `zeroSectorW`

```lean
def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

本定義で加える偏差量

$$
W=4d^5
$$

を供給する。

### 0282 `zeroSectorX`

`zeroSectorB` 本体からは直接参照されない。`zeroSectorU` の内部を通じた **推移的依存** である。

### 0285 `zeroSectorA`

Lean の定義本体の直接依存ではない。しかし数学的役割は `A` と `B` の対称ペアにあるため、証明全体の依存関係としては強く結びついている。

### theorem 依存

本宣言は `def` なので theorem を直接利用しない。`d` の数学的由来は 0281 `zeroSector_tenthPower_split` にあるが、その情報はこの定義の型や本体には埋め込まれていない。

## 定義・構築の流れ

### 1. `r,s,d` を受け取る

```lean
(r s : ℤ) (d : ℕ)
```

zero-sector candidate の整数座標 `r,s` と、tenth-power root 側から得られた自然数 `d` を入力する。

### 2. 中心量 `U` を計算する

```lean
zeroSectorU r s
```

これは

$$
(2r+s)^2+5s^2
$$

である。

### 3. 偏差量 `W` を計算する

```lean
zeroSectorW d
```

これは整数として

$$
4d^5
$$

である。

### 4. 整数上で和を取る

```lean
zeroSectorU r s + zeroSectorW d
```

として

$$
B=U+W
$$

を定義する。

`U` は平方と $5s^2$ の和、`W` は $4d^5$ であるため、zero-sector candidate の後続仮定の下では `B` は正になる。しかし、その正値性はこの定義自体には含まれず、後続 theorem で証明される。

## Lean 固有の処理

この宣言には tactic proof は存在せず、右辺そのものが definitional equation である。

したがって

```lean
example (r s : ℤ) (d : ℕ) :
    zeroSectorB r s d = zeroSectorU r s + zeroSectorW d := by
  rfl
```

は `rfl` で成立する。

完全展開して

$$
B=(2r+s)^2+5s^2+4d^5
$$

まで進める場合は、

```lean
unfold zeroSectorB zeroSectorU zeroSectorX zeroSectorW
```

または

```lean
simp only [zeroSectorB, zeroSectorU, zeroSectorX, zeroSectorW]
```

のように複数定義を展開する必要がある。

正本の `factor_product_twenty` では `zeroSectorA` と `zeroSectorB` を展開し、`ring` によって

$$
(U-W)(U+W)=U^2-W^2
$$

を機械的に正規化する。この使い方は、定義名を保持して構造を読みやすくする層と、多項式恒等式として自動正規化する層を分けている。

## 冗長・重複箇所

定義本体は一行であり、局所的な冗長性はない。

理論上は後続 theorem に

```lean
zeroSectorU r s + zeroSectorW d
```

を直接書けば `zeroSectorB` 自体は省略できる。しかし正本では `B` は

- `factor_product_twenty`
- `factor_product`
- factor difference / factor sum 関係
- `B_pos`
- `A_lt_B`
- `B0`
- `B0_cast`

など複数の後続宣言で継続的に使われる。

また `A=U-W` と `B=U+W` の対称性そのものが証明の構造なので、二つを inline 化するより独立した名前付き定義として並べる現在の設計の方が読みやすい。

## 最適化候補

### 対称 factor pair API の優先利用

後続で毎回 `zeroSectorA` / `zeroSectorB` を展開するより、正本に存在する積・差・和の named theorem を使う方が実装詳細への依存を減らせる。

特に

$$
AB=4Q^5,
$$

$$
B-A=8d^5,
$$

$$
A+B=2U
$$

のような API を downstream で維持するのがよい。

### `@[simp]` の追加は慎重に

`zeroSectorB` は `rfl` で展開可能なので、専用の simp theorem を新設する必要性は低い。

自動展開を強くすると `B` という抽象名が早期に消え、式が大きくなって factor pair の対称性が見えにくくなる可能性がある。したがって現時点では必要箇所だけ `unfold` / `simp only` する現在の設計が妥当である。

### `A,B` の structure 化

`U,W,A,B` を一つの structure にまとめる設計は可能であり、引数の反復を減らせる。しかし正本では後段の `GoldenZeroSectorCandidate` や inversion packet が構造化を担うため、この段階で別 structure を追加する利得は未確認である。

よってこれは最適化候補に留まり、現行コードを変更すべき根拠は確認できない。

## 必要 Mathlib import と import 最適化候補

repository の standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

`zeroSectorB` 単体が新たに必要とする演算は、既存の `zeroSectorU : ℤ` と `zeroSectorW : ℤ` の整数加算だけである。この定義そのものが Mathlib 全体を本質的に必要とするわけではない。

ただし今回は Lean build を行わない条件であり、generated source を独立 module として再ビルドして最小 import を検証していない。したがって具体的な最小 import 集合は **未確認** とする。

import 最適化を行うなら `SignedGoldenZeroSectorInversion` 全体の依存グラフを対象に、umbrella `Mathlib` を整数・自然数・代数正規化等のより狭い import に置き換え、Lean build で検証する必要がある。

## Comparator challenge 化の可否

### 判定: 定義単体では低適性、0285 と組み合わせれば高適性

定義単体の

```lean
zeroSectorB r s d = zeroSectorU r s + zeroSectorW d
```

は `rfl` で終わるため、Comparator challenge としてはほぼ差が出ない。

しかし 0285 `zeroSectorA` と組にして

$$
AB=U^2-W^2,
$$

$$
B-A=8d^5,
$$

$$
A+B=2U
$$

を証明する課題にすれば、`unfold`、`simp only`、`ring` の選択や、どの抽象定義を保持するかを比較できる。

特に `factor_product_twenty` の最初の代数変形は、短く局所的であり Comparator challenge に適する。

## PDF との照合

対象 branch では既存の

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

の存在を確認した。

日本語 PDF は repository 上のファイル存在と blob SHA を確認できた。英語 PDF も対象 path の取得を試みたが、GitHub コネクタの UTF-8 取得では binary decode error となり、本文を解析可能な形では取得できなかった。

そのため PDF 内で `B=U+W` が現れる具体的ページ番号・節番号・文言は **未確認** であり、推測しない。

本解説の技術的内容は Lean 正本 `Flt5DkMath/FLT5StandAlone.lean` と repository 上の既存 theorem museum を根拠としている。

## 次に読むべき宣言

次は **0287 `zeroSectorQ`** である。種別は `def`。

```lean
/-- The fifth-power mass `Q = 5^5*c^8` in `A*B = 4*Q^5`. -/
def zeroSectorQ (c : ℕ) : ℕ :=
  5 ^ 5 * c ^ 8
```

ここで inversion factor pair の積を

$$
AB=4Q^5
$$

と書くための fifth-power mass

$$
Q=5^5c^8
$$

が導入される。

0285–0286 で `A,B` が完成し、0287 からその積の fifth-power 側を名前付き量として整理する段階へ進む。
