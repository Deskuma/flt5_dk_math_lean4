# 0285 — `zeroSectorA`

## 宣言種別

これは **`def`** である。

theorem ではなく、zero-sector inversion で用いる下側の因子 `A` を定義する宣言である。直前までに導入した

$$
U=X^2+5s^2,
\qquad
W=4d^5
$$

を組み合わせて、

$$
A=U-W
$$

を名前付きの整数量として固定する。

## Lean の型

```lean
/-- The lower inversion factor `A = U-W`. -/
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d
```

Lean 上の完全な型は

```lean
zeroSectorA : ℤ → ℤ → ℕ → ℤ
```

である。

`r,s` は整数、`d` は自然数であり、結果は整数である。`d : ℕ` から `ℤ` への cast は本定義では直接書かれず、直接依存する 0284 `zeroSectorW` の内部で処理される。

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

を代入すると、`zeroSectorA` は

$$
A=U-W
$$

すなわち

$$
A=(2r+s)^2+5s^2-4d^5
$$

である。

ここで `U` を中心、`W` を中心からの偏差と見ると、`A` はその **下側の対称因子** である。直後の 0286 `zeroSectorB` は

$$
B=U+W
$$

を定義するため、二つを合わせると

$$
A=U-W,
\qquad
B=U+W
$$

という対称な factor pair が得られる。

この対称化により、後続では差の平方公式

$$
AB=(U-W)(U+W)=U^2-W^2
$$

を使って zero-sector の quartic / fifth-power 情報を積の形へ変換できる。

## 証明全体での役割

`zeroSectorA` は inversion 座標系の最初の実際の因子である。

正本の後続コードでは、0286 `zeroSectorB` と組にしてまず

$$
AB=20s^4
$$

を証明し、さらに zero-sector の tenth-power split を使って

$$
AB=4Q^5
$$

へ変換している。

また source では次の二つの exact relation も証明される。

$$
B-A=8d^5,
$$

$$
A+B=2U.
$$

したがって `A` は単なる式の略記ではない。後段では `A>0` が示され、

```lean
def A0 (p : GoldenZeroSectorCandidate) : ℕ :=
  (zeroSectorA p.r p.s p.d).natAbs
```

として自然数因子 `A0` へ移される。その後の fifth-power factorization / inversion packet ではこの自然数化された下側因子が構造データとして使われる。

この意味で 0285 は、**中心量と fifth-power 偏差量を、積分解に使える具体的な下側因子へ変換する境界** である。

## 直接依存する定義・補題

### 0283 `zeroSectorU`

```lean
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

本定義の左側、すなわち中心量

$$
U=X^2+5s^2
$$

を供給する。

### 0284 `zeroSectorW`

```lean
def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

本定義で差し引く偏差量

$$
W=4d^5
$$

を供給する。

### 0282 `zeroSectorX`

`zeroSectorA` 本体からは直接参照されない。`zeroSectorU` の内部を通じた **推移的依存** である。

### theorem 依存

本宣言は `def` なので証明補題を直接利用しない。0281 の tenth-power split は `d` の数学的由来を与えるが、Lean の定義本体には現れない。

## 定義・構築の流れ

### 1. `r,s,d` を受け取る

```lean
(r s : ℤ) (d : ℕ)
```

zero-sector candidate の整数座標 `r,s` と tenth-power root 側の自然数 `d` を入力する。

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

### 4. 整数上で差を取る

```lean
zeroSectorU r s - zeroSectorW d
```

として

$$
A=U-W
$$

を定義する。

この時点では `A` の正値性は定義そのものには含まれない。正本では後で `GoldenZeroSectorCandidate` の仮定を使って `A_pos` を証明する。したがって任意の `r,s,d` に対して `A>0` と読むのは誤りである。

## Lean 固有の処理

この宣言には tactic proof はなく、右辺がそのまま definitional equation である。そのため

```lean
example (r s : ℤ) (d : ℕ) :
    zeroSectorA r s d = zeroSectorU r s - zeroSectorW d := by
  rfl
```

は `rfl` で成立する。

一方、完全展開した

$$
A=(2r+s)^2+5s^2-4d^5
$$

まで進める場合は、

```lean
unfold zeroSectorA zeroSectorU zeroSectorX zeroSectorW
```

あるいは

```lean
simp only [zeroSectorA, zeroSectorU, zeroSectorX, zeroSectorW]
```

のように複数の定義を明示的に展開する必要がある。

`zeroSectorA` 自体では `d` の cast を書かないため、型の境界が一段隠蔽されている。これは API としては有利で、呼び出し側は `d : ℕ` をそのまま渡せばよい。

正本の `factor_product_twenty` では

```lean
unfold zeroSectorA zeroSectorB
ring
```

により

$$
AB=U^2-W^2
$$

へ正規化している。このように、定義名を残した構造表示と `ring` 向けの多項式展開を必要箇所で切り替える設計になっている。

## 冗長・重複箇所

定義本体は一行であり、局所的な冗長性はない。

理論上は後続の式へ

```lean
zeroSectorU r s - zeroSectorW d
```

を直接書けば `zeroSectorA` は省略できる。しかし正本では `A` が

- `factor_product_twenty`
- `factor_product`
- `factor_difference`
- `factor_sum`
- `A_pos`
- `A_lt_B`
- `A0`
- `A0_cast`

など多数の後続宣言に現れる。

したがって名前付き定義にする価値は高く、単純な inline 化は可読性と構造把握を悪化させる。

また `A` と `B` は完全な対称ペアなので、片方だけを特殊扱いする重複整理は適切ではない。二つの一行定義を並列に保つ現在の形は、数学的構造をコード上にも直接表現している。

## 最適化候補

### 対称恒等式 API の維持

`A,B` の定義展開を各所で繰り返すより、正本にすでに存在する

$$
B-A=8d^5,
\qquad
A+B=2U
$$

のような named theorem を downstream API として使う方が、実装詳細への依存を減らせる。

この方針は現在の source と整合しており、追加最適化というより **既存 API を優先利用すること** が有効である。

### `A=U-W` の simp lemma

定義そのものは unfolding 可能なので、別途

```lean
@[simp] theorem zeroSectorA_eq ...
```

を追加する必要性は低い。むしろ `[simp]` による自動展開を強くすると、factor pair としての `A` という抽象名が早期に消えて式が巨大化する可能性がある。

したがって現時点では専用 simp lemma を追加しない現在の設計が妥当と考えられる。

### factor pair の structure 化

`U,W,A,B` を一つの structure に束ねれば引数 `r,s,d` の反復を減らせる可能性はある。しかし source では後に `GoldenZeroSectorCandidate` や inversion packet が構造化を担当しており、この初期定義段階でさらに structure を増やす利益は未確認である。

よってこれは設計候補に留まり、現行コードを変更すべき根拠までは確認できない。

## 必要 Mathlib import と import 最適化候補

repository の standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

`zeroSectorA` 単体が新たに必要とする演算は、既存の `zeroSectorU : ℤ` と `zeroSectorW : ℤ` の整数減算だけである。したがって本定義そのものが Mathlib 全体を要求するわけではない。

ただし本実行では Lean build を行わない条件であり、generated source を独立 module として再ビルドして最小 import を検証してはいない。そのため、具体的な最小 import 集合は **未確認** とする。

import 最適化を行うなら、`SignedGoldenZeroSectorInversion` の依存グラフ全体を対象に `Mathlib` umbrella import をより狭い整数・自然数・多項式算術関連 import へ置き換え、Lean build で検証するのが適切である。ただし今回はその検証を実施していない。

## Comparator challenge 化の可否

### 判定: 定義単体では低適性、`A/B` 恒等式との組では高適性

定義単独の

```lean
zeroSectorA r s d = zeroSectorU r s - zeroSectorW d
```

は `rfl` で終わるため、Comparator challenge としてはほとんど差が出ない。

しかし 0286 `zeroSectorB` と組み合わせて

$$
AB=U^2-W^2,
$$

$$
B-A=8d^5,
$$

$$
A+B=2U
$$

を証明する課題にすると、`unfold`、`simp only`、`ring` の使い分けや、抽象定義をどの段階まで保持するかを比較できる。

特に `factor_product_twenty` の最初の変形

$$
AB=U^2-W^2
$$

は短く独立性が高く、Comparator challenge に向く。

## PDF との照合

対象 branch の repository tree には既存の

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

しかし今回、GitHub の通常の UTF-8 file 取得経路では PDF binary の取得が拒否され、本文を解析可能な形で取得できなかった。そのため PDF 内で `A=U-W` が現れる具体的なページ番号・節番号・文言は確認できていない。

よって PDF との具体的対応は推測せず、Lean 正本 `Flt5DkMath/FLT5StandAlone.lean` と repository 上で確認できる既存 theorem museum を根拠としている。

## 次に読むべき宣言

次は **0286 `zeroSectorB`** である。種別は `def`。

```lean
/-- The upper inversion factor `B = U+W`. -/
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

すなわち

$$
B=U+W
$$

を導入する。

0285 の

$$
A=U-W
$$

と対になり、ここで inversion factor pair

$$
(A,B)=(U-W,U+W)
$$

が完成する。