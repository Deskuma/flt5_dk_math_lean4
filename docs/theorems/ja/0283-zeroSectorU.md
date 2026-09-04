# 0283 — `zeroSectorU`

## 宣言種別

これは **`def`** である。

theorem ではなく、zero-sector inversion で用いる二次量 `U` を導入する定義である。直前の 0282 `zeroSectorX` が定めた

$$
X=2r+s
$$

を使い、

$$
U=X^2+5s^2
$$

を名前付きの整数量として固定する。

## Lean の型

```lean
/-- The positive quadratic quantity `U = X^2+5*s^2`. -/
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

したがって Lean 上の完全な型は

```lean
zeroSectorU : ℤ → ℤ → ℤ
```

である。

## 数学的意味

入力を `r,s : ℤ` とし、0282 の

$$
X=2r+s
$$

を代入すると、

$$
\operatorname{zeroSectorU}(r,s)
=(2r+s)^2+5s^2.
$$

展開すれば

$$
U=4r^2+4rs+6s^2
=2(2r^2+2rs+3s^2).
$$

したがって `U` は `r,s` の二次形式である。

source の docstring は `The positive quadratic quantity` と呼んでいるが、**この `def` 単独から常に $U>0$ が成り立つわけではない**。実際、`r=s=0` なら $U=0$ である。一方、

$$
U=X^2+5s^2
$$

なので整数 `r,s` に対して常に

$$
U\ge 0
$$

であり、`U=0` なら `X=0` かつ `s=0`、したがって `r=0` である。つまり数学的には正定値二次形式に対応し、非零入力に制限すれば正になる。

ただし、この宣言自身には非零仮定も positivity theorem も含まれていないため、「正」という語は後続 candidate の条件を見越した説明と読むのが正確である。

## 証明全体での役割

0281 `SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split` までで zero-sector arithmetic は

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}
$$

という tenth-power split を得た。

0282 から始まる `SignedGoldenZeroSectorInversion` 層では、この因数分解情報を inversion 用の座標へ組み替える。source 冒頭の設計は

$$
X=2r+s,
\qquad
U=X^2+5s^2,
\qquad
W=4d^5,
$$

さらに

$$
A=U-W,
\qquad
B=U+W
$$

と進む。

そのため 0283 `zeroSectorU` は、0282 の一次座標 `X` を **平方二次量へ持ち上げる段階** である。

後続の `zeroSectorA` と `zeroSectorB` は `U` を共通中心として

$$
A=U-W,
\qquad
B=U+W
$$

を作る。したがって `U` は inversion factor pair `(A,B)` の中点に相当する代数量であり、`W` がそこからの対称な偏差になる。

さらに generated source の章コメントでは、対角化された quartic identity と tenth-power split から

$$
AB=4Q^5
$$

を得ることが inversion 層の目的として明示されている。`zeroSectorU` はその factorization の中心式を構成するための基本定義である。

## 直接依存する定義・補題

### 0282 `zeroSectorX`

唯一の DkMath 独自の直接依存は

```lean
zeroSectorX r s
```

である。

0282 の定義

```lean
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s
```

を使って本定義は

```lean
zeroSectorX r s ^ 2 + 5 * s ^ 2
```

と書かれる。

### 整数の平方・加法・乗法

`r,s : ℤ` に対する

```lean
^ 2
```

整数定数 `5`、乗法、加法だけを使用する。

### 0281 との関係

コード上では 0281 を直接参照しない。しかし証明設計上は、0281 で得た `d` が次の 0284 `zeroSectorW` に入り、0283 の `U` と組になって `A,B` を構成する。したがって 0281 は inversion layer へデータを供給する前段であり、0283 はそのデータを受ける座標系側の定義である。

## 定義・構築の流れ

### 1. `r,s` を符号付き整数座標として受け取る

```lean
(r s : ℤ)
```

inversion では `s` の符号を保持するため、自然数絶対値ではなく整数座標へ戻っている。

### 2. 0282 の対角座標を評価する

```lean
zeroSectorX r s
```

すなわち

$$
X=2r+s.
$$

### 3. `X` を平方する

```lean
zeroSectorX r s ^ 2
```

符号に依存しない非負の二次量になる。

### 4. `5s²` を加える

```lean
+ 5 * s ^ 2
```

結果として

$$
U=X^2+5s^2
$$

を得る。

### 5. 後続の対称因子へ渡す

正本では直後に

```lean
def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5


def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d


def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

と続く。

ここで `U` は `A` と `B` に共通する中心項として再利用される。

## Lean 固有の処理

この宣言には proof term は存在せず、右辺がそのまま定義内容である。

したがって

```lean
zeroSectorU r s
```

は定義展開すると

```lean
zeroSectorX r s ^ 2 + 5 * s ^ 2
```

になり、さらに `zeroSectorX` まで展開すれば

```lean
(2 * r + s) ^ 2 + 5 * s ^ 2
```

になる。

よって例えば

```lean
example (r s : ℤ) :
    zeroSectorU r s = zeroSectorX r s ^ 2 + 5 * s ^ 2 := by
  rfl
```

は定義的等価性だけで成立する。

展開形

```lean
zeroSectorU r s = 4 * r ^ 2 + 4 * r * s + 6 * s ^ 2
```

を示す場合は `simp [zeroSectorU, zeroSectorX]` と `ring` / `ring_nf` の組合せが自然な候補になるが、これは本宣言そのものには含まれていない。

## 冗長・重複箇所

定義本体は一行であり、実質的な冗長性は無い。

理論上は後続の `zeroSectorA`、`zeroSectorB` に

```lean
zeroSectorX r s ^ 2 + 5 * s ^ 2
```

を直接埋め込み、`zeroSectorU` を削除できる。しかしそうすると

$$
A=U-W,
\qquad
B=U+W
$$

という inversion の対称構造がコード上で見えにくくなる。

したがって `zeroSectorU` の独立定義は重複削減よりも **構造の命名と再利用** に価値があり、現設計は妥当である。

## 最適化候補

### 専用展開 lemma

後続で展開形を頻繁に使うなら、例えば

```lean
theorem zeroSectorU_expanded (r s : ℤ) :
    zeroSectorU r s = 4 * r ^ 2 + 4 * r * s + 6 * s ^ 2 := by
  simp [zeroSectorU, zeroSectorX]
  ring
```

のような lemma を用意する余地はある。

ただし、現時点で使用回数を全面的に監査しておらず、`ring` で容易に再生成できる恒等式でもあるため、API 追加が本当に有利かは未確認である。

### positivity lemma

source docstring が `positive quadratic quantity` と呼んでいるため、意味を API として明示したいなら

```lean
theorem zeroSectorU_nonneg (r s : ℤ) : 0 ≤ zeroSectorU r s := ...
```

や

```lean
theorem zeroSectorU_pos_of_ne_zero
    (r s : ℤ) (h : r ≠ 0 ∨ s ≠ 0) : 0 < zeroSectorU r s := ...
```

のような補題は自然である。

特に前者は平方の非負性から直接示せる。しかし後続証明がこれらを必要としているかは本稿の対象宣言だけでは確定しないので、最適化候補に留める。

### `abbrev` 化

0282 と同様に透明な略記として `abbrev` を使うことも理論上可能だが、`U` を rewrite/unfold の明確な境界として保持する現行 `def` に十分な理由がある。変更を推奨する根拠はない。

## 必要 Mathlib import と import 最適化候補

repository の standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用しており、manifest 上では本宣言は

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

に属する。

`zeroSectorU` 自体が必要とする機能は `ℤ`、加法、乗法、自然数冪と 0282 `zeroSectorX` だけであり、宣言単独のために Mathlib 全体が必要とは考えにくい。

ただし、この repository には standalone へ結合される前の元 source module が個別ファイルとして格納されていないため、元 module の実際の import 列は確認できなかった。また本実行では Lean build を行わない条件なので、最小 import 集合を実証していない。

したがって確認済み事項は **standalone では `import Mathlib`** までであり、具体的な最小化先を断定しない。

## Comparator challenge 化の可否

### 判定: 単体では低適性

`zeroSectorU` は theorem ではなく一行の定義なので、定義そのものを Comparator challenge にしても

```lean
zeroSectorU r s = zeroSectorX r s ^ 2 + 5 * s ^ 2
```

を `rfl` で閉じるだけになり、証明比較としての情報量が少ない。

一方、派生問題として

$$
U=4r^2+4rs+6s^2
$$

の展開、あるいは

$$
U\ge0,
\qquad
U=0\iff r=0\land s=0
$$

を示す課題にすれば、`ring`、`positivity`、整数上の平方零判定など複数の証明戦略を比較できる。

したがって **定義そのものは challenge 不向き、派生二次形式 theorem は challenge 化可能** と評価する。

## PDF との照合

対象 branch には既存の

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを repository tree で確認した。

ただし今回利用可能な GitHub コネクタは binary PDF 本文を UTF-8 テキストとして返せず、raw PDF の取得経路も成功しなかった。そのため PDF 内の `U=X^2+5s^2` の具体的なページ番号・節番号・文言は確認できていない。

よって本稿では PDF の具体的記述を推測で補わず、Lean 正本と repository 内の既存 theorem museum 文書から確認できる技術的意味だけを記述した。

## 次に読むべき宣言

次は **0284 `zeroSectorW`** である。種別は `def`。

```lean
/-- The quantity `W = 4*d^5` supplied by `|H(r,s)| = d^10`. -/
def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

すなわち

$$
W=4d^5.
$$

0283 の `U` が `r,s` 側から作られる二次中心量であるのに対し、0284 の `W` は 0281 の tenth-power split

$$
|H(r,s)|=d^{10}
$$

から得られた `d` を fifth-power scale として inversion 座標へ持ち込む。

この二つが揃うと、続く

$$
A=U-W,
\qquad
B=U+W
$$

という対称 factor pair を定義できる。したがって依存順は

$$
\texttt{zeroSectorX}
\to
\texttt{zeroSectorU}
\to
\texttt{zeroSectorW}
\to
(\texttt{zeroSectorA},\texttt{zeroSectorB})
$$

と読むのが自然である。