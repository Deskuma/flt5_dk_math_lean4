# 0284 — `zeroSectorW`

## 宣言種別

これは **`def`** である。

theorem ではなく、zero-sector inversion で用いる fifth-power 尺度 `W` を導入する定義である。直前の 0283 `zeroSectorU` が

$$
U=X^2+5s^2
$$

という `r,s` 側の二次量を導入したのに対し、本宣言は 0281 `SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split` で得られる

$$
|H(r,s)|=d^{10}
$$

の自然数 `d` から

$$
W=4d^5
$$

を整数として作る。

## Lean の型

```lean
/-- The quantity `W = 4*d^5` supplied by `|H(r,s)| = d^10`. -/
def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

したがって Lean 上の完全な型は

```lean
zeroSectorW : ℕ → ℤ
```

である。

入力は自然数 `d : ℕ`、出力は整数 `ℤ` である。`d` は定義本体で明示的に `(d : ℤ)` へ cast される。

## 数学的意味

定義そのものは

$$
W=4d^5
$$

である。

ここで `d` は任意の自然数として受け取られるが、zero-sector inversion の文脈では 0281 の tenth-power split

$$
|H(r,s)|=d^{10}
$$

から供給される値である。

したがって

$$
d^{10}=(d^5)^2
$$

と平方に分解したとき、その平方根側の fifth power `d^5` を取り出し、さらに係数 `4` を付けて

$$
W=4d^5
$$

とする。

この `4` は後続の対称因子

$$
A=U-W,
\qquad
B=U+W
$$

を作るための正規化係数である。generated source の章コメントでは、この座標系から

$$
AB=4Q^5
$$

および

$$
B=A+8d^5
$$

を得る設計が明示されている。後者は本定義から直ちに

$$
B-A=2W=8d^5
$$

となることに対応する。

## 証明全体での役割

0281 までの arithmetic layer は

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}
$$

という tenth-power split を得る。

0282–0284 では、そのデータを inversion 用の座標へ変換する。

$$
X=2r+s,
\qquad
U=X^2+5s^2,
\qquad
W=4d^5.
$$

ここで `U` は `r,s` から作る中心量、`W` は tenth-power factor `d` から作る偏差量である。次の 0285 `zeroSectorA` と 0286 `zeroSectorB` は

$$
A=U-W,
\qquad
B=U+W
$$

と定義されるので、`W` は factor pair `(A,B)` の中心 `U` からの対称なずれを表す。

この意味で 0284 は、**算術層の tenth-power 情報を inversion 層の線形な差分座標へ移す橋** である。

## 直接依存する定義・補題

### 自然数から整数への cast

本定義で使われる唯一の型変換は

```lean
(d : ℤ)
```

である。

### 整数の fifth power

```lean
(d : ℤ) ^ 5
```

を使う。指数 `5` は自然数指数である。

### 整数定数 `4` と乗法

```lean
4 * (d : ℤ) ^ 5
```

として `W` を構成する。

### 0281 との関係

コード上では 0281 の theorem 名を直接参照しない。しかし source docstring 自身が

```text
supplied by `|H(r,s)| = d^10`
```

と明記しており、設計上の入力源は 0281 の `d` である。

### 0283 との関係

`zeroSectorW` 本体は 0283 `zeroSectorU` を直接参照しない。両者は次の `zeroSectorA` / `zeroSectorB` で初めて組み合わされる並列の基礎定義である。

## 定義・構築の流れ

### 1. `d : ℕ` を受け取る

```lean
(d : ℕ)
```

zero-sector arithmetic で得た tenth-power root を自然数のまま保持する。

### 2. `d` を整数へ cast する

```lean
(d : ℤ)
```

後続の `U`, `A`, `B` が整数値なので、ここで型を `ℤ` に揃える。

### 3. fifth power を取る

```lean
(d : ℤ) ^ 5
```

0281 の `d^10` を平方として扱うための half-exponent に相当する。

### 4. `4` 倍する

```lean
4 * (d : ℤ) ^ 5
```

これを `W` と命名する。

### 5. 後続の対称因子へ渡す

正本では直後に

```lean
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d

/-- The upper inversion factor `B = U+W`. -/
def zeroSectorB (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s + zeroSectorW d
```

と続く。

## Lean 固有の処理

この宣言には proof term はなく、右辺がそのまま定義である。

したがって

```lean
example (d : ℕ) :
    zeroSectorW d = 4 * (d : ℤ) ^ 5 := by
  rfl
```

は定義的等価性だけで成立する。

また `d : ℕ` から `ℤ` への coercion が自動的に式へ入るため、後続で `zeroSectorU r s : ℤ` と加減算できる。

一方、自然数側の式

```lean
4 * d ^ 5
```

と直接比較するには cast lemma や `norm_cast` / `exact_mod_cast` が必要になる場合がある。本宣言自体ではその処理は発生しない。

## 冗長・重複箇所

定義本体は一行であり、計算上の冗長性はない。

理論上は `zeroSectorA` と `zeroSectorB` の中へ

```lean
4 * (d : ℤ) ^ 5
```

を直接埋め込める。しかしそうすると

$$
A=U-W,
\qquad
B=U+W
$$

という対称構造が見えにくくなり、さらに

$$
B-A=2W=8d^5
$$

という後続関係の説明性も下がる。

したがって独立した `zeroSectorW` は、式の短縮よりも **inversion の偏差量を名前付きで固定すること** に価値がある。

## 最適化候補

### 非負性補題

`d : ℕ` なので

$$
W=4d^5\ge0
$$

は自明であり、後続で positivity を繰り返すなら

```lean
theorem zeroSectorW_nonneg (d : ℕ) : 0 ≤ zeroSectorW d := by
  simp [zeroSectorW]
  positivity
```

のような補題を置く余地がある。

ただし後続で実際に何度必要になるかを全面監査していないため、現時点では候補に留める。

### 正値性補題

`0 < d` が与えられる文脈では

```lean
theorem zeroSectorW_pos {d : ℕ} (hd : 0 < d) : 0 < zeroSectorW d := ...
```

も自然である。candidate 側には後に `d` の由来を含む positivity 情報が存在するため、利用価値はあり得る。

### `2 * W = 8*d^5` の専用補題

`A,B` の差を頻繁に扱うなら

```lean
theorem two_mul_zeroSectorW (d : ℕ) :
    2 * zeroSectorW d = 8 * (d : ℤ) ^ 5 := by
  simp [zeroSectorW]
  ring
```

のような正規化 lemma も考えられる。ただし `ring` で容易に再生成できるため、API として追加する必要性は未確認である。

## 必要 Mathlib import と import 最適化候補

repository の standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用している。generated source の境界コメントから、本宣言は

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

に属することを確認できる。

`zeroSectorW` 単体が必要とするのは `ℕ`、`ℤ`、自然数から整数への cast、整数乗法、自然数指数の冪だけであり、宣言単独のために Mathlib 全体が必要とは考えにくい。

ただし repository には generated source を個別 module として直接取得できる配置が確認できず、本実行では Lean build を行わない条件なので、最小 import 集合は実証していない。

したがって確認済み事項は **standalone では `import Mathlib`** までとし、具体的な import 最小化先は未確認とする。

## Comparator challenge 化の可否

### 判定: 定義単体では低適性

`zeroSectorW` 自体は

```lean
zeroSectorW d = 4 * (d : ℤ) ^ 5
```

を `rfl` で閉じる一行定義なので、証明比較問題としては情報量が少ない。

一方、派生問題として

$$
W\ge0,
$$

$$
0<d\Longrightarrow W>0,
$$

あるいは後続の `A,B` と組み合わせて

$$
B-A=8d^5
$$

を示す課題にすれば、`simp`、`ring`、`positivity`、cast 処理など複数の Lean 技法を比較できる。

したがって **定義そのものは challenge 不向きだが、`A,B` との差分恒等式まで含めれば良い Comparator challenge になる** と評価する。

## PDF との照合

対象 branch の repository tree には既存の

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

しかし今回利用可能な取得経路では binary PDF 本文を解析可能な形で取得できず、raw PDF の直接取得も成功しなかった。そのため PDF 内で `W=4d^5` が現れる具体的なページ番号・節番号・文言は確認できていない。

よって PDF との具体的対応は推測せず、Lean 正本の generated source と既存 theorem museum の確認可能な記述を根拠としている。

## 次に読むべき宣言

次は **0285 `zeroSectorA`** である。種別は `def`。

```lean
/-- The lower inversion factor `A = U-W`. -/
def zeroSectorA (r s : ℤ) (d : ℕ) : ℤ :=
  zeroSectorU r s - zeroSectorW d
```

すなわち

$$
A=U-W
$$

を導入し、0283 の中心量 `U` と本宣言の偏差量 `W` が初めて一つの inversion factor に結合される。