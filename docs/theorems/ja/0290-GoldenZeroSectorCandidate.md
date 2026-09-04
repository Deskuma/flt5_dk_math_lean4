# 0290 — `GoldenZeroSectorCandidate`

## 宣言種別

これは **`structure`** である。

0289 までで得られた zero-sector の符号・互いに素・ノルム・10 乗分離に関する情報を、後続の inversion 証明が一つの入力として扱えるようにまとめるレコード型である。

## Lean の型

```lean
/--
All raw hypotheses supplied by the zero-sector arithmetic receiver, including the
chosen tenth-power split.  No norm or coprimality provenance is discarded.
-/
structure GoldenZeroSectorCandidate where
  r : ℤ
  s : ℤ
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_b : Nat.Coprime a b
  five_not_dvd_b : ¬ 5 ∣ b
  norm_eq_or_eq_neg :
    goldenNorm ⟨r, s⟩ = (b : ℤ) ∨ goldenNorm ⟨r, s⟩ = -(b : ℤ)
  product_eq :
    s * goldenFifthSndFactor r s = -(5 : ℤ) ^ 6 * (a : ℤ) ^ 10
  coprime_coords : Nat.Coprime r.natAbs s.natAbs
  s_natAbs_eq : s.natAbs = 5 ^ 6 * c ^ 10
  H_natAbs_eq : (goldenFifthSndFactor r s).natAbs = d ^ 10
```

この宣言自体は命題を証明する theorem ではなく、以後の証明に必要なデータとその証拠を一つに束ねる **構造体の定義** である。

## 数学的意味

`GoldenZeroSectorCandidate` の一要素 $p$ は、整数座標

$$
(r,s)\in\mathbb Z^2
$$

と自然数パラメータ

$$
a,b,c,d\in\mathbb N
$$

を持ち、次の情報を同時に保持する。

まず

$$
a>0,\qquad b>0,\qquad \gcd(a,b)=1,\qquad 5\nmid b.
$$

さらに黄金整数座標 $(r,s)$ の norm について

$$
N(r,s)=b
\quad\text{または}\quad
N(r,s)=-b
$$

という符号付き同一視を保持する。Lean ではこれが

```lean
norm_eq_or_eq_neg :
  goldenNorm ⟨r, s⟩ = (b : ℤ) ∨
  goldenNorm ⟨r, s⟩ = -(b : ℤ)
```

として保存される。

zero-sector の中心的な積等式は

$$
s\,H(r,s)=-5^6a^{10},
$$

ここで

$$
H(r,s)=\texttt{goldenFifthSndFactor}(r,s).
$$

また primitive coordinate 条件として

$$
\gcd(|r|,|s|)=1
$$

を保持する。

そして 0281 までの arithmetic receiver が選んだ tenth-power split を

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}
$$

という二つの exact equation として保持する。

したがって、この structure は単なる座標の容器ではない。zero-sector で得た **算術的 provenance を失わずに inversion 層へ渡す証明証書** である。

## 証明全体での役割

0282–0289 では、

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
B=U+W,
\qquad
Q=5^5c^8
$$

という inversion 用の量と、四次因子の対角化・非負性が準備された。

0290 は、それらを実際の zero-sector candidate に適用するための **状態パケット** を作る境界である。

後続 theorem はすべて `p : GoldenZeroSectorCandidate` を受け取り、必要な仮定を `p.a_pos`、`p.product_eq`、`p.s_natAbs_eq` などの projection から取り出す。この設計によって、長い仮定列を theorem ごとに繰り返す必要がなくなる。

特に直後の 0291 `GoldenZeroSectorCandidate.product_neg` は

```lean
theorem product_neg (p : GoldenZeroSectorCandidate) :
    p.s * goldenFifthSndFactor p.r p.s < 0 := by
  rw [p.product_eq]
  have ha : (0 : ℤ) < p.a := by exact_mod_cast p.a_pos
  exact mul_neg_of_neg_of_pos (by norm_num) (pow_pos ha 10)
```

と、structure が保存した `product_eq` と `a_pos` をただちに利用する。

その後も正本では `H_pos`、`s_neg`、`c_pos`、`d_pos`、`H_eq_tenth`、`a_eq_c_mul_d`、`coprime_c_d`、`factor_product` などへ進む。したがって 0290 は、zero-sector arithmetic と inversion/factorization の間の API 境界として重要である。

## 直接依存する定義・型

### `goldenNorm`

黄金整数座標の norm。structure はその値が $\pm b$ のどちらかであるという情報を保存する。

### `goldenFifthSndFactor`

黄金整数の 5 乗第二座標に現れる四次因子

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4
$$

である。

`product_eq` と `H_natAbs_eq` の双方に現れる。

### `Nat.Coprime`

`coprime_a_b` と `coprime_coords` に使われる。後者では整数座標を `Int.natAbs` で自然数へ移してから互いに素性を記録する。

### `Int.natAbs`

符号付き整数 $r,s,H(r,s)$ の絶対値を自然数として扱うために使われる。

## 構築の流れ

structure 宣言なので、ここには theorem のような `by` proof は存在しない。Lean は各 field を持つレコード型と、その constructor、および projection を生成する。

概念的には、zero-sector arithmetic receiver が得た情報を次の順に詰める。

1. 基本座標 `r`, `s` と分解パラメータ `a`, `b`, `c`, `d` を保存する。
2. `a_pos`, `b_pos`, `coprime_a_b`, `five_not_dvd_b` で元の packet の primitive 情報を保存する。
3. `norm_eq_or_eq_neg` で norm の符号付き由来を保存する。
4. `product_eq` で zero-sector の負符号を伴う tenth-power product equation を保存する。
5. `coprime_coords` で座標の primitive 性を保存する。
6. `s_natAbs_eq`, `H_natAbs_eq` で chosen tenth-power split を保存する。

重要なのは、`c` と `d` だけを保存して元の情報を捨てるのではなく、`a,b`、norm、積等式、互いに素性も残している点である。source docstring の “No norm or coprimality provenance is discarded.” はこの設計を明示している。

## Lean 固有の処理

`structure ... where` により、Lean は自動的に

- constructor
- `p.r`, `p.s`, `p.a` などの projection
- 命題 field の projection `p.a_pos`, `p.product_eq` など

を生成する。

`r,s` は `ℤ`、`a,b,c,d` は `ℕ` と型が分かれているため、後続 proof では `exact_mod_cast` や `Int.natCast` を使った橋渡しが必要になる。実際、直後の `product_neg` は `p.a_pos : 0 < p.a` を整数上の

$$
0<(p.a:\mathbb Z)
$$

へ `exact_mod_cast` で移している。

また `coprime_coords` は `r,s` 自体ではなく `r.natAbs`, `s.natAbs` に対する `Nat.Coprime` として記録される。これは後続の自然数可除性 API と接続しやすい形である。

## 冗長・重複箇所

一見すると `product_eq` と `s_natAbs_eq` / `H_natAbs_eq` は情報が重複しているように見える。しかし完全な重複ではない。

`product_eq` は

$$
sH=-5^6a^{10}
$$

という **符号付き積全体** を保持し、後続の `product_neg` や `s_neg` に必要である。一方、二つの natAbs equation は

$$
|s|=5^6c^{10},\qquad |H|=d^{10}
$$

という **因子ごとの exact split** を保持し、`c_pos`, `d_pos`, `H_eq_tenth`, `a_eq_c_mul_d` などに必要である。

同様に `coprime_a_b` と `coprime_coords` も異なる段階の primitive 情報であり、単純には統合できない。

したがって現状の field 群には、明白な削除可能重複は見当たらない。

## 最適化候補

### 1. サブ structure に分ける

概念的には、

- 元 packet の情報
- signed zero-sector product 情報
- chosen tenth-power split

を別 structure に分け、`GoldenZeroSectorCandidate` がそれらを合成する設計も可能である。

ただし現在の proof 群は projection が浅く、`p.product_eq` のように直接読める。教育性と実装簡潔性の点では現在の flat structure に利点がある。

### 2. 派生 field の削減

将来、ある field が他の field から短く安定して再導出できることが確立したなら、structure を最小化する余地はある。しかし本 source は provenance を意図的に保持する方針を明言しているため、単なる論理的冗長性だけで field を除くのは設計目的に反する可能性がある。

### 3. `Prop` structure にするか

この structure は `: Prop` を明示せず、データ `r,s,a,b,c,d` 自体を保持する通常の structure である。後続で各 parameter を計算・再構成に使うため、この選択は自然である。単なる存在命題へ圧縮すると projection ベースの API が使いにくくなる。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 structure が直接利用する主要要素は、

- `ℤ`, `ℕ`
- `Nat.Coprime`
- `Int.natAbs`
- 整数・自然数の冪と可除性記法
- 既存の `goldenNorm`
- 既存の `goldenFifthSndFactor`

である。

structure 宣言自体には tactic は不要であるため、`ring`, `nlinarith`, `positivity` などは 0290 単体には必要ない。

ただしこの作業では Lean build を行わないため、元 module `SignedGoldenZeroSectorInversion.lean` の厳密な最小 import 集合は **未検証** である。`import Mathlib` からの具体的な削減先は推測で断定しない。

## Comparator challenge 化の可否

**そのまま theorem challenge にするには不向きだが、API 設計 challenge としては適している。**

proof hole を埋める種類の問題ではなく、必要な invariant をどの field として保存するかを設計する問題だからである。

Comparator 用にするなら、例えば後続 theorem 群

- `product_neg`
- `H_pos`
- `s_neg`
- `a_eq_c_mul_d`
- `coprime_c_d`

を成立させるために、どの最小 field set が必要かを比較する課題が適している。

通常の「Lean theorem の証明を完成させる」形式としての判定は **不向き**、structure/API design comparator としては **適する** とする。

## PDF との対応

対象 branch には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

日本語 PDF の repository file 自体と blob SHA は確認できたが、GitHub コネクタの通常 UTF-8 取得では binary 本文を解析できない。英語 PDF も UTF-8 decode error となった。

したがって、本 structure と PDF の具体的ページ・節番号・文言との対応は **未確認** であり、推測しない。ここでの技術的説明は対象 branch の Lean 正本を主根拠とする。

## 次に読むべき宣言

次は 0291 `GoldenZeroSectorCandidate.product_neg` である。種別は **`theorem`**。

```lean
theorem product_neg (p : GoldenZeroSectorCandidate) :
    p.s * goldenFifthSndFactor p.r p.s < 0 := by
  rw [p.product_eq]
  have ha : (0 : ℤ) < p.a := by exact_mod_cast p.a_pos
  exact mul_neg_of_neg_of_pos (by norm_num) (pow_pos ha 10)
```

0290 が保存した `product_eq` と `a_pos` を最初に利用し、

$$
p.s\,H(p.r,p.s)<0
$$

という符号情報へ変換する theorem である。
