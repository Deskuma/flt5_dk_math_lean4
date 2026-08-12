# 0030 — `coprime_GN5_y_of_coprime`

## 1. 展示対象

```lean
theorem coprime_GN5_y_of_coprime
    {g y : ℕ} (hgy : Nat.Coprime g y) :
    Nat.Coprime (GN5 g y) y := by
  refine (Nat.coprime_iff_gcd_eq_one).2 ?_
  by_contra hgcd
  rcases Nat.exists_prime_and_dvd (n := Nat.gcd (GN5 g y) y) hgcd with
    ⟨q, hq, hqgcd⟩
  have hqGN : q ∣ GN5 g y :=
    hqgcd.trans (Nat.gcd_dvd_left (GN5 g y) y)
  have hqy : q ∣ y := hqgcd.trans (Nat.gcd_dvd_right (GN5 g y) y)
  have hdecomp :
      GN5 g y =
        g ^ 4 +
          y * (5 * g ^ 3 + 10 * g ^ 2 * y + 10 * g * y ^ 2 + 5 * y ^ 3) := by
    unfold GN5
    ring
  have hqTail :
      q ∣ y * (5 * g ^ 3 + 10 * g ^ 2 * y + 10 * g * y ^ 2 + 5 * y ^ 3) :=
    dvd_mul_of_dvd_left hqy _
  rw [hdecomp] at hqGN
  have hqg4 : q ∣ g ^ 4 := (Nat.dvd_add_left hqTail).mp hqGN
  have hqg : q ∣ g := hq.dvd_of_dvd_pow hqg4
  exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqg hqy) hgy
```

宣言の完全修飾名は `DkMath.FLT.Five.coprime_GN5_y_of_coprime` である。

## 2. Lean の型

```lean
{g y : ℕ} → Nat.Coprime g y → Nat.Coprime (GN5 g y) y
```

入力は gap 座標 $g$ と第二座標 $y$ の互いに素性であり、出力は残余核 `GN5 g y` と $y$ の互いに素性である。追加の正値性や $5\nmid g$ は要求しない。

## 3. 数学的主張

$$
\gcd(g,y)=1 \Longrightarrow \gcd\bigl(GN5(g,y),y\bigr)=1.
$$

`GN5` の定義を $y$ の倍数部分が見える形に並べ替えると、

$$
GN5(g,y)=g^4+y\left(5g^3+10g^2y+10gy^2+5y^3\right).
$$

したがって $y$ を法として、

$$
GN5(g,y)\equiv g^4\pmod y.
$$

`GN5(g,y)` と $y$ の共通素因子 $q$ が存在すれば、上の合同式から $q\mid g^4$、素数性から $q\mid g$ となる。これは $q\mid y$ と合わせて $\gcd(g,y)=1$ に反する。

## 4. 証明全体での役割

本定理は `NormalForm.lean` の入口に置かれ、Reduction 層で得た局所座標の原始性を `GN5` 側へ転送する。

前段では Branch B における gap と `GN5` の互いに素性

$$
\gcd\bigl(g,GN5(g,y)\bigr)=1
$$

を確立した。本定理が与えるのは別方向の

$$
\gcd\bigl(GN5(g,y),y\bigr)=1
$$

である。この二つは同じ主張ではない。後続の normal-form 構造体や素因数分解では、`GN5` が gap だけでなく $y$ とも共通因子を持たないことが、各座標の原始性を保持するために使われる。

## 5. 直接依存する定義・補題

### リポジトリ内

- `DkMath.FLT.Five.GN5`

本証明は既存の名前付き分解定理を直接再利用せず、`GN5` を展開して専用の $y$-剰余分解をその場で証明する。

### Mathlib

- `Nat.coprime_iff_gcd_eq_one`
- `Nat.exists_prime_and_dvd`
- `Nat.gcd_dvd_left`
- `Nat.gcd_dvd_right`
- `dvd_mul_of_dvd_left`
- `Nat.dvd_add_left`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.not_coprime_of_dvd_of_dvd`
- `ring`

## 6. 証明の流れ

1. `Nat.Coprime (GN5 g y) y` を gcd が $1$ である形へ変換する。
2. gcd が $1$ でないと仮定する。
3. `Nat.exists_prime_and_dvd` で gcd の素因子 $q$ を取る。
4. gcd の左右への整除性から $q\mid GN5(g,y)$ と $q\mid y$ を得る。
5. `GN5` を

$$
GN5(g,y)=g^4+yT(g,y)
$$

の形へ展開する。
6. $q\mid y$ から $q\mid yT(g,y)$ を得る。
7. $q\mid GN5(g,y)$ から既知の tail を除き、$q\mid g^4$ を得る。
8. $q$ が素数なので $q\mid g$ を得る。
9. $q\mid g$ と $q\mid y$ は入力 `hgy` に矛盾する。

## 7. Lean 固有の処理

### `Coprime` から gcd 反証へ

```lean
refine (Nat.coprime_iff_gcd_eq_one).2 ?_
by_contra hgcd
```

`Nat.Coprime` を直接分解するのではなく、gcd が $1$ でないなら素因子を取れるという Mathlib の経路を選んでいる。

### gcd の素因子を左右へ配送

```lean
hqgcd.trans (Nat.gcd_dvd_left (GN5 g y) y)
hqgcd.trans (Nat.gcd_dvd_right (GN5 g y) y)
```

`hqgcd : q ∣ gcd ...` と gcd の標準整除性を推移律 `Dvd.dvd.trans` で合成している。

### 減算を使わない剰余抽出

```lean
have hqg4 : q ∣ g ^ 4 := (Nat.dvd_add_left hqTail).mp hqGN
```

自然数上で `GN5 - tail` を書かず、加法に関する整除性同値で $g^4$ を取り出す。切り捨て減算の順序条件を避ける堅牢な実装である。

### 冪から底への降下

```lean
have hqg : q ∣ g := hq.dvd_of_dvd_pow hqg4
```

素数 $q$ が $g^4$ を割るなら $g$ を割る、という一般補題を利用している。指数 $4$ の個別展開は不要である。

## 8. 冗長・重複箇所

本証明中の

```lean
have hdecomp :
    GN5 g y = g ^ 4 + y * (...) := by
  unfold GN5
  ring
```

は数学的に自然である一方、`GN5` の合同分解をその場で再構築している。既出の `GN5_eq_g_pow_four_add_five_mul` も $g^4$ と $5$ の倍数部分を分離するが、tail 全体が明示的に $y$ の倍数となる形ではない。そのため現状の証明は単純な重複とは言い切れない。

ただし `GN5(g,y) ≡ g^4 (mod y)` は再利用価値が高く、名前付き補題が存在しないなら局所的な重複候補である。

## 9. 最適化候補

### 候補 A: $y$-剰余分解を名前付き補題にする

```lean
theorem GN5_eq_g_pow_four_add_y_mul (g y : ℕ) :
    GN5 g y = g ^ 4 +
      y * (5 * g ^ 3 + 10 * g ^ 2 * y + 10 * g * y ^ 2 + 5 * y ^ 3) := by
  unfold GN5
  ring
```

これにより本証明は多項式正規化から分離され、後続の合同・互いに素性補題でも再利用できる。

### 候補 B: gcd の合同不変性を使う

Mathlib に適合する補題があれば、

$$
\gcd(g^4+yT,y)=\gcd(g^4,y)
$$

へ直接書き換え、`hgy.pow_left 4` から結論を得る短い証明も考えられる。ただし、使用可能な補題名と自然数加法の向きは未検証である。

### 候補 C: 素因子反証を共通化する

「gcd が $1$ でないと仮定し、共通素因子を取り、入力の `Coprime` と衝突させる」骨格は前段にも現れる。小さな局所補題や gcd API に寄せる余地があるが、抽象化がかえって読みづらくなる可能性もある。

## 10. 必要 Mathlib import と import 最適化候補

standalone 版は `import Mathlib` を使用しているため、本記事だけから厳密な最小 import は確定できない。

必要機能は少なくとも次の領域に属する。

- 自然数 gcd・coprime・素数・整除性
- 冪に対する素数整除
- 可換半環上の `ring` 正規化

候補としては gcd/coprime と prime divisibility を提供する数論モジュール、および `Mathlib.Tactic.Ring` の組合せまで縮小できる可能性がある。正確な import 名と閉包は Lean ビルドで検証すべきであり、本号では未検証の最適化案として扱う。

## 11. Comparator challenge 化

適している。

### Challenge

`GN5` の定義と `hgy : Nat.Coprime g y` から、

```lean
Nat.Coprime (GN5 g y) y
```

を証明せよ。

### 比較軸

- 現行の共通素因子反証
- 名前付き $y$-剰余分解を用いる版
- gcd の加法不変性を用いる短縮版
- `ring` の呼出し回数
- 自然数減算を導入しないか
- 使用 import の最小性

定理型が小さく、証明戦略の差が明瞭なので Comparator に向く。

## 12. 根拠と推測の区別

確認済みの事実:

- 定理型、証明本体、宣言順はリポジトリ内の生成済み standalone Lean ソースに基づく。
- 本定理は `NormalForm.lean` 生成区間の入口にある。
- 直後の宣言は `BranchBFifthPowerNormalForm` である。

解釈・未検証の提案:

- $y$-剰余分解を独立補題にする最適化。
- gcd の合同不変性を用いる短縮証明。
- 個別 Mathlib import への縮小案。

既存の日英 PDF は証明全体の物語的背景を補う資料として位置づけ、宣言の型と証明については Lean ソースを最終根拠とした。

## 13. 次に読むべき宣言

次は

```lean
DkMath.FLT.Five.BranchBFifthPowerNormalForm
```

を読む。

本定理で確立した `GN5` と $y$ の互いに素性を含め、Branch B の候補を後続証明が消費しやすい exact normal form として束ねる `Prop` 構造体である。