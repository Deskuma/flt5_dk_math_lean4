# 0022 — `coprime_y_z_of_counterexamplePack`

## Lean の型

```lean
theorem coprime_y_z_of_counterexamplePack
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    Nat.Coprime y z
```

`CounterexamplePack x y z` から、第二基底 `y` と結果基底 `z` が互いに素であることを導く定理です。

## 数学的主張

正の自然数が

$$
x^5+y^5=z^5
$$

を満たし、かつ $\gcd(x,y)=1$ ならば、

$$
\gcd(y,z)=1
$$

です。実際、`y` と `z` の共通素因子 $q$ があれば、方程式から $q\mid x^5$、したがって素数性により $q\mid x$ となり、$q\mid x$ かつ $q\mid y$ が原始性に反します。

## 証明全体での役割

この定理は、入力で仮定された `Nat.Coprime x y` から、方程式が強制する新しい互いに素性 `Nat.Coprime y z` を回収します。直後に gap $g=z-y$ と `y` の互いに素性を導くための基礎となり、`GN5(g,y)` と gap の共通素因子を例外素数 $5$ に絞る Reduction 層へ渡します。

## 直接依存する定義・補題

- `CounterexamplePack` とそのフィールド `hEq`, `hxy`
- `Nat.coprime_iff_gcd_eq_one`
- `Nat.exists_prime_and_dvd`
- `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right`
- `dvd_pow_self`
- `Nat.dvd_add_left`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.not_coprime_of_dvd_of_dvd`

## 証明の流れ

1. `Nat.Coprime y z` を `Nat.gcd y z = 1` に変換する。
2. gcd が $1$ でないと仮定し、その gcd を割る素数 $q$ を取る。
3. $q\mid y$ と $q\mid z$ を得て、第五冪にも持ち上げる。
4. 方程式 $x^5+y^5=z^5$ から $q\mid x^5$ を得る。
5. 素数性から $q\mid x$ を得る。
6. $q$ が `x` と `y` の共通因子となるため、`hPack.hxy` と矛盾する。

Lean 本体の核は次の区間です。

```lean
have hqsum : q ∣ x ^ 5 + y ^ 5 := by
  rw [hPack.hEq]
  exact hqzp
exact (Nat.dvd_add_left hqyp).mp hqsum
```

## Lean 固有の処理

`by_contra hg` 後の `hg` は `Nat.gcd y z ≠ 1` です。`Nat.exists_prime_and_dvd` が非単位 gcd から素因子を供給します。第五冪への持ち上げでは `dvd_pow_self` に指数非零証明 `(by decide : 5 ≠ 0)` を渡しています。

`Nat.dvd_add_left hqyp` は、$q\mid y^5$ のもとで $q\mid x^5+y^5$ と $q\mid x^5$ を同値化する消去 API として使われます。最後は `Nat.not_coprime_of_dvd_of_dvd` が共通素因子から非互いに素性を生成し、`hPack.hxy` に適用して矛盾を閉じます。

## 冗長・重複箇所

`hqyp` と `hqzp` の構成は同型です。ただし、後者は方程式右辺を、前者は加法の一項を処理するため、名前を分けた現行証明は読みやすさがあります。

`hPack.hEq` は `Fermat5Equation` の定義ですが、`rw [hPack.hEq]` がそのまま成功しており、ここでは明示的な `unfold Fermat5Equation` は不要です。

## 最適化候補

- 共通補題「$a^n+b^n=c^n$ と `Coprime a b` から `Coprime b c`」へ一般化できる可能性があります。ただし指数正値条件と既存 Mathlib API の調査が必要で、未検証です。
- `dvd_pow_self` の代わりに `dvd_pow` 系 API を使う形も比較可能ですが、現行形は具体的で明瞭です。
- term proof への圧縮は可能でも、素因子反証の各段階が見えにくくなるため、博物館用途では現行構造が適切です。

## 必要 Mathlib import と import 最適化候補

standalone 生成物は `import Mathlib` のみを使用しています。確認できる機能上の依存は、自然数 gcd・素数・整除性・冪に関する Mathlib API と、`CounterexamplePack` を定義する先行モジュールです。

元の分割モジュール `Reduction.lean` の最小 import 行は生成済み standalone からは復元できません。候補として `DkMath.FLT.Five.Basic` と自然数の gcd・素数・整除性を供給する個別 Mathlib モジュールへ縮小できますが、正確な最小集合は import 監査とビルド確認が必要な未検証提案です。

## Comparator challenge 化

適しています。比較対象として次が考えられます。

- gcd を $1$ と示す現行の素因子反証
- `Nat.Coprime` の消去・転送補題を中心にした証明
- 指数を一般の正整数へ抽象化した補題

評価軸は、補題数、明示的な整除性中間項、Mathlib API への依存、一般化可能性、可読性です。

## 根拠と推測の区別

定理型・証明本体・宣言順・Reduction 層の説明はリポジトリ内の `Flt5DkMath/FLT5StandAlone.lean` を根拠とします。import 最小化と一般指数への抽象化は未検証の最適化案です。既存 PDF は証明全体の数学的文脈を補いますが、本記事の形式的根拠は Lean ソースです。

## 次に読むべき定理

`DkMath.FLT.Five.coprime_gap_y_of_counterexamplePack`

今回得た `Nat.Coprime y z` を差 $z-y$ へ移し、

$$
\gcd(z-y,y)=1
$$

を確立する次の Reduction 補題です。