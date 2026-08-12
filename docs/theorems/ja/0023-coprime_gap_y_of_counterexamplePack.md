# 0023 — `coprime_gap_y_of_counterexamplePack`

## Lean の型

```lean
theorem coprime_gap_y_of_counterexamplePack
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    Nat.Coprime (z - y) y
```

`CounterexamplePack x y z` から、自然数差として定義された gap `z - y` と第二基底 `y` が互いに素であることを導きます。

## 数学的主張

正の自然数が

$$
x^5+y^5=z^5
$$

を満たし、かつ入力が原始的であるとき、前号で得た

$$
\gcd(y,z)=1
$$

から

$$
\gcd(z-y,y)=1
$$

が従います。共通因子は差を取っても保存されるため、`y` と `z` が互いに素なら `y` と `z-y` も互いに素です。

## 証明全体での役割

この定理は、元の座標 `(y,z)` の互いに素性を、第五冪差の局所座標 `(g,y)`、すなわち `g=z-y` へ移します。

後続の Reduction 層では、

$$
GN5(g,y)\equiv 5y^4\pmod g
$$

を使って `g` と `GN5(g,y)` の共通素因子を調べます。その際、`Nat.Coprime g y` があることで、共通素因子が `y` から来る可能性を排除し、例外素数 `5` へ絞り込めます。本定理は、グローバルな Fermat 方程式から局所 gap 因数分解へ移る座標変換の互いに素性橋です。

## 直接依存する定義・補題

- `CounterexamplePack`
- `right_lt_of_fermat5Equation`
- `coprime_y_z_of_counterexamplePack`
- `Nat.coprime_sub_self_right`
- `Nat.coprime_comm`

直接の数学的入力は前号の `Nat.Coprime y z` です。`hPack.hx` と `hPack.hEq` は、自然数減算を正しい差として扱うための `y ≤ z` を得る際に使われます。

## 証明の流れ

Lean 本体は次の三段階です。

```lean
have hyz : y ≤ z :=
  (right_lt_of_fermat5Equation hPack.hx hPack.hEq).le
have hyGap : Nat.Coprime y (z - y) :=
  (Nat.coprime_sub_self_right hyz).2
    (coprime_y_z_of_counterexamplePack hPack)
simpa [Nat.coprime_comm] using hyGap
```

1. 正の `x` と Fermat 方程式から `y < z` を得て、`y ≤ z` に弱める。
2. `Nat.coprime_sub_self_right hyz` に前号の `Nat.Coprime y z` を渡し、`Nat.Coprime y (z-y)` を得る。
3. 目標は因子順が逆の `Nat.Coprime (z-y) y` なので、`Nat.coprime_comm` で対称化する。

## Lean 固有の処理

自然数の減算は切り捨て減算であるため、差に関する補題 `Nat.coprime_sub_self_right` は `y ≤ z` を要求します。数学上は自明に見える順序条件を、Lean では `right_lt_of_fermat5Equation` から明示的に供給しています。

`(Nat.coprime_sub_self_right hyz).2` は同値命題の逆向き、すなわち `Nat.Coprime y z` から `Nat.Coprime y (z-y)` を取り出します。最後の `simpa [Nat.coprime_comm]` は、互いに素性の引数順だけを正規化します。

## 冗長・重複箇所

`right_lt_of_fermat5Equation` を再度呼び出して `y ≤ z` を構成しています。後続の多くの補題でも gap の正値性や順序を必要とするなら、`CounterexamplePack` から `y<z`、`y≤z`、`0<z-y` をまとめて提供する小さな API 層を置く余地があります。ただし現行の一行取得は十分に軽量です。

`hyGap` は最終目標と引数順だけが異なります。定理の結論を `Nat.Coprime y (z-y)` とすれば最後の対称化は不要ですが、後続の因数分解では gap を第一引数に置く現行 API の方が自然です。

## 最適化候補

- `Nat.Coprime (z-y) y` を直接返す既存補題が Mathlib にあるか監査すれば、最後の `simpa` を省ける可能性があります。未検証です。
- `CounterexamplePack.coprime_gap_y` のような namespace method にすると、後続コードで `hPack.coprime_gap_y` と読めます。
- 前号と本号を一般補題「`Coprime y z` と `y≤z` から `Coprime (z-y) y`」へ抽象化する必要は薄く、Mathlib の既存補題がすでにその役割を担っています。

## 必要 Mathlib import と import 最適化候補

standalone 生成物は `import Mathlib` を使用しています。本定理が直接使う Mathlib 機能は、自然数の順序、切り捨て減算、`Nat.Coprime`、`Nat.coprime_sub_self_right`、`Nat.coprime_comm` です。加えて DkMath 側の `Basic` と直前の Reduction 補題に依存します。

元の分割モジュールの厳密な最小 import 集合はこの記事ではビルド検証していません。自然数 gcd・互いに素性を供給する個別 Mathlib モジュールへ縮小できる可能性はありますが、未検証の import 最適化案です。

## Comparator challenge 化

小規模な Comparator challenge に適しています。

- 現行の `Nat.coprime_sub_self_right` による三段階証明
- gcd 等式へ展開して算術的に差を処理する証明
- 引数順を最初から後続用途に揃える API 設計

評価軸は、自然数減算の安全性、利用する高水準 API の適切さ、証明行数、後続コードでの使いやすさです。gcd の素因子反証を再実装する案は、既存 Mathlib 補題を使う現行証明より冗長になる可能性が高いです。

## 根拠と推測の区別

定理型、証明本体、宣言順、Reduction 層での役割は、リポジトリ内の `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/Reduction.lean` 生成区間を根拠とします。import の最小化、namespace method 化、補助 API の追加は未検証の提案です。既存 PDF は FLT5 証明全体の文脈を補いますが、本記事の形式的根拠は Lean ソースです。

## 次に読むべき定理

`DkMath.FLT.Five.dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5`

これは、素数または一般の因子が gap と `GN5(g,y)` の双方を割るなら、合同分解

$$
GN5(g,y)=gA+5y^4
$$

から

$$
q\mid 5y^4
$$

を導く補題です。今回確立した `Nat.Coprime (z-y) y` と結合し、共通素因子を例外素数 `5` へ絞る段階へ進みます。