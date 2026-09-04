# 0103 — `squareGolden_square_discriminant`

## Lean の型

```lean
theorem squareGolden_square_discriminant (z y : ℕ) :
    (SquareGoldenM z y) ^ 2 - 4 * (SquareGoldenN z y) ^ 2 =
      ((z : ℤ) ^ 2 - (y : ℤ) ^ 2) ^ 2 := by
  unfold SquareGoldenM SquareGoldenN
  exact endpoint_square_discriminant (z : ℤ) (y : ℤ)
```

## 数学的主張

0100 `SquareGoldenM` と 0101 `SquareGoldenN` を

$$
M=z^2+y^2,\qquad N=zy
$$

と書けば、本定理は

$$
M^2-4N^2=(z^2-y^2)^2
$$

を主張する。

左辺は差の平方へ因数分解でき、

$$
M^2-4N^2=(M-2N)(M+2N)
$$

である。一方、endpoint 座標を代入すると

$$
M-2N=(z-y)^2,
$$

かつ

$$
M+2N=(z+y)^2
$$

なので、積は

$$
(z-y)^2(z+y)^2=(z^2-y^2)^2
$$

となる。

ただし Lean 証明はこの因数分解経路を再構成せず、0098 `endpoint_square_discriminant` を直接再利用する。

## 証明全体での役割

`SquareGoldenNormalForm.lean` では、Branch-B の fifth-power normal form を square/golden 座標 $(M,N)$ に射影し、複数の保存量を同時に保持する packet を構成する。

0102 `squareGolden_tenth_boundary_base` が

$$
M-2N=(z-y)^2
$$

という低次数の平方境界を提供したのに対し、本定理は

$$
M^2-4N^2=(z^2-y^2)^2
$$

という独立な square discriminant を提供する。

後続 `exists_branchB_squareGoldenNormalForm` では

```lean
have hSquare := squareGolden_square_discriminant z y
```

として本定理がそのまま取得され、最終的な `BranchBSquareGoldenNormalForm` packet の square-discriminant 成分へ渡される。

したがって本定理の役割は、新しい座標 API において「endpoint-square 判別式が完全平方である」という既存事実を明示的な invariant として保存することである。

## 直接依存する定義・補題

project-local な直接依存は三つである。

1. 0100 `SquareGoldenM`
2. 0101 `SquareGoldenN`
3. 0098 `endpoint_square_discriminant`

定義は

```lean
def SquareGoldenM (z y : ℕ) : ℤ :=
  (z : ℤ) ^ 2 + (y : ℤ) ^ 2

def SquareGoldenN (z y : ℕ) : ℤ :=
  (z : ℤ) * (y : ℤ)
```

であり、再利用される補題は

```lean
theorem endpoint_square_discriminant (z y : ℤ) :
    (z ^ 2 + y ^ 2) ^ 2 - 4 * (z * y) ^ 2 =
      (z ^ 2 - y ^ 2) ^ 2 := by
  ring
```

である。

## 証明の流れ

証明は二段である。

### 1. square/golden 座標を展開する

```lean
unfold SquareGoldenM SquareGoldenN
```

これにより goal は整数上で

```lean
(((z : ℤ) ^ 2 + (y : ℤ) ^ 2) ^ 2
    - 4 * (((z : ℤ) * (y : ℤ)) ^ 2)) =
  (((z : ℤ) ^ 2 - (y : ℤ) ^ 2) ^ 2)
```

という形になる。

### 2. 既存の endpoint 補題を適用する

```lean
exact endpoint_square_discriminant (z : ℤ) (y : ℤ)
```

展開後の goal が 0098 の型と一致するため、その proof term をそのまま流用して閉じる。

ここで重要なのは、本 theorem 自体は `ring` を実行していないことである。計算は 0098 に集約され、本 theorem は API adaptation のみを担当する。

## Lean 固有の処理

### 1. `ℕ` から `ℤ` への境界は定義側で吸収されている

入力 `z y` は自然数だが、`SquareGoldenM` と `SquareGoldenN` は整数値を返す。`unfold` 後には `(z : ℤ)`、`(y : ℤ)` が明示され、0098 の整数引数へそのまま渡せる。

### 2. cast tactic が不要

証明では `push_cast`、`norm_cast`、`exact_mod_cast` を使わない。必要な coercion は theorem application の引数

```lean
(z : ℤ) (y : ℤ)
```

で明示されている。

### 3. `exact` が通ること自体が API 一致の監査になる

`simpa` や `ring` で差異を吸収せず `exact` で閉じているため、座標定義を unfold した形と 0098 の statement が定義的に一致していることが明瞭である。

## 冗長・重複箇所

数学的には本 theorem と 0098 は同じ恒等式を表す。本 theorem は 0098 を `(SquareGoldenM, SquareGoldenN)` API へ再包装した wrapper であり、計算内容の追加はない。

したがって証明コードだけを最小化するなら、後続で毎回 0098 を直接使うことも可能である。しかしそれでは `SquareGoldenNormalForm` 層の利用者が内部の endpoint 表現へ降りる必要があり、抽象化境界が崩れる。

この重複は冗長というより、下位補題を上位 vocabulary に持ち上げる意図的な API duplication と見るのが自然である。

0102 とも近い。0102 は

$$
M-2N=(z-y)^2
$$

、本 theorem は

$$
M^2-4N^2=(z^2-y^2)^2
$$

を保存する。どちらも平方性を示すが、後続 packet では別フィールドとして保持されるため役割は独立している。

## 最適化候補

### 候補 A — `[SquareGoldenM, SquareGoldenN]` を `simpa` で展開する

現在は

```lean
unfold SquareGoldenM SquareGoldenN
exact endpoint_square_discriminant (z : ℤ) (y : ℤ)
```

である。例えば

```lean
simpa [SquareGoldenM, SquareGoldenN] using
  endpoint_square_discriminant (z : ℤ) (y : ℤ)
```

という一式への短縮候補がある。

短い一方、現在形は「座標を展開する」「既存補題を適用する」という二段構造が明確で、監査性では優位である。

### 候補 B — endpoint 座標 pair / structure の API 化

`SquareGoldenM` と `SquareGoldenN` が今後常に対で現れるなら、座標 pair や structure を導入し、その invariant theorem として本結果を持たせる設計も考えられる。

ただし現段階では二つの軽量 `def` と wrapper theorem のほうが proof surface は小さい。

### 候補 C — 0102 から因数分解で導く

0102 と恒等式

$$
M^2-4N^2=(M-2N)(M+2N)
$$

を用いて導くことも可能だが、追加で $M+2N=(z+y)^2$ が必要になる。既に 0098 がある以上、この経路は証明を長くするだけである。

## 必要 Mathlib import と import 最適化候補

standalone artifact は

```lean
import Mathlib
```

を使用している。

本 theorem 自体が直接必要とするのは、整数・自然数 coercion、`SquareGoldenM` / `SquareGoldenN`、そして既に証明済みの `endpoint_square_discriminant` である。本 theorem 内では tactic として `ring` を呼ばない。

ただし依存先 0098 の証明は `ring` を使用するため、その source module まで含めた依存閉包では `Mathlib.Tactic.Ring` 系が必要になると考えられる。

module 全体には後続で `exact_mod_cast` なども現れるため、`SquareGoldenNormalForm.lean` 全体の最小 import は Lean build なしには断定しない。import 最適化を行うなら、まず project-local な `SquareGoldenBridge` 依存と tactic import を分離し、段階的な build 検証を行うのが安全である。本回では Lean build は実施していない。

## Comparator challenge 化の可否

非常に適している。数学的計算ではなく wrapper theorem の設計比較になるため、通常の `ring` challenge とは異なる評価ができる。

比較候補は次である。

1. 現行の `unfold ...; exact ...`。
2. `simpa [SquareGoldenM, SquareGoldenN] using ...`。
3. `unfold ...; ring` として 0098 を再利用しない方式。
4. 0102 と因数分解補題から構成する方式。

評価軸は proof term の短さだけでなく、依存の再利用性、抽象化境界、監査性、下位補題の変更に対する安定性である。

この theorem では、計算を再実行するより既存 theorem を `exact` で再利用する現行形が設計意図を最もよく表している可能性が高い。

## 次に読むべき宣言

Lean source で本 theorem の直後に置かれている主要宣言は

```lean
structure BranchBSquareGoldenNormalForm
    (x y z a b : ℕ) : Prop where
  normal : BranchBFifthPowerNormalForm x y z a b
  golden_eq :
    GoldenNorm (SquareGoldenM z y) (SquareGoldenN z y) = (b : ℤ) ^ 5
  tenth_boundary :
    SquareGoldenM z y - 2 * SquareGoldenN z y = (a : ℤ) ^ 10
  square_discriminant :
    (SquareGoldenM z y) ^ 2 - 4 * (SquareGoldenN z y) ^ 2 =
      ((z : ℤ) ^ 2 - (y : ℤ) ^ 2) ^ 2
  discriminant_five :
    (2 * SquareGoldenM z y + SquareGoldenN z y) ^ 2 -
        5 * (SquareGoldenN z y) ^ 2 = 4 * (b : ℤ) ^ 5
```

である。

ここで 0102 の tenth-power boundary と本 0103 の square discriminant、さらに golden norm と判別式 5 の情報が一つの packet にまとめられる。

したがって次号は `BranchBSquareGoldenNormalForm` を読むのが依存順として自然である。

## 根拠と注記

形式的根拠は `docs/flt5-theorem-museum` ブランチ上の generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` に含まれる `SquareGoldenNormalForm.lean` 区間である。そこでは本 theorem が 0102 相当の `squareGolden_tenth_boundary_base` の直後にあり、後続 `exists_branchB_squareGoldenNormalForm` で `have hSquare := squareGolden_square_discriminant z y` として直接利用されている。

既存日本語・英語 PDF の本 theorem に対する具体的なページ対応は本回では確認できなかった。GitHub code search は upstream error となったため、PDF のページ番号・節番号・叙述対応を推測で補っていない。

standalone artifact は generated file であり、split source 名として `DkMath/FLT/Five/SquareGoldenNormalForm.lean` を記録している。本記事では対象ブランチ上で取得した現在の standalone 内容を一次的な形式根拠としている。