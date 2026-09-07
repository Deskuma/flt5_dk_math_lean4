# 0333 — `GoldenZeroSectorFactorBranch`

## 宣言種別

この宣言は theorem ではなく **`inductive`** である。

零セクター factorization で現れる二進的な場合分けを、三つの constructor を持つ有限型として定義する。

```lean
/-- The exhaustive two-adic branch label. -/
inductive GoldenZeroSectorFactorBranch
  | odd
  | evenLeftLow
  | evenRightLow
  deriving DecidableEq
```

## Lean の型

宣言後、Lean には新しい型

```lean
GoldenZeroSectorFactorBranch : Type
```

と三つの constructor

```lean
GoldenZeroSectorFactorBranch.odd : GoldenZeroSectorFactorBranch
GoldenZeroSectorFactorBranch.evenLeftLow : GoldenZeroSectorFactorBranch
GoldenZeroSectorFactorBranch.evenRightLow : GoldenZeroSectorFactorBranch
```

が導入される。

さらに

```lean
deriving DecidableEq
```

により、branch 同士の等号が決定可能になる。

したがって例えば

```lean
b = .odd
```

のような命題を計算可能な判定として扱え、後続 theorem では branch equality を仮定として受け取り、`cases` や `simp` で不一致 branch を排除できる。

## 数学的意味

この宣言自体は新しい数論定理を主張しない。

役割は、零セクター反転後の factorization に現れる二進付値の配置を三種類へ分類する **有限ラベル型** を与えることである。

三 constructor は次の branch を表す。

### `odd`

奇数側の branch である。

直後の `GoldenZeroSectorFactorData.odd` では、自然数 $e,f$ を用いて

$$
A_0 = 2e^5,
\qquad
B_0 = 2f^5
$$

という形を持ち、$e,f$ はともに奇数となる。

この branch では差分から

$$
e^5 + 4d^5 = f^5
$$

が得られ、直前の `eleven_dvd_d_of_fifth_add_four_fifth` による mod 11 obstruction が適用される。

### `evenLeftLow`

偶数側のうち、左因子 $A_0$ が相対的に低い二進指数を持つ branch のラベルである。

直後の factor data では

$$
A_0 = 8e^5,
\qquad
B_0 = 16f^5
$$

と記録される。

### `evenRightLow`

左右を反転した branch であり、直後の factor data では

$$
A_0 = 16e^5,
\qquad
B_0 = 8f^5
$$

となる。

重要なのは、これらの数式や奇偶性は **この `inductive` 宣言そのものには field として含まれていない** ことである。この型はあくまで branch の名前だけを持つ。具体的な数論的証明データは次の `GoldenZeroSectorFactorData` に格納される。

## 証明全体での役割

この宣言は、零セクターの反転 packet から完全な factor packet へ進む境界で、二進場合分けを **型レベルの有限状態** に変換する。

ここまでの流れでは、`GoldenZeroSectorInversionPacket` に

- factor product
- factor difference
- coprimality
- 奇偶性
- 自然数 factor の正性

などが集約されていた。

さらに前段で

- `odd_factor_halves`
- `coprime_Q_d`
- `fifth_mod_eleven_cases`
- `eleven_dvd_d_of_fifth_add_four_fifth`

が整備され、odd branch と even branch を解析するための局所補題が揃った。

今回の `GoldenZeroSectorFactorBranch` は、それらの解析結果を以後

```text
odd / evenLeftLow / evenRightLow
```

という三状態で参照できるようにする。

直後の `GoldenZeroSectorFactorData` はこの三分岐と一対一に対応する constructor を持ち、それぞれに第五冪因子化、互いに素性、所有関係、差分方程式を載せる。

したがってこの宣言は、数論的場合分けを単なる proof script 内の `by_cases` や disjunction のまま残さず、後続 API が参照可能な **明示的 branch vocabulary** へ昇格させる役割を持つ。

## 直接依存する定義・補題

プロジェクト固有の定義・補題への直接依存はない。

この宣言は単独の列挙型であり、前段の `GoldenZeroSectorInversionPacket` や各 theorem を constructor の型に含めていない。

Lean 言語機能として直接使っているのは次だけである。

### `inductive`

有限個の constructor からなる帰納型を定義する。

### `deriving DecidableEq`

`GoldenZeroSectorFactorBranch` の等号判定器を自動生成する。

数学的な意味付けは前後のコードから与えられているが、Lean の依存グラフだけを見ると非常に軽量な宣言である。

## 構築の流れ

この宣言には `by` 以下の proof script は存在しない。構築は型定義そのもので完結する。

### 1. 新しい branch 型を宣言する

```lean
inductive GoldenZeroSectorFactorBranch
```

により、factorization branch 専用の型を導入する。

### 2. 三つの constructor を列挙する

```lean
  | odd
  | evenLeftLow
  | evenRightLow
```

これにより branch が三種類に閉じていることが型定義として保証される。

任意の

```lean
b : GoldenZeroSectorFactorBranch
```

は必ずこの三つのいずれかである。

### 3. 等号判定を導出する

```lean
  deriving DecidableEq
```

により、後続で branch equality を計算・簡約できる。

特に直後の `GoldenZeroSectorFactorData.branch` は factor data をこのラベルへ射影し、その次の `GoldenZeroSectorFactorData.odd_eleven_channel` では

```lean
hbranch : data.branch = .odd
```

を受け取って non-odd constructor を `simp` で排除する。

## Lean 固有の処理

### constructor 名による exhaustiveness

Lean の `inductive` なので、三 constructor 以外の値は作れない。

したがって「三 branch が exhaustive である」という性質は別 theorem として証明する必要がなく、型の elimination principle に組み込まれる。

### `DecidableEq` の自動導出

branch は payload を持たない有限 constructor 型なので、等号判定は機械的に生成できる。

後続では `.odd` のような短縮記法と組み合わせて branch equality を扱える。

### 数論データとラベルの分離

この型に $e,f$ や因子化等式を直接持たせず、次の dependent inductive `GoldenZeroSectorFactorData p` に実データを委ねている。

この分離により、branch 名だけを必要とする API と、証明 witness まで必要とする API を区別できる。

## 冗長・重複箇所

宣言は最小に近く、コード上の冗長性はほぼない。

三 constructor 名は、直後の `GoldenZeroSectorFactorData` の三 constructor と同名で対応しているため、表面的には名前が重複する。しかしこれは意図的な対応であり、

```lean
GoldenZeroSectorFactorData.branch
```

が

```lean
| .odd .. => .odd
| .evenLeftLow .. => .evenLeftLow
| .evenRightLow .. => .evenRightLow
```

と自然に書ける利点がある。

この重複は削除対象というより、ラベル層と証明データ層の対応を明示する設計上の重複と見るべきである。

## 最適化候補

### 1. `Fin 3` や `Bool × ...` への置換は不要

三状態だけなら `Fin 3` のような一般有限型でも表現できるが、`odd`, `evenLeftLow`, `evenRightLow` という数学的意味が失われる。

現行 `inductive` の方が圧倒的に可読性が高い。

### 2. `deriving Repr` の追加

デバッグや `#eval` で branch を表示する用途が増えるなら `Repr` を derive する余地はある。

ただし現在の証明 API では `DecidableEq` が主要用途であり、必要性は確認できない。

### 3. branch 型自体へ証明データを統合しない

`GoldenZeroSectorFactorBranch` を indexed inductive にして各 branch の不変量まで持たせる設計も可能だが、直後に `GoldenZeroSectorFactorData` がその役割を担っている。

したがって現状の「軽いラベル型 + 重い dependent data 型」という二層構成は整理されている。

## 必要 Mathlib import と import 最適化候補

standalone 正本全体は

```lean
import Mathlib
```

を使用している。

しかし、この宣言単体が使うのは Lean の基本的な `inductive` と `DecidableEq` deriving 機構だけであり、Mathlib 固有 API は直接参照していない。

そのため **この宣言単体だけなら `import Mathlib` は明らかに過大** と考えられる。

一方、実際には同じファイル内で多数の Mathlib 定理・tactic を利用しているため、ファイル全体の import をこの宣言だけを理由に縮められるわけではない。また今回は Lean ビルドを行わないため、standalone 抽出時の厳密な最小 import は検証していない。

## Comparator challenge 化の可否

**単体では低〜中程度、周辺設計を含めれば適している。**

宣言そのものは三 constructor の enum なので、proof challenge として比較する余地は小さい。

一方で API 設計 challenge としては次を比較できる。

1. 現行の専用 `inductive` ラベル型
2. branch label を持たず `GoldenZeroSectorFactorData` の constructor だけで場合分けする設計
3. `Fin 3` 等の一般有限型をラベルにする設計
4. branch と factor proof data を一つの indexed structure / inductive に統合する設計

評価軸は、pattern matching の可読性、後続 theorem の型、`simp` の扱いやすさ、証明データと状態ラベルの分離、将来 branch が増えた場合の保守性である。

特に現行設計は `GoldenZeroSectorFactorData.branch` という明示射影を一枚挟むため、「ラベルを独立型として持つ価値」が Comparator の主題になる。

## 次に読むべき宣言

正本上で次の宣言は

```lean
inductive GoldenZeroSectorFactorData
    (p : GoldenZeroSectorInversionPacket) : Type
  | odd ...
  | evenLeftLow ...
  | evenRightLow ...
```

である。

したがって次の連番は **0334 `GoldenZeroSectorFactorData`** となる。

これは theorem ではなく **dependent `inductive`** 宣言である。今回の `GoldenZeroSectorFactorBranch` が三 branch の名前だけを定義したのに対し、`GoldenZeroSectorFactorData p` は各 branch に

- 第五冪 base $e,f$
- 正性
- `Nat.Coprime e f`
- $d$ との coprimality
- 奇偶性
- $A_0,B_0$ の正確な第五冪因子化
- `zeroSectorQ` の ownership
- branch 固有の差分方程式

を証明付きで格納する。

つまり 0333 が **branch vocabulary**、0334 が **branch certificate** という関係であり、次は factorization phase の実質的なデータ型へ進む。