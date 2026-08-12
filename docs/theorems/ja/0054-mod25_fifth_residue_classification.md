# 0054 — `mod25_fifth_residue_classification`

## 1. Lean の宣言

```lean
/-- The finite mod-25 residue obstruction used by the signed routing theorem. -/
private theorem mod25_fifth_residue_classification :
    ∀ x y z : Fin 25,
      (x.1 ^ 5 + y.1 ^ 5) % 25 = z.1 ^ 5 % 25 →
      ¬ 5 ∣ x.1 →
      5 ∣ y.1 ∨ 5 ∣ z.1 := by
  -- native_decide
  decide +kernel
```

本宣言は `DkMath.FLT.Five` 名前空間内にあるが、`private` なのでファイル外から安定した完全修飾名で参照する公開 API ではない。本記事ではソース上の宣言名 `mod25_fifth_residue_classification` を用いる。

## 2. Lean の型

```lean
∀ x y z : Fin 25,
  (x.1 ^ 5 + y.1 ^ 5) % 25 = z.1 ^ 5 % 25 →
  ¬ 5 ∣ x.1 →
  5 ∣ y.1 ∨ 5 ∣ z.1
```

`x y z` は自然数そのものではなく、$0$ 以上 $25$ 未満の値を持つ `Fin 25` である。`.1` はその自然数値を取り出す射影である。

## 3. 数学的主張

法 $25$ の剰余代表 $x,y,z\in\{0,1,\dots,24\}$ が

$$
x^5+y^5\equiv z^5\pmod{25}
$$

を満たし、さらに

$$
5\nmid x
$$

ならば、

$$
5\mid y
\quad\text{または}\quad
5\mid z
$$

が成り立つ。

これは無限個の自然数に対する一般論を直接証明する補題ではなく、法 $25$ の有限な $25^3=15625$ 個の剰余三つ組を完全検査した有限分類である。

## 4. 証明全体での役割

前号までに、Branch B の反例候補から $5\nmid x$ が得られた。signed Branch A への routing には、残る座標について

$$
5\mid y
\quad\text{または}\quad
5\mid z
$$

という二分が必要である。

```text
Fermat5Equation x y z
        +
      5 ∤ x
        ↓ reduce modulo 25
mod25_fifth_residue_classification
        ↓
   5 ∣ y  ∨  5 ∣ z
        ↓
differenceGap / sumGap routing
```

本補題はその有限算術核である。直後の公開定理 `five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x` が自然数を法 $25$ の `Fin 25` へ落とし、本補題を適用して結果を自然数の整除へ戻す。

## 5. 直接依存する定義・補題

リポジトリ固有の宣言には直接依存しない。使用する主要要素は次である。

- `Fin 25`
- 自然数の第五冪 `x.1 ^ 5`
- 剰余 `% 25`
- 整除 `5 ∣ x.1`
- 選言 `Or`
- 決定可能命題を kernel reduction で閉じる `decide +kernel`

数学的背景としては第五冪剰余の法 $25$ 分類を表すが、その分類表を別補題として展開せず、有限決定手続きへ委ねている。

## 6. 証明の流れ

証明項は一行である。

1. `Fin 25` により三変数の探索空間を有限化する。
2. 等式、整除、否定、選言はいずれも decidable である。
3. `decide +kernel` が全入力に対する命題の真偽を正規化し、証明項を生成する。
4. コメントアウトされた `native_decide` は、より高速なネイティブ評価を試した痕跡と読めるが、現行証明は kernel 内の決定で完結する。

## 7. Lean 固有の処理

### 7.1 `private theorem`

`private` 宣言は同一ソースファイル内の補助実装であり、外部モジュールの API に含めない意図を示す。後続公開定理は本補題を包み、自然数上の安定した意味を提供する。

### 7.2 `Fin 25` と `.1`

`Fin 25` の要素は値と範囲証明の組である。`x.1` は値を取り出す。範囲は型に埋め込まれているため、決定手続きは有限な全要素を列挙できる。

### 7.3 `decide +kernel`

`decide` は命題の `Decidable` インスタンスを評価して証明を返す。`+kernel` は kernel reduction を明示的に用いる構文であり、外部ネイティブコード生成へ証明の信頼境界を広げない。

### 7.4 命題中の `% 25`

`x.1` 自体はすでに $25$ 未満だが、第五冪と和は範囲を越えるため、方程式側には明示的な `% 25` が必要である。

### 7.5 排他的選言ではない

結論は `5 ∣ y.1 ∨ 5 ∣ z.1` であり、両方が五で割れる可能性を排除しない。後続 routing に必要なのは少なくとも一方向の構成可能性である。

## 8. 冗長・重複箇所

命題の有限性から、証明は非常に短い。一方で数学的な理由は証明項に現れず、可読性の大部分をコメントと後続記事が担う。

`x.1 ^ 5` などの `.1` は三変数で繰り返されるが、`Fin` の値を使う以上は自然な記述である。法 $25$ の第五冪剰余集合を先に定義すれば式を短縮できるものの、補助 API が増える。

`-- native_decide` は実行されないコメントであり、完成コードだけを重視するなら削除可能である。ただし証明性能の選択履歴として残す価値はある。

## 9. 最適化候補

1. 数学的透明性を高めるなら、法 $25$ における第五冪剰余を分類する補題を明示し、そこから論理的に導出する。
2. 証明時間が問題になる場合は `native_decide` を再検討できる。ただしプロジェクトの信頼境界と CI 環境をそろえて判断すべきである。
3. `Fin 25` 上の第五冪写像を局所定義し、式の重複を減らす案があるが、本補題一件だけなら過剰抽象化になりやすい。
4. 一般化するなら、素数 $p$ と法 $p^2$ に対する同様の有限分類をパラメータ化できる。ただし命題自体が $p=5$ の特殊な剰余構造に依存するため、一般定理化には追加条件が必要である。
5. 公開 API として再利用する必要が生じた場合のみ `private` を外すべきである。現状は直後の自然数版公開定理が十分な境界を与える。

## 10. 必要な Mathlib import

対象ブランチの生成済み standalone ソースは全体として次を用いる。

```lean
import Mathlib
```

本補題単体で必要なのは、概ね `Fin`、自然数の整除・剰余・冪、決定手続きである。候補としては次の領域が関係する。

```lean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
```

ただし `decide +kernel` の構文と全インスタンスを含む厳密な最小 import は、分割元ファイルで import を削りながらビルドして測定しなければ確定できない。上記は推測を含む。

ファイル単位では同じ `SignedBranchA.lean` 内の前後定理が `norm_num`、`interval_cases`、自然数剰余補題を使うため、本補題だけを基準に import を狭めるよりモジュール全体で監査する方がよい。

## 11. Comparator challenge 化の可否

可能であり、有限計算証明の比較課題に適している。

### Challenge 案

次を二通りで証明せよ。

```lean
∀ x y z : Fin 25,
  (x.1 ^ 5 + y.1 ^ 5) % 25 = z.1 ^ 5 % 25 →
  ¬ 5 ∣ x.1 →
  5 ∣ y.1 ∨ 5 ∣ z.1
```

- 解法 A: `decide +kernel` または `native_decide` による有限決定。
- 解法 B: 第五冪剰余類を明示分類して手続き的に証明。

比較項目は証明時間、生成項の大きさ、可読性、信頼境界、法 $25$ から別の法への再利用性である。

## 12. 根拠と推測の区別

宣言名、`private` 指定、完全な型、コメント、`decide +kernel` による証明、および直後の公開定理から直接利用されることは、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` で確認した。

この補題の数学的動機を既存日英 PDF がどの節名で説明しているか、分割元 `DkMath/FLT/Five/SignedBranchA.lean` の厳密な最小 import は今回直接確認できていない。import 最小化の候補は推測として明示した。

## 13. 次に読むべき定理

次は本有限分類を自然数上の公開定理へ持ち上げる。

```lean
theorem five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x
    {x y z : ℕ} (hEq : Fermat5Equation x y z)
    (h5x : ¬ 5 ∣ x) :
    5 ∣ y ∨ 5 ∣ z := by
  ...
```

その後に `signedBranchA_normalForm_of_branchB` がこの二分を使い、差分型または和型の `SignedBranchANormalForm` を構成する。