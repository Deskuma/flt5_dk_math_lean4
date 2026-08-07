# 0055 — `five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x`

## 1. Lean の宣言

```lean
/-- A fifth-power equation with `5 ∤ x` forces five into `y` or `z`. -/
theorem five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x
    {x y z : ℕ} (hEq : Fermat5Equation x y z)
    (h5x : ¬ 5 ∣ x) :
    5 ∣ y ∨ 5 ∣ z := by
  let xr : Fin 25 := ⟨x % 25, Nat.mod_lt _ (by decide)⟩
  let yr : Fin 25 := ⟨y % 25, Nat.mod_lt _ (by decide)⟩
  let zr : Fin 25 := ⟨z % 25, Nat.mod_lt _ (by decide)⟩
  have hEqNat : x ^ 5 + y ^ 5 = z ^ 5 := by
    simpa [Fermat5Equation] using hEq
  have hEqMod :
      ((x % 25) ^ 5 + (y % 25) ^ 5) % 25 = (z % 25) ^ 5 % 25 := by
    have h := congrArg (fun n : ℕ => n % 25) hEqNat
    simpa [Nat.add_mod, Nat.pow_mod] using h
  have h5xr : ¬ 5 ∣ x % 25 := by
    intro h
    exact h5x ((Nat.dvd_mod_iff (by norm_num : 5 ∣ 25)).mp h)
  have hres := mod25_fifth_residue_classification xr yr zr
  have hfinite : 5 ∣ y % 25 ∨ 5 ∣ z % 25 := by
    simpa [xr, yr, zr] using hres hEqMod h5xr
  rcases hfinite with h5yr | h5zr
  · exact Or.inl ((Nat.dvd_mod_iff (by norm_num : 5 ∣ 25)).mp h5yr)
  · exact Or.inr ((Nat.dvd_mod_iff (by norm_num : 5 ∣ 25)).mp h5zr)
```

## 2. Lean の型

```lean
{x y z : ℕ} →
Fermat5Equation x y z →
(¬ 5 ∣ x) →
5 ∣ y ∨ 5 ∣ z
```

自然数上の指数 5 の Fermat 方程式と `5 ∤ x` を受け取り、残る二座標の少なくとも一方へ 5 が入ることを返す公開定理である。

## 3. 数学的主張

$$
x^5+y^5=z^5,
\qquad
5\nmid x
$$

ならば、

$$
5\mid y
\quad\text{または}\quad
5\mid z
$$

が成り立つ。

この定理の実装は、自然数上で直接剰余類を議論するのではなく、各座標を法 $25$ の代表へ落として前号 0054 の有限分類を利用する。

## 4. 証明全体での役割

Branch B 側からは既刊 0048 により `5 ∤ x` が得られる。signed Branch A へ接続するには、次に「5 がどこへ入るか」を `y` と `z` の二方向へ分ける必要がある。

```text
CounterexamplePack x y z
        +
Branch B: 5 ∤ (z - y)
        ↓ 0048
      5 ∤ x
        ↓ 0055
  5 ∣ y  ∨  5 ∣ z
      ↙             ↘
0050 difference     0051 sum
      ↘             ↙
 SignedBranchAOrientation
```

`5 ∣ y` の枝では 0050 により `5 ∣ z - x` を得て、交換後の `CounterexamplePack y x z` に `differenceGap` を付けられる。`5 ∣ z` の枝では 0051 により `5 ∣ x + y` を得て、元の pack に `sumGap` を付けられる。

したがって本定理は、Branch B の反例候補を signed five-adic 降下の二つの入口へ振り分ける routing theorem の中心的な算術分岐である。

## 5. 直接依存する定義・補題

リポジトリ固有の直接依存は次である。

- `Fermat5Equation`
- `mod25_fifth_residue_classification` — 0054。`private` な有限分類補題

Mathlib 側では主に次を使う。

- `Fin 25`
- `Nat.mod_lt`
- `congrArg`
- `Nat.add_mod`
- `Nat.pow_mod`
- `Nat.dvd_mod_iff`
- `norm_num`
- `Or.inl`, `Or.inr`
- `rcases`

特に `Nat.dvd_mod_iff` が、自然数と法 $25$ の代表との間で「5 で割れる」を往復させる橋である。

## 6. 証明の流れ

1. `x % 25`, `y % 25`, `z % 25` を値にもつ `xr yr zr : Fin 25` を構成する。
2. `Fermat5Equation` を展開して自然数等式 `x^5 + y^5 = z^5` を取り出す。
3. `congrArg (fun n => n % 25)` により両辺を法 $25$ へ写す。
4. `Nat.add_mod` と `Nat.pow_mod` で、前号の有限分類が期待する形へ正規化する。
5. `5 ∤ x` から `5 ∤ x % 25` を導く。ここでは $5\mid25$ を使った `Nat.dvd_mod_iff` を用いる。
6. `mod25_fifth_residue_classification xr yr zr` に `hEqMod` と `h5xr` を渡し、`5 ∣ y % 25 ∨ 5 ∣ z % 25` を得る。
7. 各枝を再び `Nat.dvd_mod_iff` で自然数へ持ち上げ、`5 ∣ y ∨ 5 ∣ z` を返す。

本質は「自然数 → 法 25 の有限世界 → 自然数」という往復である。

## 7. Lean 固有の処理

### 7.1 `let xr : Fin 25 := ...`

`Fin 25` は値だけでなく $x\bmod25<25$ の証明も必要とする。`Nat.mod_lt _ (by decide)` がその範囲証明を埋める。

### 7.2 `congrArg`

自然数等式そのものから合同式を作るため、等式の両辺へ `% 25` を適用する。

```lean
have h := congrArg (fun n : ℕ => n % 25) hEqNat
```

ここでは専用の合同関係型へ移行せず、自然数の剰余値の等式として扱っている。

### 7.3 `Nat.pow_mod`

前号の命題は `((x % 25)^5 + ...) % 25` という形を期待する。元の等式を単に `% 25` へ写すと `(x^5 + y^5) % 25` なので、`Nat.pow_mod` と `Nat.add_mod` で剰余代表へ押し込む。

### 7.4 `Nat.dvd_mod_iff`

$5\mid25$ のもとでは、

$$
5\mid(n\bmod25)
\quad\Longleftrightarrow\quad
5\mid n
$$

が使える。証明中では同じ橋を三回使う。

### 7.5 `private` 補題の公開ラッパー

0054 は同一ファイル内部だけで使う有限計算実装である。本定理はその詳細を外部へ漏らさず、自然数上の数学的 API として公開する。

## 8. 冗長・重複箇所

`Nat.dvd_mod_iff (by norm_num : 5 ∣ 25)` が、`x` の非整除を下ろす箇所と、`y`,`z` の整除を戻す二箇所で計三回現れる。局所補題、たとえば

```lean
have h5mod : ∀ n : ℕ, 5 ∣ n % 25 ↔ 5 ∣ n := ...
```

を置けば重複を減らせる。

また `xr`, `yr`, `zr` は構造が完全に同じで、単純な `% 25` 射影の三回記述である。局所関数

```lean
let mod25 : ℕ → Fin 25 := fun n => ⟨n % 25, Nat.mod_lt _ (by decide)⟩
```

を置く案もある。ただし現状の三行は読みやすく、抽象化による利益は小さい。

`hEqNat` も `Fermat5Equation` が単なる定義なので理論上は直接展開できるが、自然数等式に名前を与えたことで後段の `congrArg` が読みやすくなっている。

## 9. 最適化候補

1. `Nat.dvd_mod_iff` の三回利用を局所同値 `h5mod` にまとめる。
2. `xr`,`yr`,`zr` を作る局所写像 `mod25 : ℕ → Fin 25` を定義する。
3. `hEqMod` の生成を「Fermat 方程式を法 $25$ へ落とす」専用補題に切り出すと、将来ほかの有限剰余分類でも再利用できる。
4. 数学的透明性を優先するなら、`Nat.ModEq 25` を使う形へ書き換え、合同式としての意図を型に表す案がある。ただし 0054 が剰余値の等式を要求するため、最終的には値等式への変換が必要になる。
5. 0054 の有限分類を手計算可能な剰余クラス補題へ置き換えれば、本定理の証明は計算依存を弱められる。ただしコード量は増える。

## 10. 必要な Mathlib import

対象ブランチの生成済み `Flt5DkMath/FLT5StandAlone.lean` は全体として

```lean
import Mathlib
```

を用いる。

本定理単体で必要な領域は、`Fin`、自然数の剰余・整除・冪、`norm_num`、基本 tactic である。最小化候補としては概ね次の領域が関係する。

```lean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
```

ただし分割元 `DkMath/FLT/Five/SignedBranchA.lean` の正確な import 集合を削減ビルドで検証したわけではないため、これは推測を含む。ファイル単位では前後の `interval_cases`、`norm_num`、有限決定証明も考慮して監査すべきである。

## 11. Comparator challenge 化の可否

適している。

### Challenge 案

同じ定理

```lean
theorem five_dvd_y_or_z_of_fermat5_of_five_not_dvd_x
    {x y z : ℕ} (hEq : Fermat5Equation x y z)
    (h5x : ¬ 5 ∣ x) :
    5 ∣ y ∨ 5 ∣ z
```

を次の二系統で証明する。

- 解法 A: 現行どおり法 $25$ の `Fin 25` へ落とし、有限分類 `decide +kernel` を利用する。
- 解法 B: 第五冪の法 $25$ 剰余を数学的に分類し、`Nat.ModEq` を中心に明示的推論する。

比較項目は、証明時間、生成証明項の大きさ、可読性、数学的説明力、一般化可能性、信頼境界である。

## 12. 根拠と推測の区別

宣言名、完全な型、証明本体、0054 の `mod25_fifth_residue_classification` を直接呼ぶこと、および直後の `signedBranchA_normalForm_of_branchB` が本定理を直接利用することは、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` で確認した。

リポジトリの README には既存解説 PDF として日本語版 `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語版 `docs/pdf/FLT5-main-en-v0-r1.pdf` が列挙されており、対象ブランチ上に両ファイルが存在することも確認した。今回の宣言に対応する PDF の厳密な節・ページ番号までは抽出していないため、PDF に由来する細部を推測で補ってはいない。

Mathlib の最小 import 候補は実ビルドによる削減監査を行っていないため推測である。

## 13. 次に読むべき定理

次は、本定理の二分を使って signed Branch A の正規形を実際に構成する routing theorem である。

```lean
theorem signedBranchA_normalForm_of_branchB
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    SignedBranchANormalForm y x z ∨ SignedBranchANormalForm x y z := by
  ...
```

この定理で 0048、0050、0051、0052、0053、0055 が一つに合流し、次の signed five-adic 層へ渡す正規化入口が完成する。
