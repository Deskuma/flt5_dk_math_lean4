# 0029 — `branchB_false_of_GN5_not_fifth_power`

## 宣言

```lean
theorem branchB_false_of_GN5_not_fifth_power
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y)
    (hGN : ¬ ∃ b : ℕ, GN5 (z - y) y = b ^ 5) :
    False := by
  exact hGN (branchB_fifth_power_factor_split hPack hBranch).2
```

## Lean の型

この定理は、正の原始的な FLT5 反例候補、Branch B 条件、そして対応する `GN5` が完全第五冪ではないという外部証明を受け取り、矛盾 `False` を返す。

```lean
CounterexamplePack x y z →
  (¬ 5 ∣ z - y) →
  (¬ ∃ b : ℕ, GN5 (z - y) y = b ^ 5) →
  False
```

第三引数 `hGN` は、この定理の内部で新たに証明される算術事実ではない。Branch B の前段が強制する完全第五冪性と衝突させるための receiver input である。

## 数学的主張

`CounterexamplePack x y z` と Branch B 条件

$$
5\nmid z-y
$$

が成立すると、前号 `branchB_fifth_power_factor_split` により、ある $b\in\mathbb N$ が存在して

$$
GN5(z-y,y)=b^5
$$

となる。

一方、仮定 `hGN` は

$$
\neg\exists b\in\mathbb N,
\quad GN5(z-y,y)=b^5
$$

である。したがって同じ存在命題が肯定と否定の両方から得られ、矛盾する。

## 証明全体での役割

本定理は Branch B の **最終消費インターフェース** である。

Reduction 層はここまでに、反例方程式を gap と `GN5` の積へ変換し、Branch B では二因子が互いに素であることを示し、それぞれを第五冪へ分離した。本定理は、その長い算術経路の最終出力である

```lean
∃ b : ℕ, GN5 (z - y) y = b ^ 5
```

だけを取り出し、別の provider が供給する非第五冪証明へ渡す。

したがって、本定理自体は `GN5` の非第五冪性を確立しない。後続の具体的 provider、valuation 障害、あるいはより強い正規形・降下法が `hGN` を供給すれば、Branch B はこの一行で閉じる。

## 直接依存する定義・補題

1. `CounterexamplePack`
   - 正値性、原始性、FLT5 方程式を束ねる入力構造体。
2. `GN5`
   - 第五冪差から gap を取り除いた斉次次数4の残余核。
3. `branchB_fifth_power_factor_split`
   - `hPack` と `hBranch` から、gap と `GN5` が個別に完全第五冪であることを返す。
4. 連言の第二射影 `.2`
   - 前号の返値から `GN5` 側の存在証明だけを選び出す。
5. 関数適用による否定の消費
   - Lean では `¬ P` は `P → False` なので、`hGN` に存在証明を適用すれば `False` になる。

## 証明の流れ

1. `branchB_fifth_power_factor_split hPack hBranch` を適用する。
2. その結論は次の連言である。

```lean
(∃ a : ℕ, z - y = a ^ 5) ∧
  (∃ b : ℕ, GN5 (z - y) y = b ^ 5)
```

3. `.2` により第二成分を取得する。

```lean
(branchB_fifth_power_factor_split hPack hBranch).2
```

4. 取得した存在証明を、否定命題 `hGN` に適用する。

```lean
hGN (branchB_fifth_power_factor_split hPack hBranch).2
```

5. `hGN` の返値は `False` なので、目標が閉じる。

## Lean 固有の処理

### 否定は関数型

Lean では

```lean
¬ P
```

は定義上

```lean
P → False
```

である。したがって、`hGN` は「非存在性を記述するデータ」であると同時に、存在証明を受け取ると矛盾を返す関数として直接利用できる。

### 連言射影 `.2`

前号は gap 側と `GN5` 側の二つの存在証明を連言で返す。本定理が必要とするのは後者だけなので、パターン分解せず `.2` を使っている。

```lean
(branchB_fifth_power_factor_split hPack hBranch).2
```

これは `rcases` で両成分へ名前を付けるより短く、未使用の gap 側証明を導入しない。

### 暗黙引数推論

`branchB_fifth_power_factor_split` の暗黙変数 `x y z` は、`hPack` と `hBranch` の型から推論される。`hGN` の対象も同じ `z-y` と `y` なので、rewrite や `simpa` は不要である。

### term proof

証明全体は tactic state を変形する必要がなく、一つの項として完全に記述できる。依存関係が型にそのまま現れるため、この形は非常に透明である。

## 冗長・重複箇所

本定理には算術計算、多項式展開、素因数反証の重複はない。前号の第二成分を否定仮定へ渡すだけの薄い consumer theorem である。

同じパターンが他の branch や指数で繰り返される場合、一般形

```lean
(P ∧ Q) → ¬ Q → False
```

へ抽象化すること自体は可能である。しかし、これは命題論理として自明であり、専用補題を増やすと FLT5 に固有の意味が見えにくくなる。現在の名前付き定理は、Branch B の閉じ方を公開 API として明示する役割があるため、残す価値が高い。

## 最適化候補

1. 現行の一行 proof はすでに最小に近く、実質的な短縮余地はない。
2. 読みやすさを優先するなら、次のように中間事実へ名前を付けられる。

```lean
have hPow : ∃ b : ℕ, GN5 (z - y) y = b ^ 5 :=
  (branchB_fifth_power_factor_split hPack hBranch).2
exact hGN hPow
```

3. ただし現行形の方が provider-to-consumer 接続を直接示す。
4. 将来 `branchB_fifth_power_factor_split` の返値が構造体へ変更された場合は、`.2` を意味付きフィールド名へ置き換えると保守性が上がる。
5. `False` ではなく `¬ CounterexamplePack x y z` の形を公開 API にする案もあるが、Branch B 条件と `hGN` が別引数なので、現在の contradiction consumer の方が合成しやすい。

## 必要 Mathlib import と import 最適化候補

standalone 生成物は `import Mathlib` を使用しているが、本定理単独が直接使う Mathlib 機能は極めて少ない。

必要なのは主に次である。

1. 命題論理の `False`、否定、存在、連言。
2. 自然数、冪、整除性の記法。
3. リポジトリ内の `CounterexamplePack`、`GN5`、`branchB_fifth_power_factor_split`。

算術的な重い依存はすべて前号へ隠蔽されている。実際の `Reduction.lean` を分割しない限り、推移的 import が大半を供給する。最小 Mathlib import の正確なモジュール名は Lean ビルドを行っていないため未検証である。

## Comparator challenge 化の可否

小規模な challenge として適している。難しさは算術ではなく、前号の返値から必要な成分を正しく取り出し、否定を関数として消費できるかにある。

### 課題案

```lean
{x y z : ℕ}
(hPack : CounterexamplePack x y z)
(hBranch : ¬ 5 ∣ z - y)
(hGN : ¬ ∃ b : ℕ, GN5 (z - y) y = b ^ 5)
⊢ False
```

比較候補は次の通り。

1. 現行の一行 term proof。
2. `have` で `GN5` の第五冪性を取り出す二段 proof。
3. `rcases branchB_fifth_power_factor_split ... with ⟨ha, hb⟩` と分解する版。
4. `exact hGN ...` ではなく `contradiction` や `aesop` に任せる版。

評価軸は、依存の明瞭さ、不要な事実を導入しないこと、自動化への依存度、変更耐性である。現行版は最短であるだけでなく、論理構造も最も直接的である。

## 根拠と推測の区別

宣言の型、証明本体、`branchB_fifth_power_factor_split` の第二成分を `hGN` に渡す構造、そして本定理が `Reduction.lean` の最後の宣言であることは、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` で確認した。

本定理を Branch B の最終消費インターフェースと呼ぶ説明は、ソースコメントとモジュール境界に基づく解釈である。最小 import、返値の構造体化、一般論理補題との比較は未検証提案である。既存 PDF は補助資料として扱い、Lean ソースを最終根拠とする。

## 次に読むべき定理

```lean
DkMath.FLT.Five.coprime_GN5_y_of_coprime
```

これは次の `NormalForm.lean` の最初の定理であり、

$$
\gcd(g,y)=1
$$

から

$$
\gcd(GN5(g,y),y)=1
$$

を導く。Reduction 層で得た gap 座標の原始性を `GN5` 側へ転送し、後続の elementary Branch-B normal form が保持すべき互いに素性を準備する。
