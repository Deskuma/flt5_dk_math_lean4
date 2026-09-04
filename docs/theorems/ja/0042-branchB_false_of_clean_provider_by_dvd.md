# 0042 — `branchB_false_of_clean_provider_by_dvd`

## 1. 宣言

```lean
theorem branchB_false_of_clean_provider_by_dvd
    (hProvider : BranchBCleanGN5ChannelProvider)
    {x y z : ℕ}
    (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  rcases hProvider hPack hBranch with ⟨q, hClean⟩
  exact counterexample_false_of_clean_GN5Channel_by_dvd hPack hClean
```

本定理は `DkMath.FLT.Five` 名前空間に属し、`Provider.lean` に置かれている。

## 2. Lean の型

入力は三つである。

- `hProvider : BranchBCleanGN5ChannelProvider`
- `hPack : CounterexamplePack x y z`
- `hBranch : ¬ 5 ∣ z - y`

出力は `False` である。したがって本定理は、clean-channel provider を仮定した条件付き Branch B refuter である。

`x`、`y`、`z` は暗黙引数であり、`hPack` と `hBranch` の型から推論される。

## 3. 数学的主張

`CounterexamplePack x y z` は、正の原始的な Fermat 第五冪方程式候補

$$
x^5+y^5=z^5
$$

を表す。Branch B 条件は、gap $g=z-y$ に対して

$$
5\nmid g
$$

である。

provider は、この候補と Branch B 条件から、ある自然数 $q$ と clean channel

$$
CleanGN5Channel(g,y,q)
$$

を供給する。clean channel は概念的には、$q$ が素数であり、

$$
q\mid GN5(g,y),\qquad q\nmid g,
$$

かつ

$$
q^2\nmid GN5(g,y)
$$

であることを記録する。

一方、Fermat 方程式は full body を完全第五冪にする。

$$
Body5(g,y)=g\,GN5(g,y)=x^5
$$

clean channel はこの full body が完全第五冪であることを排除するため、矛盾が生じる。

## 4. 証明全体での役割

本定理は provider API と局所整除 refuter の間に位置する consumer である。

```text
BranchBCleanGN5ChannelProvider
              ↓ existential witness q
CleanGN5Channel (z - y) y q
              ↓
counterexample_false_of_clean_GN5Channel_by_dvd
              ↓
False
```

ここでは新しい数論的事実を証明しない。素数供給問題を `hProvider` に委譲し、既に完成している局所矛盾へ接続する。

この分離により、provider の構成方法を変更しても局所 refuter は不変であり、逆に局所 valuation 証明を改良しても provider interface は維持できる。

## 5. 直接依存する定義・補題

### `BranchBCleanGN5ChannelProvider`

任意の Branch B 反例候補に対し、clean channel の存在を返す bundled provider interface である。

### `CounterexamplePack`

正値性、原始性、および Fermat 第五冪方程式をまとめた反例候補構造体である。

### `CleanGN5Channel`

局所 valuation がちょうど一となる素数チャネルを束ねる構造体である。

### `counterexample_false_of_clean_GN5Channel_by_dvd`

具体的な clean channel が一つ与えられれば、Fermat 方程式が強制する完全第五冪 body と square-divisibility obstruction を衝突させて `False` を返す既刊 0038 の局所 refuter である。

## 6. 証明の流れ

### 6.1 provider の適用

```lean
hProvider hPack hBranch
```

により、次の存在命題を得る。

```lean
∃ q : ℕ, CleanGN5Channel (z - y) y q
```

### 6.2 存在証人の分解

```lean
rcases hProvider hPack hBranch with ⟨q, hClean⟩
```

により、素数候補 `q` と、その clean-channel 証明 `hClean` を局所コンテキストへ導入する。

### 6.3 局所 refuter の適用

```lean
exact counterexample_false_of_clean_GN5Channel_by_dvd hPack hClean
```

で証明を閉じる。`hBranch` は局所 refuter へ直接渡されない。Branch B 条件は provider が clean channel を生成する段階で消費済みだからである。

## 7. Lean 固有の処理

### 暗黙引数の推論

`counterexample_false_of_clean_GN5Channel_by_dvd hPack hClean` の `x`、`y`、`z`、`q` は、引数の型から Lean が推論する。

### `abbrev` の透過展開

`BranchBCleanGN5ChannelProvider` は `Prop` の略称である。Lean は関数適用時に透過的に展開するため、`unfold BranchBCleanGN5ChannelProvider at hProvider` は不要である。

### `rcases` による存在除去

`rcases ... with ⟨q, hClean⟩` は `Exists` の witness と証明を同時に取り出す。ここでは構造体 `CleanGN5Channel` の内部フィールドまでは分解せず、bundled object のまま次の定理へ渡している。

### `False` の直接構成

ゴールが `False` なので、局所 refuter が返す `False` を `exact` でそのまま利用できる。

## 8. 冗長・重複箇所

証明は二行であり、論理的冗長性はほぼない。

ただし、次の一行形も同値である。

```lean
  obtain ⟨q, hClean⟩ := hProvider hPack hBranch
  exact counterexample_false_of_clean_GN5Channel_by_dvd hPack hClean
```

これは短縮ではなく文体差にすぎない。

`q` は後続行で名前として明示使用されないが、`hClean` の型に現れるため、存在証人を保持する必要がある。匿名化による実質的な簡略化は小さい。

## 9. 最適化候補

現行証明は十分に最小である。最適化よりも API 境界の可読性を維持する方が重要である。

一行の term proof へ圧縮することも可能だが、存在除去が見えにくくなるため推奨しない。

```lean
by
  rcases hProvider hPack hBranch with ⟨q, hClean⟩
  exact counterexample_false_of_clean_GN5Channel_by_dvd hPack hClean
```

は provider、witness、consumer の三役を最も明瞭に示している。

将来、局所 refuter を clean channel 自体のメソッド風 API に再配置する場合でも、本定理の構造は変わらない。

## 10. 必要 Mathlib import と import 最適化候補

生成済み standalone ソース全体は `import Mathlib` を使用しているが、本定理自身が直接利用する機能は次に限られる。

- 自然数 `ℕ`
- 整除記法 `∣`
- 存在型 `Exists`
- `rcases` tactic
- 先行する FLT5 定義・定理

実際のモジュール境界では `Provider.lean` が直前の FLT5 モジュール、少なくとも provider interface と `counterexample_false_of_clean_GN5Channel_by_dvd` を公開する `BranchB.lean` 相当を import すれば足りると考えられる。

ただし、個別 Mathlib import の厳密な最小集合は本記事作成時に Lean ビルドで検証していない。したがって、次は最適化候補であって確認済み変更ではない。

- umbrella import `Mathlib` を避ける。
- FLT5 内部モジュールの推移的 import に依存しすぎない。
- `rcases` を利用する tactic import が既に上位モジュールから供給されるか、`lake env lean` と import lint で監査する。

## 11. Comparator challenge 化の可否

適している。ただし数学発見型ではなく API 配線型 challenge である。

### challenge 例

次を仮定する。

```lean
hProvider : BranchBCleanGN5ChannelProvider
hPack : CounterexamplePack x y z
hBranch : ¬ 5 ∣ z - y
```

目標は `False` を証明することである。

制約として、

- `BranchBCleanGN5ChannelProvider` を手動展開しない。
- `CleanGN5Channel` の各フィールドを分解しない。
- `counterexample_false_of_clean_GN5Channel_by_dvd` を再証明しない。

とすれば、存在 provider と bundled consumer を最短で接続できるかを比較できる。

評価軸は、

- witness の適切な除去
- bundled abstraction の保持
-不要な `unfold` やフィールド分解の回避
- 依存の明瞭さ

である。

## 12. 根拠と監査上の留保

宣言名、型、証明本体、ソース内コメント、および直後の宣言は、リポジトリ内の生成済み `Flt5DkMath/FLT5StandAlone.lean` で確認した。

日本語・英語 PDF は証明全体の叙述的背景資料であるが、本記事の形式的主張は Lean ソースを優先する。

import 最小化案は未ビルドの提案であり、確認済み事実ではない。

## 13. 次に読むべき定理

次は

```lean
DkMath.FLT.Five.branchB_false_of_noLiftEscape_by_dvd
```

を読む。

この定理は `BranchBNoLiftEscape` を前号 0041 の adapter で bundled provider に変換し、本号の consumer へ渡す。すなわち、unbundled no-lift kernel から Branch B の矛盾までを一段で閉じる合成定理である。
