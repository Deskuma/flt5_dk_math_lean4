# 0046 — `CounterexamplePack.swap`

## 1. 対象宣言

```lean
theorem CounterexamplePack.swap
    {x y z : ℕ} (hPack : CounterexamplePack x y z) :
    CounterexamplePack y x z where
  hx := hPack.hy
  hy := hPack.hx
  hz := hPack.hz
  hxy := hPack.hxy.symm
  hEq := by
    simpa [Fermat5Equation, Nat.add_comm] using hPack.hEq
```

完全修飾名は `DkMath.FLT.Five.CounterexamplePack.swap` である。

## 2. Lean の型

任意の自然数 `x y z` に対し、`CounterexamplePack x y z` から `CounterexamplePack y x z` を構成する。

```lean
CounterexamplePack x y z → CounterexamplePack y x z
```

これは `CounterexamplePack` 名前空間に置かれたメソッド形式の定理なので、`hPack.swap` としても利用できる。

## 3. 数学的主張

正の原始的 Fermat 候補

$$
x^5+y^5=z^5,\qquad \gcd(x,y)=1
$$

において、左辺の二項を交換しても、

$$
y^5+x^5=z^5,\qquad \gcd(y,x)=1
$$

が成り立つ。したがって反例候補のパケットは交換対称性を持つ。

## 4. 証明全体での役割

後続の signed Branch A では、五で割り切れる対象が差 `z-y` 側に現れる場合と、左右を交換した差 `z-x` 側に現れる場合を同じ機構へ送る必要がある。本定理は左辺の対称性を Lean 上の構造体変換として明示し、一方向に書かれた補題を他方向へ再利用するための bridge となる。

新しい数論的内容を加えるのではなく、Fermat 方程式と原始性の対称性を API として固定する宣言である。

## 5. 直接依存する定義・補題

- `CounterexamplePack`：正値、互いに素性、Fermat 方程式を保持する構造体。
- `Fermat5Equation`：`x ^ 5 + y ^ 5 = z ^ 5`。
- `Nat.Coprime.symm`：`Coprime x y` から `Coprime y x` を得る。
- `Nat.add_comm`：Fermat 方程式の左辺を交換する。
- `simpa`：定義展開と可換則による式の正規化をまとめる。

## 6. 証明の流れ

1. `where` 構文で交換後の `CounterexamplePack y x z` を直接構築する。
2. 新しい `hx` には元の `hy`、新しい `hy` には元の `hx` を入れる。
3. `z` は変化しないため `hz` をそのまま再利用する。
4. 互いに素性は `hPack.hxy.symm` で向きを反転する。
5. 方程式は `Fermat5Equation` を展開し、`Nat.add_comm` で左辺を交換して `hPack.hEq` を再利用する。

## 7. Lean 固有の処理

### 構造体の named-field construction

`where` 以下で各フィールドを名前付きで埋めているため、`CounterexamplePack` のフィールド順序に依存しない。長期保守では positional constructor より安全である。

### namespace method

宣言名が `CounterexamplePack.swap` なので、型が一致する値 `hPack` に対して `hPack.swap` とドット記法で適用できる。

### `simpa` による定義展開

`hPack.hEq` の型は `Fermat5Equation x y z` であり、目標は `Fermat5Equation y x z` である。両者を展開すると差は加法の順序だけなので、`simpa [Fermat5Equation, Nat.add_comm]` で閉じる。

## 8. 冗長・重複箇所

数学的には加法と互いに素性の対称性を構造体へ持ち上げただけであり、論理内容は小さい。しかし、後続で毎回フィールドを並べ直す重複を除き、signed 分岐の対称処理を明瞭にするため、独立定理としての価値が高い。

`hz := hPack.hz` は恒等的な再掲だが、構造体構築には必要である。

## 9. 最適化候補

現在の証明は短く、named-field construction も安定しているため、実質的な最適化は不要である。代案として方程式部分を

```lean
  hEq := by
    unfold Fermat5Equation at hPack ⊢
    simpa [Nat.add_comm] using hPack.hEq
```

のように書くことも考えられるが、構造体仮定全体を `unfold` 対象にする必要はなく、現行の局所的な `simpa` の方が明快である。

対称性 API をさらに整えるなら、交換を二回行うと元へ戻る補題

```lean
(hPack.swap).swap = hPack
```

を検討できる。ただし `Prop` 値の等式は証明無関連性により容易であり、実際の数学的経路では通常不要である。

## 10. 必要な Mathlib import と import 最適化候補

生成済み standalone ファイルは `import Mathlib` を用いる。宣言単体が必要とする機能は、自然数、累乗、`Nat.Coprime`、構造体、`simpa`、加法可換則に限られる。

正確な最小 import は、この実行では元の分割モジュールを直接取得できなかったため未確定である。少なくとも `CounterexamplePack` と `Fermat5Equation` を定義する先行モジュールを import すれば、追加の広い Mathlib import は不要である可能性が高い。これは import 監査時に Lean ビルドで確認すべき推測である。

## 11. Comparator challenge 化

適している。課題は次の形にできる。

> `CounterexamplePack x y z` から、左辺を交換した `CounterexamplePack y x z` を構築せよ。方程式の交換には加法可換則を使い、構造体の全フィールドを明示的に埋めること。

比較観点は、

- named-field construction を用いるか
- `Nat.Coprime.symm` を正しく選べるか
- `Fermat5Equation` の展開範囲を必要最小限に保てるか
- `simpa [Nat.add_comm]` で方程式を再利用できるか

である。短いが、構造体再梱包と definitional unfolding の基礎を測れる良い challenge となる。

## 12. 根拠と留保

宣言の型と証明本体は、対象ブランチの生成済み `Flt5DkMath/FLT5StandAlone.lean` から確認した。そこでは `SignedBranchA.lean` 相当部分の冒頭に置かれている。

既存 PDF の物語的説明は補助資料であり、本稿では取得できた Lean 宣言を最終根拠とした。分割元ファイルの正確な import 行は対象リポジトリ内で直接取得できなかったため、import 最小化に関する記述は明示的に推測として扱った。

## 13. 次に読むべき定理

次は `DkMath.FLT.Five.five_not_dvd_GN5_of_five_not_dvd_gap` を読む。

これは gap が五で割れないとき、五進分解

$$
GN5(g,y)=g^4+5K
$$

を用いて `GN5 g y` も五で割れないことを示し、signed Branch A の mod-5／mod-25 ルーティングを支える補題である。
