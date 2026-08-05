# 0036 — `body5_eq_add_pow_sub`

## 宣言

```lean
theorem body5_eq_add_pow_sub (g y : ℕ) :
    Body5 g y = (g + y) ^ 5 - y ^ 5 := by
  symm
  exact add_pow_five_sub_eq_mul_GN5 g y
```

## Lean の型

```lean
body5_eq_add_pow_sub :
  (g y : ℕ) → Body5 g y = (g + y) ^ 5 - y ^ 5
```

任意の自然数 `g`, `y` について、`Body5 g y` が第五冪差 `(g+y)^5-y^5` に等しいことを述べる全称定理です。

## 数学的主張

`Body5` の定義は

$$
Body5(g,y)=g\,GN5(g,y)
$$

です。先行定理

$$
(g+y)^5-y^5=g\,GN5(g,y)
$$

の向きを反転することで、

$$
Body5(g,y)=(g+y)^5-y^5
$$

を得ます。

自然数の減算を含みますが、右辺は常に切り捨てを起こしません。実際、$y\le g+y$ なので $y^5\le(g+y)^5$ です。ただし本証明では、この順序事実を改めて示さず、既に証明済みの `add_pow_five_sub_eq_mul_GN5` をそのまま再利用します。

## 証明全体での役割

前号の `Body5` は単なる名前付き積でした。本定理は、その名前を第五冪差の意味へ接続する最初の semantic bridge です。

後続では $g=z-y$ と置き、

$$
Body5(z-y,y)=z^5-y^5
$$

へ進みます。さらに Fermat 方程式から $z^5-y^5=x^5$ を得ることで、

$$
Body5(z-y,y)=x^5
$$

という完全第五冪 body が構成されます。

したがって本定理は、局所座標 `(g,y)` の多項式的 body と、元の第五冪方程式を接続する二段 bridge の第一段です。

## 直接依存する定義・補題

### `Body5`

```lean
def Body5 (g y : ℕ) : ℕ :=
  g * GN5 g y
```

左辺の意味を与えるローカル定義です。

### `add_pow_five_sub_eq_mul_GN5`

```lean
theorem add_pow_five_sub_eq_mul_GN5 (g y : ℕ) :
    (g + y) ^ 5 - y ^ 5 = g * GN5 g y
```

本証明の唯一の実質的依存です。右辺 `g * GN5 g y` は `Body5 g y` と定義上同じなので、Lean は期待型に合わせて展開できます。

## 証明の流れ

1. ゴールは `Body5 g y = (g+y)^5-y^5`。
2. `symm` で等式を反転し、ゴールを `(g+y)^5-y^5 = Body5 g y` にする。
3. `add_pow_five_sub_eq_mul_GN5 g y` を適用する。
4. `Body5 g y` は定義上 `g * GN5 g y` なので、`exact` が definitional equality により閉じる。

新しい展開計算、`ring`、`omega`、順序証明は不要です。

## Lean 固有の処理

### `symm`

既存補題の向きが今回の公開 API と逆であるため、ゴール側を反転します。

```lean
symm
```

は現在の等式ゴール `a = b` を `b = a` に置き換えます。

### Definitional equality

先行補題の結論は

```lean
(g + y) ^ 5 - y ^ 5 = g * GN5 g y
```

ですが、反転後のゴール右辺は `Body5 g y` です。`Body5` の定義展開により両者は judgmentally equal なので、明示的な `unfold Body5` や `simpa [Body5]` を書かずに `exact` が成功します。

### 自然数減算

`Nat` の減算は切り捨て減算です。しかし、この定理は減算の安全性を直接操作せず、その処理を完了済みの先行補題へ委譲しています。これは証明責務の重複を避ける良い API 利用です。

## 冗長・重複箇所

数学的には `Body5` の定義と `add_pow_five_sub_eq_mul_GN5` の単純な合成であり、新情報はありません。しかし、以下の理由で公開補題として価値があります。

- 後続定理が `Body5` を展開せず第五冪差へ rewrite できる。
- `Body5` の実装を局所化し、利用側を定義の具体形から分離する。
- 等式の向きを後続 proof flow に適した形へ固定する。
- API 名だけで「body は第五冪差」という数学的意味を読める。

したがって、これは除去対象の重複ではなく、意図的な abstraction lemma です。

## 最適化候補

現行証明は二行で十分に短く、性能上の最適化余地はほぼありません。

代替として次の一行も考えられます。

```lean
  simpa [Body5] using (add_pow_five_sub_eq_mul_GN5 g y).symm
```

ただし現行版は `Body5` の明示展開を避け、definitional equality に任せています。抽象境界を保つ点では現行版がより簡潔です。

別案として定理へ `[simp]` 属性を付けることもできますが、`Body5` が常に差へ展開されると、積として扱いたい valuation 証明で逆効果になり得ます。rewrite の方向を制御する現状が安全です。この評価は設計上の提案であり、`simp` セット全体でのビルド検証は行っていません。

## 必要 Mathlib import と import 最適化候補

生成済み standalone source は `import Mathlib` を使用しています。本定理自体が直接必要とするのは、

- 自然数と累乗・減算
- ローカル定義 `Body5`
- ローカル定理 `add_pow_five_sub_eq_mul_GN5`

です。

実際の `BranchB.lean` では、これらを提供するプロジェクト内モジュール import が本質です。本証明は tactic として `symm` と `exact` しか使わないため、追加の algebra tactic import は不要です。最小 import の具体形は Lean ビルドを行っていないため未検証です。

## Comparator challenge 化の可否

初級から中級の Comparator challenge に適しています。

```lean
theorem body5_eq_add_pow_sub_challenge (g y : ℕ) :
    Body5 g y = (g + y) ^ 5 - y ^ 5 := by
  -- 既存の差分解補題を再利用し、等式の向きを合わせる
  sorry
```

比較対象は次の三案です。

1. `symm` と `exact` による現行証明。
2. `.symm` と `simpa [Body5]` による一行証明。
3. `unfold Body5; rw [← add_pow_five_sub_eq_mul_GN5]` のような明示展開版。

評価点は、証明長だけでなく、definitional equality の理解、抽象境界の保持、rewrite 方向の明瞭さです。

## 根拠と推測の区別

宣言型、二行の証明本体、`Body5` の直後に置かれていること、さらに次の宣言が `body5_eq_fifth_power_of_fermat` であることは、リポジトリ内の `Flt5DkMath/FLT5StandAlone.lean` にある生成済み `DkMath/FLT/Five/BranchB.lean` 部分で確認しました。

既存 PDF は FLT5 の第五冪差分解と Branch B の物語的背景を与えますが、本定理の Lean 実装に関する最終根拠はコードです。`[simp]` 属性や最小 import に関する記述は未検証の設計提案です。本作業では Lean ビルドを行っていません。

## 次に読むべき宣言

次はソース直後の

```lean
DkMath.FLT.Five.body5_eq_fifth_power_of_fermat
```

です。

この定理は $g=z-y$ を代入し、順序条件 $y\le z$ を使って、

$$
Body5(z-y,y)=z^5-y^5
$$

を得た後、Fermat 方程式から

$$
Body5(z-y,y)=x^5
$$

へ接続します。今回の一般 gap bridge を、反例候補に直接利用できる第五冪 normal form へ特殊化する第二段です。
