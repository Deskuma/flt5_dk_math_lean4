# 0160 — `golden_pow_eq`

## Lean の型

```lean
@[simp] theorem golden_pow_eq (x : GoldenInt) (n : ℕ) :
    goldenPow x n = x ^ n := rfl
```

これは theorem であり、raw operation `goldenPow` と `CommRing GoldenInt` が提供する標準冪 `x ^ n` が定義的に一致することを公開する `@[simp]` bridge である。

## 数学的主張または宣言の意味

`goldenPow` は黄金整数上の自然数冪を明示的に再帰定義している。

```lean
def goldenPow (x : GoldenInt) : ℕ → GoldenInt
  | 0 => goldenOne
  | n + 1 => goldenMul (goldenPow x n) x
```

したがって数学的には

$$
goldenPow(x,0)=1,
$$

$$
goldenPow(x,n+1)=goldenPow(x,n)\,x
$$

である。一方、`goldenCommRing : CommRing GoldenInt` の構築時には

```lean
npow := fun n x => goldenPow x n
```

と登録されているため、標準記法 `x ^ n` の自然数冪そのものが `goldenPow x n` である。本 theorem は新しい冪法則を証明するのではなく、この同一性を名前付き API として外部へ公開する。

## 証明全体での役割

0156–0160 は raw operation を Mathlib 標準 notation へ正規化する bridge block である。

```text
goldenAdd x y  →  x + y
goldenNeg x    →  -x
goldenSub x y  →  x - y
goldenMul x y  →  x * y
goldenPow x n  →  x ^ n
```

0160 はこの block の最後に位置する。ここまでで `GoldenOrder` の bootstrap 用 raw API を、後続の環論・整除・単元・第五冪分解では通常の algebra notation と混在させずに扱える。

実際、後続 source では `golden_pow_eq` が第五冪因子分解、単元 sector の整理、ノルムと冪の関係などで明示的に rewrite 集合へ含められている。したがって単なる cosmetic lemma ではなく、raw API から標準環 API へ証明を移すための安定した rewrite contract である。

## 直接依存する定義・補題

直接の依存は次の通りである。

- `GoldenInt`
- `goldenPow`
- `goldenOne`
- `goldenMul`
- `goldenCommRing : CommRing GoldenInt`
- 標準冪記法 `HPow.hPow` / `Pow.pow` を提供する Mathlib の algebra hierarchy

特に重要なのは `goldenCommRing` の `npow` field が `goldenPow` そのものに設定されている点である。この設計により theorem は補題を使わず `rfl` で閉じる。

## 証明または構築の流れ

証明は

```lean
:= rfl
```

だけである。

Lean が右辺 `x ^ n` を `CommRing GoldenInt` の自然数冪へ展開すると、その実装は `goldenPow x n` である。したがって左右は definitional equality になり、帰納法も `simp` も不要である。

この theorem で数学的に重要なのは証明の長さではなく、`CommRing` 構築時に raw recursion と標準冪を同一実装へ揃えておいた設計そのものである。

## Lean 固有の処理

`^` は単なる構文糖ではなく typeclass / algebra structure を経由して解決される。`goldenCommRing` では

```lean
npow := fun n x => goldenPow x n
npow_zero := by intro x; rfl
npow_succ := by
  intro n x
  change goldenPow x (n + 1) = goldenMul (goldenPow x n) x
  rfl
```

と構築されている。つまり標準冪の zero / successor law も raw recursion と同じ定義形に合わせてある。

`@[simp]` を付けることで、proof state に `goldenPow x n` が現れた場合、simp は標準形 `x ^ n` へ寄せる。後続の `mul_pow`、`pow_mul`、ノルムの冪補題など Mathlib 標準 theorem を使う際に有利である。

## 冗長・重複箇所

`goldenPow` と `x ^ n` は `goldenCommRing` 構築後には同じ演算なので、API としては二重に見える。しかし raw `goldenPow` は `CommRing GoldenInt` を作る前に自然数冪を定義する bootstrap operation であり、標準 `^` は完成した algebra structure の外部 interface である。

そのため重複は偶発的ではなく、構造構築前後の層を分離するための意図的な二層構成である。

## 最適化候補

1. `goldenPow` を削除し、`CommRing` 構築時に一般的な recursive `npow` を直接記述する。
2. 現行方式を維持し、raw operation と標準 notation の境界を `golden_pow_eq` で明示する。
3. raw operation 群全体を private に寄せ、bridge theorem 以降は標準 algebra API のみを公開する。
4. `golden_add_eq` から `golden_pow_eq` までの bridge 群を統一的な API section として整理し、downstream の `simp only` rewrite 集合を監査しやすくする。

FLT5 の formal proof を監査可能に保つ目的では、現行の explicit bootstrap は有利である。特に第五冪を raw recursion の段階から追跡できる点は、抽象化し過ぎるより説明性が高い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自体が必要とするのは、`GoldenInt` とその `CommRing` instance、自然数冪 notation、`simp` attribute infrastructure 程度である。

したがって 0160 単独のために `Mathlib` 全体を必要とするとは考えにくい。ただし実際の `GoldenOrder` module は `ring`、`omega`、`Zsqrtd` など複数の機能を使用している。Lean build を行わない今回の作業では最小 import 集合は検証していないため、import 削減は候補としてのみ記録する。

## Comparator challenge 化の可否

適している。例えば次の三方式を比較できる。

- 現行: explicit `goldenPow` を `npow` に登録し `golden_pow_eq` を `rfl` で公開する。
- `CommRing` 側で自然数冪を直接定義し raw `goldenPow` を持たない。
- より一般的な quadratic-order abstraction の標準 `Pow` を最初から使用する。

評価軸は、`rfl` で閉じる補題数、第五冪 theorem の rewrite 数、simp の正規形、bootstrap dependency の明瞭さ、一般化可能性、後続 source の可読性である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる generated `DkMath/FLT/Five/GoldenOrder.lean` section である。そこでは `golden_mul_eq` の直後に本 theorem があり、その次に basis element `goldenPhi` の定義が続く。

対象ブランチには日本語・英語 PDF も存在するが、この小さな raw/standard API bridge theorem に対応する具体的ページは今回直接特定していない。したがって PDF ページ番号は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
/-- The basis element `phi`. -/
def goldenPhi : GoldenInt := ⟨0, 1⟩
```

である。

0160 で raw operation bridge block が完結し、次からは黄金整数環固有の基底元 $\varphi$ と、その後の共役・ノルムへ進む。`goldenPhi = 0 + 1\varphi` を明示することで、抽象的な `CommRing GoldenInt` に黄金比由来の算術的内容が再び投入される。
