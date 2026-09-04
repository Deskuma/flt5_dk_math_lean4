# 0181 — `goldenSqrtFive_sq`

## Lean の型

```lean
theorem goldenSqrtFive_sq :
    goldenMul goldenSqrtFive goldenSqrtFive = goldenOfInt 5 := by
  decide
```

これは `theorem` である。0177 で導入した `goldenSqrtFive : GoldenInt := ⟨-1, 2⟩` が、本当に平方すると整数 `5` になることを明示する。

## 数学的主張または宣言の意味

`GoldenInt` の座標 `⟨a,b⟩` を $a+b\varphi$ と読む。0177 では

```lean
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩
```

と定義されているので、

$$
goldenSqrtFive=-1+2\varphi=2\varphi-1.
$$

黄金比の関係 $\varphi^2=\varphi+1$ から

$$
(2\varphi-1)^2=4\varphi^2-4\varphi+1=4(\varphi+1)-4\varphi+1=5.
$$

したがって theorem は

$$
(2\varphi-1)^2=5
$$

を `GoldenInt` の明示座標モデル上で証明している。右辺の `goldenOfInt 5` は整数 $5$ を黄金整数環へ埋め込んだ元 `⟨5,0⟩` である。

## 証明全体での役割

0177–0180 では ramified element とその短い公開名を整備した。本 theorem から、その元が単なる記号ではなく実際に平方根 $\sqrt5$ と同じ代数的関係を満たすことが確定する。

この直後には

```lean
theorem goldenNorm_sqrtFive : goldenNorm goldenSqrtFive = -5 := by
  norm_num [goldenNorm, goldenSqrtFive]
```

が続き、その後 `goldenTau_eq_phi_mul_sqrtFive`、`goldenNorm_tau`、`golden_tau_mul_conj`、`exists_goldenTau_factor_of_five_dvd` へ進む。したがって 0181 は、五に対する ramification 算術の最初の実質的恒等式である。

## 直接依存する定義・補題

直接依存は次である。

- `GoldenInt`
- 0124 相当の raw multiplication `goldenMul`
- 0162 `goldenOfInt`
- 0177 `goldenSqrtFive`

数学的背景として 0165 `golden_phi_sq` の $\varphi^2=\varphi+1$ と同じ還元則を使っているが、Lean proof term は `goldenMul` の座標定義を閉じた計算として評価するため、0181 自身が 0165 を rewrite しているわけではない。

## 証明または構築の流れ

証明は一行である。

```lean
by
  decide
```

`goldenSqrtFive`、`goldenMul`、`goldenOfInt 5` はすべて具体的な整数座標へ展開でき、命題は有限の決定可能な等式になる。

座標で見ると

```text
goldenSqrtFive = ⟨-1, 2⟩
goldenMul ⟨-1,2⟩ ⟨-1,2⟩ = ⟨5,0⟩
goldenOfInt 5 = ⟨5,0⟩
```

まで計算され、`decide` が equality decision procedure で閉じる。

## Lean 固有の処理

`by decide` は、一般的な ring identity を証明しているのではなく、完全に閉じた concrete term の等式を decidable equality により判定している点が重要である。

代替としては

```lean
ext <;> norm_num [goldenMul, goldenSqrtFive, goldenOfInt]
```

のような座標証明や、標準 notation と `ring` を使う証明も考えられる。ただし今回は Lean build を行わないため、これらの代替 proof がそのまま通るかは未検証である。

## 冗長・重複箇所

数学的には 0165 `golden_phi_sq` から導出できる関係であり、`goldenSqrtFive := 2φ-1` という表現を標準記法で定義していれば、展開後に `golden_phi_sq` を再利用する構成も可能である。

一方、現行実装は `goldenSqrtFive := ⟨-1,2⟩` と座標を直接固定しているので、0181 を閉じた計算として `decide` で証明する方が短い。この重複は「生成関係から導く数学的証明」と「座標モデルを直接検査する実装証明」の二重化とみなせる。

## 最適化候補

1. 現行の `by decide` を維持し、closed coordinate certificate として扱う。
2. `goldenSqrtFive` を `2 * goldenPhi - 1` に近い標準 algebra notation で定義し、0165 `golden_phi_sq` を使って導出する。
3. `golden_mul_eq` を介し、statement 自体を `goldenSqrtFive ^ 2 = 5` に寄せる。
4. raw API theorem と標準 notation theorem の双方を用意し、後者を public theorem とする。
5. quadratic-order 一般論で discriminant / ramified square-root element を抽象化する。

現状の利点は、証明が非常に小さく、座標定義の回帰テストとしても機能する点にある。

## 必要 Mathlib import と import 最適化候補

本 theorem 自体は `decide` と既存の定義群があれば足り、高度な Mathlib theorem を直接使わない。standalone artifact は `import Mathlib` を使用しているが、0181 単独のために Mathlib 全体が必要とは考えにくい。

ただし `GoldenOrder` モジュール全体は整数算術、環構造、`Zsqrtd` など多くの依存を持つ。Lean build を行わないため、正確な最小 import 集合は未検証であり、import 削減は候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次である。

- concrete coordinates + `by decide`
- `ext` + `norm_num`
- 標準 notation + `ring`
- `golden_phi_sq` からの導出
- generic quadratic-order theorem の特殊化

比較軸は proof term の小ささ、定義変更への耐性、数学的説明力、definitional transparency、必要 import、下流 theorem での再利用性である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `GoldenOrder` generated source である。source では `tau` alias の直後に本 theorem が置かれ、その次に `goldenNorm_sqrtFive` が続く。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし 0181 に対応する具体的 PDF ページ・節番号は直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は

```lean
theorem goldenNorm_sqrtFive : goldenNorm goldenSqrtFive = -5 := by
  norm_num [goldenNorm, goldenSqrtFive]
```

である。

0181 が

$$
(2\varphi-1)^2=5
$$

を確定したのに続き、0182 では同じ元のノルムが

$$
N(2\varphi-1)=-5
$$

であることを証明する。ここから norm-five ramification の算術がさらに明示化される。