# 0178 — `goldenTau`

## Lean の型

```lean
/-- The distinguished ramifier `2 + phi`. -/
def goldenTau : GoldenInt := ⟨2, 1⟩
```

これは `theorem` ではなく `def` であり、黄金整数環 `GoldenInt` の具体的な元

$$
2+\varphi
$$

を `goldenTau` という名前で定義する。

## 数学的主張または宣言の意味

`GoldenInt` の座標 `⟨a,b⟩` は $a+b\varphi$ を表すので、

```lean
def goldenTau : GoldenInt := ⟨2, 1⟩
```

はそのまま

$$
\tau=2+\varphi
$$

を表す。ここで $\varphi=(1+\sqrt5)/2$ と読めば、0177 の

$$
\sqrt5=2\varphi-1
$$

と組み合わせて、後続では

$$
\tau=\varphi\sqrt5
$$

が成り立つ。実際 source には

```lean
theorem goldenTau_eq_phi_mul_sqrtFive :
    goldenTau = goldenMul goldenPhi goldenSqrtFive := by
  decide
```

が置かれている。

さらに

```lean
theorem goldenNorm_tau : goldenNorm goldenTau = 5 := by
  norm_num [goldenNorm, goldenTau]
```

により

$$
N(\tau)=5
$$

となる。このため `goldenTau` は、素数 $5$ の ramification を黄金整数環の内部で担う distinguished norm-five element である。

## 証明全体での役割

0177 `goldenSqrtFive` が $2\varphi-1$ に対応する平方根側の ramified element を固定したのに対し、0178 `goldenTau` はその element に unit $\varphi$ を掛けた norm-five representative を固定する。

source では本定義の直後に

```lean
abbrev sqrtFiveElement : GoldenInt := goldenSqrtFive
abbrev tau : GoldenInt := goldenTau
```

という public alias が続き、その後

- `goldenSqrtFive_sq`
- `goldenNorm_sqrtFive`
- `goldenTau_eq_phi_mul_sqrtFive`
- `goldenNorm_tau`
- `golden_tau_mul_conj`
- `exists_goldenTau_factor_of_five_dvd`

へ進む。

特に `exists_goldenTau_factor_of_five_dvd` は、整数座標 $M,N$ に対する $5\mid 2M+N$ から、対応する `GoldenInt` が `goldenTau` を因子として持つことを具体的に抽出する。したがって `goldenTau` は FLT5 exceptional branch において、単なる名前付き元ではなく「5 の可視 ramified factor」を担う実用的な因子である。

## 直接依存する定義・補題

定義本体が syntactic に直接依存するものは少ない。

- `GoldenInt`
- 整数 literal `2`, `1`

数学的意味付けでは、上流の

- 0161 `goldenPhi`
- 0164 `goldenNorm`
- 0177 `goldenSqrtFive`

と密接に関係する。ただし `goldenTau` 自体はそれらを式として呼び出さず、還元済み座標 `⟨2,1⟩` を直接採用している。

## 証明または構築の流れ

proof script は存在しない。

```lean
def goldenTau : GoldenInt := ⟨2, 1⟩
```

という structure literal だけで構築される。

概念的には、

1. distinguished ramifier を $\tau=2+\varphi$ と選ぶ。
2. 基底 $1,\varphi$ に対する係数 $2,1$ を読む。
3. その係数を `GoldenInt` の二座標へ直接格納する。

という一段の座標化である。

## Lean 固有の処理

期待型が `GoldenInt` なので、`⟨2,1⟩` は structure constructor として elaboration され、両 literal は `ℤ` として解釈される。

`goldenPhi * goldenSqrtFive` のような algebraic expression ではなく coordinate literal を直接採用しているため、後続の `goldenNorm_tau` や `goldenTau_eq_phi_mul_sqrtFive` は閉じた整数座標計算へ落ちる。実際、前者は `norm_num`、後者は `decide` で閉じられている。

本定義には `@[simp]` は付いていない。`goldenTau` は正規化 rule ではなく、後続証明で参照される distinguished element だからである。

## 冗長・重複箇所

直後に

```lean
abbrev tau : GoldenInt := goldenTau
```

が置かれるため、`goldenTau` と `tau` は値として同一であり、API-level の alias 重複がある。

また数学的には

$$
\tau=\varphi\sqrt5
$$

であるため、coordinate literal `⟨2,1⟩` と algebraic expression `goldenMul goldenPhi goldenSqrtFive` の二つの表現が並存する。現行 source は計算透明性を優先して座標定義を正本としている。

## 最適化候補

1. 現行の `⟨2,1⟩` を維持し、closed computation の簡潔さを優先する。
2. `goldenTau` を `goldenMul goldenPhi goldenSqrtFive` から定義し、数学的由来を定義式へ直接埋め込む。
3. 現行定義を維持しつつ、既存 theorem `goldenTau_eq_phi_mul_sqrtFive` を標準 notation 版へ寄せる。
4. `tau` alias の downstream 使用状況を監査し、公開 API 名を一本化できるか検討する。
5. 一般 quadratic order における ramified prime representative として抽象化し、discriminant $5$ を特殊化する。

局所的には一行定義なので、最適化対象は proof 長ではなく API naming、数学的由来の可視性、一般化可能性である。

## 必要 Mathlib import と import 最適化候補

本 `def` 単独なら `GoldenInt` と基本的な整数 literal の環境だけで足り、高度な Mathlib theorem や tactic は直接使わない。

standalone artifact は `import Mathlib` を使用しているが、`GoldenOrder` module 全体では `Zsqrtd`、`ring`、`omega`、`norm_num`、`interval_cases`、algebra typeclass 群を使う。したがって import 最適化は本宣言単独ではなく module 単位で評価すべきである。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、具体的な削減先は候補としてのみ扱う。

## Comparator challenge 化の可否

適している。

比較候補は、

- explicit coordinate `⟨2,1⟩`
- `goldenMul goldenPhi goldenSqrtFive`
- 標準 notation `goldenPhi * goldenSqrtFive`
- generic quadratic-order / `AdjoinRoot` 上の ramified element

である。

比較軸は、`goldenNorm_tau` や factor extraction theorem の proof burden、definitional transparency、数学的由来の読みやすさ、`simp` / `norm_num` / `decide` との相性、一般化可能性である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `GoldenOrder` generated source である。source 上では 0177 `goldenSqrtFive` の直後に本定義があり、その次に `sqrtFiveElement` alias が続く。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、本定義に対応する具体的 PDF ページ・節番号は直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は

```lean
/-- Short public name for the element `2φ-1`, whose square is five. -/
abbrev sqrtFiveElement : GoldenInt := goldenSqrtFive
```

である。

0177–0178 で ramified element の内部名 `goldenSqrtFive` と `goldenTau` が揃った。次からは downstream で扱いやすい短い public alias を導入し、その後に平方・ノルム・因子抽出の theorem 群へ進む。