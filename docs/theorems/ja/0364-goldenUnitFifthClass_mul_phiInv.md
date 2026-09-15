# 0364 — `goldenUnitFifthClass_mul_phiInv`

## 宣言種別

この宣言は **`theorem`** である。

```lean
theorem goldenUnitFifthClass_mul_phiInv {x : GoldenInt}
    (hx : GoldenUnitFifthClass x) :
    GoldenUnitFifthClass (goldenMul x goldenPhiInv) := by
  rcases hx with ⟨i, delta, hx⟩
  fin_cases i
  · refine ⟨⟨4, by decide⟩, goldenMul goldenPhiInv delta, ?_⟩
    rw [hx]
    simpa only [golden_mul_eq, golden_pow_eq] using
      golden_sector_zero_mul_phiInv delta
  · refine ⟨⟨0, by decide⟩, delta, ?_⟩
    rw [hx]
    simpa only [golden_mul_eq, golden_pow_eq] using
      golden_sector_succ_mul_phiInv delta 0
  · refine ⟨⟨1, by decide⟩, delta, ?_⟩
    rw [hx]
    simpa only [golden_mul_eq, golden_pow_eq] using
      golden_sector_succ_mul_phiInv delta 1
  · refine ⟨⟨2, by decide⟩, delta, ?_⟩
    rw [hx]
    simpa only [golden_mul_eq, golden_pow_eq] using
      golden_sector_succ_mul_phiInv delta 2
  · refine ⟨⟨3, by decide⟩, delta, ?_⟩
    rw [hx]
    simpa only [golden_mul_eq, golden_pow_eq] using
      golden_sector_succ_mul_phiInv delta 3
```

0362 `golden_sector_zero_mul_phiInv` と 0363 `golden_sector_succ_mul_phiInv` が局所的な sector 遷移を与えたのに対し、本定理はそれらを `GoldenUnitFifthClass` の存在量化された witness に持ち上げ、`φ⁻¹` 倍が five-sector 分類を保存することを示す。

## Lean の型

```lean
goldenUnitFifthClass_mul_phiInv :
  {x : GoldenInt} →
  GoldenUnitFifthClass x →
  GoldenUnitFifthClass (goldenMul x goldenPhiInv)
```

したがって、任意の黄金整数 `x` が fifth-power modulo の five-sector 表現を持つなら、その `φ⁻¹` 倍も同じ形式の表現を持つ。

`GoldenUnitFifthClass` の定義を展開すると、仮定は

```lean
∃ i : Fin 5, ∃ delta : GoldenInt,
  x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

であり、結論は

```lean
∃ j : Fin 5, ∃ gamma : GoldenInt,
  goldenMul x goldenPhiInv =
    goldenMul (goldenPow goldenPhi j.val) (goldenPow gamma 5)
```

である。

## 数学的主張

`GoldenUnitFifthClass x` を

$$
x=\varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\}
$$

と読む。

本定理は

$$
x\varphi^{-1}
$$

も同じ five-sector 形式を持つことを示す。

sector ごとの遷移は

$$
0\longmapsto4,
\qquad
1\longmapsto0,
\qquad
2\longmapsto1,
\qquad
3\longmapsto2,
\qquad
4\longmapsto3.
$$

つまり指数だけを見れば

$$
i\longmapsto i-1\pmod 5
$$

である。

ただし sector `0` だけは単純に指数を `-1` と書けないため、0362 が fifth-power witness そのものを

$$
\delta\longmapsto\varphi^{-1}\delta
$$

へ変更し、

$$
\delta^5\varphi^{-1}
=\varphi^4(\varphi^{-1}\delta)^5
$$

として sector `4` に戻す。

sector `1,2,3,4` では witness `delta` を変えず、0363 の

$$
(\varphi^{n+1}\delta^5)\varphi^{-1}
=\varphi^n\delta^5
$$

をそのまま使う。

## 証明全体での役割

0359 `goldenUnit_descent` は、measure が 1 より大きい golden unit `x` から、より小さい golden unit `y` を構成し、

$$
x=y\varphi
$$

または

$$
x=y\varphi^{-1}
$$

という一手の復元式を与えた。

この降下を strong induction へ接続するには、「小さい `y` が fifth class に属するなら、`yφ` と `yφ⁻¹` も fifth class に属する」という閉性が必要になる。

`φ` 側は直前の `goldenUnitFifthClass_mul_phi` が担当し、本定理が `φ⁻¹` 側を担当する。

実際、後続 `goldenUnitFifthClass_of_unit` では降下結果の二分岐に対して

```lean
exact goldenUnitFifthClass_mul_phi hyClass
```

または

```lean
exact goldenUnitFifthClass_mul_phiInv hyClass
```

が適用される。

したがって本定理は、局所的な sector arithmetic を unit の自然数降下による全体分類へ接続する橋である。

## 直接依存する定義・補題

プロジェクト内の直接依存は主に次である。

- `GoldenInt` — 黄金整数の型。
- `goldenMul` — 黄金整数の乗法。
- `goldenPhi` — 黄金比 unit `φ`。
- `goldenPhiInv` — `φ` の積逆元。
- `goldenPow` — 黄金整数の冪。
- `GoldenUnitFifthClass` — `x = φ^i δ^5`, `i : Fin 5` という five-sector predicate。
- `golden_sector_zero_mul_phiInv` — sector `0 → 4` の wrap-around。
- `golden_sector_succ_mul_phiInv` — successor sector `n+1 → n` の通常遷移。
- `golden_mul_eq` — `goldenMul` と通常の `(*)` 表現を対応させる rewrite 用等式。
- `golden_pow_eq` — `goldenPow` と通常の `(^)` 表現を対応させる rewrite 用等式。

Lean / Mathlib 側では主に次を使う。

- `rcases`
- `fin_cases`
- `refine`
- `decide`
- `rw`
- `simpa only`

0361 `golden_phi_four_mul_inv_five` は本定理から直接呼ばれない。0362 の内部で使われるため、依存は一段間接である。

## 証明の流れ

### 1. fifth-class witness を取り出す

最初に

```lean
rcases hx with ⟨i, delta, hx⟩
```

として、

- `i : Fin 5`
- `delta : GoldenInt`
- `hx : x = φ^i δ^5`

を得る。

これにより抽象 predicate を具体的な sector arithmetic に変換する。

### 2. `Fin 5` を完全列挙する

```lean
fin_cases i
```

によって `i = 0,1,2,3,4` の五つを完全に列挙する。

数学的には一つの合同式

$$
i\mapsto i-1\pmod5
$$

で済むが、Lean では有限集合を直接 case split することで modular arithmetic をほぼ使わずに証明している。

### 3. sector `0` を wrap-around する

最初の枝では新しい witness として

```lean
⟨⟨4, by decide⟩, goldenMul goldenPhiInv delta, ...⟩
```

を選ぶ。

つまり新しい sector は `4`、新しい fifth-power base は `φ⁻¹δ` である。

その後

```lean
rw [hx]
```

で `x` を元の sector 表現へ置き換え、

```lean
simpa only [golden_mul_eq, golden_pow_eq] using
  golden_sector_zero_mul_phiInv delta
```

によって 0362 の等式をそのまま結論へ合わせる。

### 4. sector `1,2,3,4` を一段下げる

残る四枝では fifth-power base は `delta` のままで、新しい sector witness は順に `0,1,2,3` である。

例えば sector `1` では

```lean
refine ⟨⟨0, by decide⟩, delta, ?_⟩
rw [hx]
simpa only [golden_mul_eq, golden_pow_eq] using
  golden_sector_succ_mul_phiInv delta 0
```

とする。

同様に `n = 1,2,3` を代入すれば `2→1`, `3→2`, `4→3` が閉じる。

## Lean 固有の処理

### `fin_cases i`

`i : Fin 5` という有限型の全要素を列挙する tactic である。

この theorem の数学的本体は cyclic shift だが、`fin_cases` を使うことで `Fin` の減算や `% 5` の補題を導入せず、五つの concrete case に落とせる。

### `⟨k, by decide⟩ : Fin 5`

各 sector witness は `Fin 5` なので、値 `k` だけでなく `k < 5` の証明も必要である。

`k = 0,1,2,3,4` は閉じた数値命題なので `by decide` で処理できる。

### `rw [hx]`

結論中の `x` を witness 表現へ置き換え、0362 / 0363 が扱う具体的な `φ^i δ^5` の形へ変換する。

### `simpa only [golden_mul_eq, golden_pow_eq] using ...`

局所補題 0362 / 0363 は通常の `(*)` と `(^)` の表記を使う一方、`GoldenUnitFifthClass` は project wrapper `goldenMul`, `goldenPow` を使っている。

`simpa only` はこの表記差だけを正規化し、局所補題を existential witness の目標へ正確に接続する。

`only` が付いているので、巨大な simp set に依存せず、変換内容が監査しやすい。

## 冗長・重複箇所

最も目立つ重複は successor の四枝である。

```lean
refine ⟨⟨k, by decide⟩, delta, ?_⟩
rw [hx]
simpa only [golden_mul_eq, golden_pow_eq] using
  golden_sector_succ_mul_phiInv delta k
```

というほぼ同型のコードが `k = 0,1,2,3` で四回繰り返される。

ただし、この重複には利点もある。

- five-sector の遷移表がコード上で完全に可視化される。
- `Fin` の modular subtraction API を必要としない。
- 各枝が小さく、proof failure の局所化が容易である。
- Comparator challenge としても case structure が明瞭である。

したがって「冗長だから直ちに悪い」とは言えない。

## 最適化候補

1. **現状維持** — 5 個しかない sector を明示列挙する実装は読みやすく、証明依存も単純である。
2. **successor 四枝の共通化** — `i ≠ 0` から `i = n+1` を取り出し、0363 を一度だけ適用する補題を作れる可能性がある。ただし `Fin` と `Nat` の変換が増える。
3. **循環作用の一般化** — `Fin 5` 上に `i ↦ i-1` を定義し、sector witness の更新を一つの theorem にまとめることもできる。zero case では fifth-power base の補正が必要なので、単なる指数写像だけでは完結しない。
4. **`goldenMul` / `goldenPow` wrapper の simp API 強化** — `golden_mul_eq`, `golden_pow_eq` を適切に局所 simp 化すれば各枝を短縮できる可能性がある。ただし自動 rewrite の範囲が広がり、監査性との交換になる。
5. **`φ` と `φ⁻¹` の閉性を統合** — `goldenUnitFifthClass_mul_phi` と本 theorem を、符号付き unit-step の一つの API にまとめる設計も考えられる。後続 descent の二分岐と対応しているため、現在の二本立ても十分自然である。

これらの最適化案は Lean ビルドを行っていないため未検証である。

## 必要 Mathlib import と import 最適化候補

standalone `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem 自体が直接要求する Mathlib 機能は、主として

- `Fin 5`
- `fin_cases`
- `decide`
- existential / pattern destructuring
- `rw`
- `simpa`

である。

さらに project 側から `GoldenInt`, `GoldenUnitFifthClass`, sector transition 補題群が必要となる。

`Mathlib` 全体はこの theorem 単体には過剰である可能性が高いが、元モジュール `GoldenUnitClassification.lean` の厳密な最小 import は周辺宣言の依存を含めて決まる。今回は Lean ビルドを行わない条件なので、具体的な最小 import 集合は確認できない。

## Comparator challenge 化の可否

**適している。** 特に 0362・0363 を前提として与える中程度の composition challenge に向く。

例えば次を hole にできる。

```lean
theorem goldenUnitFifthClass_mul_phiInv {x : GoldenInt}
    (hx : GoldenUnitFifthClass x) :
    GoldenUnitFifthClass (goldenMul x goldenPhiInv) := by
  ?_
```

前提 API として

```lean
golden_sector_zero_mul_phiInv
golden_sector_succ_mul_phiInv
```

を与える。

モデルが解くべき点は、

- existential witness `i, delta` を抽出すること、
- `Fin 5` を完全分岐すること、
- zero case だけ witness を `φ⁻¹δ` に補正すること、
- successor case では sector index だけを一段下げること、
- wrapper 表記と通常の ring 表記の差を `simpa only` で橋渡しすること、

である。

単なる `ring` challenge ではなく、「既存局所補題を有限分類 theorem に組み上げられるか」を測れるため、Comparator 用として 0361〜0363 より一段上の難度を持つ。

## 次に読むべき宣言

次は **0365 `goldenUnitFifthClass_one`**、種別は **`private theorem`** である。

```lean
private theorem goldenUnitFifthClass_one : GoldenUnitFifthClass goldenOne := by
  refine ⟨⟨0, by decide⟩, goldenOne, ?_⟩
  decide
```

これは measure `1` の基底分類を fifth-class の具体 witness へ接続する準備であり、

$$
1=\varphi^0\cdot1^5
$$

を sector `0` の代表として登録する。

0364 までで `φ` / `φ⁻¹` による class 保存が揃い、0365 からは strong-induction の基底となる具体的な小さい unit を fifth class に入れる段階へ進む。
