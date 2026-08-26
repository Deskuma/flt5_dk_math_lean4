# 0189 — `goldenDivides_refl`

## Lean の型

```lean
theorem goldenDivides_refl (x : GoldenInt) : GoldenDivides x x := by
  rw [goldenDivides_iff_dvd]
```

これは `theorem` であり、0187 で定義した黄金整数専用の整除関係 `GoldenDivides` が反射的であること、すなわち任意の黄金整数 `x` が自分自身を割ることを示す。

## 数学的主張

数学的内容は通常の整除の反射性

$$
x\mid x
$$

そのものである。

`GoldenDivides x x` の定義を直接展開すれば、ある `q : GoldenInt` が存在して

$$
x=goldenMul\ x\ q
$$

となればよい。商として `goldenOne`、標準記法なら `1` を選べば成立する。

しかし現行 proof はその witness を直接構成せず、0188 `goldenDivides_iff_dvd` を使って目標を標準整除 `x ∣ x` へ変換し、Mathlib の反射性に委譲する。

## 証明全体での役割

0187 `GoldenDivides` は raw operation `goldenMul` を用いた domain-specific な整除関係を導入し、0188 で Mathlib 標準 `∣` と完全同値であることを確立した。本 0189 は、その bridge を最初に実用する基本法則である。

このあと source は `goldenDivides_trans`、`goldenDivides_sub` と続き、専用整除 API の推移性や差に対する閉性も標準 `dvd` theorem に委譲する。

したがって 0189 の役割は新しい数論を作ることではなく、`GoldenDivides` が通常の整除と同じ algebraic behavior を持つことを、小さな named theorem として公開することにある。

後段の `GoldenRelPrime` では共通因子を `GoldenDivides` で表現するため、こうした基本法則群が domain-specific API の土台になる。

## 直接依存する定義・補題

直接依存は次の通りである。

- 0187 `GoldenDivides`
- 0188 `goldenDivides_iff_dvd`
- `GoldenInt`
- Mathlib 標準の整除反射性 `dvd_refl` 相当の API

proof script で明示的に名前を呼んでいるのは `goldenDivides_iff_dvd` だけである。

概念的には

$$
\texttt{goldenDivides\_iff\_dvd}
+\text{standard divisibility reflexivity}
\longrightarrow
\texttt{goldenDivides\_refl}
$$

である。

## 証明の流れ

現行 proof は一行だけである。

```lean
by
  rw [goldenDivides_iff_dvd]
```

1. 目標 `GoldenDivides x x` を、0188 によって `x ∣ x` へ書き換える。
2. `rw` 後の目標は標準整除の反射性になる。
3. Lean / Mathlib の既存 simplification / reflexivity machinery により目標が閉じる。

ここでは quotient witness を手で作らず、標準 API に意味を移してから閉じている。

## Lean 固有の処理

`rw [goldenDivides_iff_dvd]` は proposition-level の `↔` rewrite を行う。0188 は

```lean
theorem goldenDivides_iff_dvd {d x : GoldenInt} :
    GoldenDivides d x ↔ d ∣ x
```

なので、目標中の `GoldenDivides x x` が `x ∣ x` へ置き換わる。

この proof が一行で閉じることは、0188 の bridge が単なる説明用 theorem ではなく、実際に専用 API を Mathlib 標準 algebra へ接続する rewrite contract として機能していることを示す。

一方、定義を直接使うなら例えば概念上

```lean
refine ⟨1, ?_⟩
```

のように quotient witness を与える別方式も考えられる。ただし `GoldenDivides` は raw `goldenMul` を使うため、標準 `1` と raw multiplication の bridge を追加で処理する必要がある。

## 冗長・重複箇所

標準整除 `x ∣ x` には既に一般 theorem があるため、`goldenDivides_refl` は論理的には wrapper theorem である。

0188 が存在する以上、downstream で毎回

```lean
rw [goldenDivides_iff_dvd]
```

と書けば同じ事実を得られる。

それでも named theorem を置く利点は、FLT5 の黄金整数部分を `GoldenDivides` の語彙だけで読めることである。domain-specific API の利用者は標準 `dvd` への変換手順を意識せず、`goldenDivides_refl` を直接使える。

したがってこれは数学的重複というより API convenience のための意図的な薄い wrapper と見るのが自然である。

## 最適化候補

1. **現行の薄い wrapper を維持する**
   - domain-specific theorem 名を保ち、Mathlib 実装詳細を隠せる。

2. **wrapper を削除して標準 `dvd_refl` を直接使う**
   - コード量は減るが、downstream で bridge rewrite が増える可能性がある。

3. **定義から直接 witness を構成する**
   - `GoldenDivides` の raw semantics をより明示できる。
   - 一方で 0188 の bridge を再利用しないため、API architecture としてはやや逆行する。

4. **0188 を `[simp]` 化して `simp` で閉じる設計を検討する**
   - `GoldenDivides` を標準 `dvd` へ自動正規化できる可能性がある。
   - proposition-level simp の広がりは要検証である。

現行 proof は一行で、可読性も高いため、局所的な最適化余地は小さい。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が必要とする表面は小さい。

- `GoldenInt`
- `GoldenDivides`
- `goldenDivides_iff_dvd`
- 標準 `Dvd` relation
- `rw` tactic

本 theorem 単独では `ring`、`norm_num`、`omega` などは不要である。

ただし `GoldenDivisibility.lean` 全体では直後に `dvd_trans`、`dvd_sub`、整数ノルム整除、unit 関連 theorem を使用するため、module 全体の最小 import はより広い。今回は Lean build を行わないため、正確な細粒度 import は未検証の最適化候補として扱う。

## Comparator challenge 化の可否

適している。小さな theorem なので proof architecture の違いが明瞭に比較できる。

- A: 現行 `rw [goldenDivides_iff_dvd]`
- B: `GoldenDivides` を直接展開して quotient `1` を構成
- C: 標準 `dvd_refl` を明示的に使う proof
- D: 0188 を `[simp]` 化して `simpa`

比較軸は、proof term の短さ、raw semantics の可視性、Mathlib 依存、bridge theorem の再利用度、simp の安定性、downstream readability である。

A と B の比較は特に、「domain-specific 定義を直接証明するか、標準 algebra API に transport して証明するか」という設計差を見るよい Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

直前の 0188 文書と source 順から、次の並びが確認できる。

```lean
theorem goldenDivides_iff_dvd {d x : GoldenInt} :
    GoldenDivides d x ↔ d ∣ x := by
  ...

theorem goldenDivides_refl (x : GoldenInt) : GoldenDivides x x := by
  rw [goldenDivides_iff_dvd]
```

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、本 theorem に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0190 `goldenDivides_trans`** である。

```lean
theorem goldenDivides_trans {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hxy : GoldenDivides x y) :
    GoldenDivides d y := by
  rw [goldenDivides_iff_dvd] at hdx hxy ⊢
  exact dvd_trans hdx hxy
```

0189 が反射性を標準 `dvd` へ委譲したのに対し、0190 は二つの `GoldenDivides` 仮定を標準整除へ移し、Mathlib の推移性 `dvd_trans` を再利用する。