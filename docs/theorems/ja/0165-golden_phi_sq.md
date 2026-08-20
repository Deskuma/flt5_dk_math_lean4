# 0165 — `golden_phi_sq`

## Lean の型

```lean
/-- The defining relation of the coordinate order: `φ^2 = φ+1`. -/
@[simp] theorem golden_phi_sq :
    goldenMul goldenPhi goldenPhi = goldenAdd goldenPhi goldenOne := by
  decide
```

これは `theorem` であり、黄金整数環の生成元 `goldenPhi` が満たす基本関係 `φ^2 = φ + 1` を、raw operation API `goldenMul` / `goldenAdd` / `goldenOne` の上で明示する。

## 数学的主張または宣言の意味

`GoldenInt` の元を

$$
x=a+b\varphi
$$

と読む。0161 で

```lean
def goldenPhi : GoldenInt := ⟨0, 1⟩
```

と定義されているため、`goldenPhi` は基底元 `φ` そのものを表す。

また上流の乗法は

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

であり、これは最初から関係

$$
\varphi^2=\varphi+1
$$

を使って二次以上の項を基底 `1, φ` に還元した座標乗法である。

実際、`goldenPhi = (0,1)` を代入すると

$$
(0,1)\cdot(0,1)=(1,1),
$$

一方、`goldenPhi + goldenOne` も

$$
(0,1)+(1,0)=(1,1)
$$

となる。したがって本 theorem は、座標乗法の設計に埋め込まれていた二次関係を外向き API として取り出したものである。

## 証明全体での役割

`GoldenOrder` のここまでの流れは、まず `GoldenInt` を整数2座標で構成し、raw operation を定義し、`CommRing GoldenInt` を構築し、さらに `goldenPhi`、`goldenConj`、`goldenNorm` を導入するというものだった。

本 theorem は、その座標モデルが単なる `ℤ × ℤ` ではなく、実際に

$$
\mathbb Z[\varphi],\qquad \varphi^2-\varphi-1=0
$$

という二次整環を表していることを最も直接に示す基本恒等式である。

この関係は以後、`goldenConj_phi` で共役が `φ ↦ 1-φ` として振る舞うこと、`goldenNorm_phi` で `N(φ)=-1` となること、さらに `φ` が単元であることや unit classification へ進むための基礎構造になる。

## 直接依存する定義・補題

直接依存するのは主に次の定義である。

- `GoldenInt`
- `goldenPhi`
- `goldenOne`
- `goldenAdd`
- `goldenMul`

数学的には `goldenMul` の定義そのものが `φ^2 = φ+1` による還元を内蔵しているため、本 theorem は新しい外部仮定を導入しない。

依存関係は概念的に

$$
\texttt{goldenPhi},\ \texttt{goldenOne},\ \texttt{goldenAdd},\ \texttt{goldenMul}
\longrightarrow
\texttt{golden\_phi\_sq}
$$

となる。

## 証明または構築の流れ

証明は

```lean
by
  decide
```

のみである。

両辺は具体的な `GoldenInt` 値へ計算でき、`GoldenInt` の等号は decidable なので、`decide` が座標計算を評価して等号を閉じる。

計算内容を人間向けに展開すれば、第一座標について

$$
0\cdot0+1\cdot1=1,
$$

第二座標について

$$
0\cdot1+1\cdot0+1\cdot1=1
$$

となり、右辺 `goldenAdd goldenPhi goldenOne` の座標 `(1,1)` と一致する。

## Lean 固有の処理

`decide` は proposition に `Decidable` instance があるとき、その決定手続きを評価して証明項を生成する。ここでは等式の両辺が閉じた具体値なので、有限の整数計算として完全に評価できる。

本 theorem には `@[simp]` が付いている。そのため simp は raw 式

```lean
goldenMul goldenPhi goldenPhi
```

を

```lean
goldenAdd goldenPhi goldenOne
```

へ書き換えられる。これは `φ^2` を `φ+1` へ還元する数学的な正規化方向そのものになっている。

なお、定義を十分展開すれば `rfl` で閉じられる可能性もあるが、今回は Lean build を行わないため未検証であり、最適化候補としてのみ扱う。

## 冗長・重複箇所

`goldenMul` の定義自体が既に `φ^2=φ+1` を織り込んでいるため、本 theorem は情報量だけ見れば定義から計算可能な事実を再公開している。

しかしこれは有益な重複である。座標乗法の内部実装を毎回展開せず、数学で使う基本関係を名前付きの `@[simp]` theorem として公開することで、以後の証明を二次環の言葉で読めるようになる。

つまり、内部の座標実装と外部の数学 API を分離するための重複である。

## 最適化候補

候補は次の通りである。

1. 現行の `by decide` を維持し、閉じた具体計算であることを明示する。
2. `rfl` で閉じられるなら definitional equality を強調する実装へ変更する。
3. `norm_num [goldenPhi, goldenMul, goldenAdd, goldenOne]` のように、計算過程を tactic として明示する。
4. 標準 notation を使う別 theorem `goldenPhi ^ 2 = goldenPhi + 1` を公開し、raw API theorem は bridge として残す。

特に 4 は downstream の可読性を高める可能性がある。現行 theorem は raw operation layer の整合性を直接確認するという意味では明快である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自体が必要とする機能は、整数算術、構造体の decidable equality、`decide`、および上流の `GoldenInt` 定義群である。

したがって、この theorem 単独のために `Mathlib` 全体が必要とは考えにくい。ただし実際の `GoldenOrder` モジュール全体は ring tactic、`Zsqrtd`、各種 algebra typeclass なども使用しているため、最小 import はモジュール全体の依存で決まる。Lean build を行っていないため、具体的な最小 import 集合は未検証である。

## Comparator challenge 化の可否

適している。比較候補として、次の証明方式を並べられる。

- `by decide`
- `by rfl` が可能か
- `by norm_num [goldenPhi, goldenMul, goldenAdd, goldenOne]`
- 座標 extensionality を使う `ext <;> norm_num [...]`

比較軸は、proof term の単純さ、定義変更への耐性、エラーメッセージの読みやすさ、計算過程の透明性、Mathlib import 依存である。

また API 設計として、raw theorem

```lean
goldenMul goldenPhi goldenPhi = goldenAdd goldenPhi goldenOne
```

と標準 notation theorem

```lean
goldenPhi ^ 2 = goldenPhi + 1
```

のどちらを simp 正規化の主軸にするかも Comparator challenge にできる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `DkMath/FLT/Five/GoldenOrder.lean` generated section である。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在することを確認した。ただし、本 theorem に対応する具体的な PDF ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は

```lean
/-- Conjugation sends `φ` to `1-φ`. -/
@[simp] theorem goldenConj_phi :
    goldenConj goldenPhi = goldenSub goldenOne goldenPhi := by
  decide
```

である。

0165 で `φ^2=φ+1` という生成元の定義関係を明示した次は、非自明な自己同型である共役が

$$
\varphi\mapsto1-\varphi
$$

と作用することを確認する段階へ進む。