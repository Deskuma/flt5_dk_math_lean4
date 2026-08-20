# 0166 — `goldenConj_phi`

## Lean の型

```lean
/-- Conjugation sends `φ` to `1-φ`. -/
@[simp] theorem goldenConj_phi :
    goldenConj goldenPhi = goldenSub goldenOne goldenPhi := by
  decide
```

これは `theorem` であり、黄金整数環の共役 `goldenConj` が生成元 `goldenPhi` を `1-φ` へ送ることを、raw operation API 上で明示する。

## 数学的主張または宣言の意味

`GoldenInt` の元を

$$
x=a+b\varphi
$$

と読む。0163 の定義

```lean
def goldenConj (x : GoldenInt) : GoldenInt :=
  ⟨x.fst + x.snd, -x.snd⟩
```

は座標変換

$$
(a,b)\mapsto(a+b,-b)
$$

を表す。0161 では

```lean
def goldenPhi : GoldenInt := ⟨0, 1⟩
```

なので、これを共役すると

$$
(0,1)\mapsto(1,-1),
$$

すなわち

$$
\overline{\varphi}=1-\varphi
$$

となる。一方 `goldenSub goldenOne goldenPhi` も座標 `(1,-1)` であるため、本 theorem は二次拡大の非自明な共役作用を具体的な等式として公開する。

## 証明全体での役割

0165 `golden_phi_sq` が生成元の二次関係

$$
\varphi^2=\varphi+1
$$

を明示したのに対し、本 theorem はその二次方程式のもう一つの根が `1-φ` であることに対応する共役対称性を公開する。

この対称性は、後続の `goldenConj_invol`、`goldenConj_mul`、`goldenNorm_conj`、`golden_mul_conj` などで共役を代数的に扱う基礎になる。さらにノルム

$$
N(x)=x\overline{x}
$$

の構造、単元判定、整除論、Euclidean-domain 側の算術へつながる。

## 直接依存する定義・補題

主な直接依存は次である。

- `GoldenInt`
- `goldenPhi`
- `goldenOne`
- `goldenConj`
- `goldenSub`

依存関係は概念的に

$$
\texttt{goldenPhi},\ \texttt{goldenConj},\ \texttt{goldenOne},\ \texttt{goldenSub}
\longrightarrow
\texttt{goldenConj\_phi}
$$

となる。

## 証明または構築の流れ

証明は

```lean
by
  decide
```

のみである。

両辺は具体的な `GoldenInt` の閉じた値へ評価できる。左辺は

$$
goldenConj(0,1)=(1,-1),
$$

右辺は

$$
goldenOne-goldenPhi=(1,0)-(0,1)=(1,-1)
$$

である。`GoldenInt` の等号は decidable なので、`decide` がこの座標計算を評価して証明を閉じる。

## Lean 固有の処理

`decide` は `Decidable` instance を用いて命題を計算的に証明する。ここでは具体的な整数座標同士の等式なので、証明探索というより closed computation である。

また `@[simp]` により、simp は

```lean
goldenConj goldenPhi
```

を

```lean
goldenSub goldenOne goldenPhi
```

へ正規化できる。これは数学的な共役作用

$$
\varphi\mapsto1-\varphi
$$

をそのまま rewrite rule にしたものとみなせる。

`golden_sub_eq` が既に存在するため、標準 notation 側では最終的に `1 - goldenPhi` へ寄せることも可能である。

## 冗長・重複箇所

`goldenConj` と `goldenPhi` の定義を展開すれば本 theorem は直接計算できるので、情報量だけ見れば定義から導出可能な事実の再公開である。

しかし、共役の生成元上での作用は二次環を理解するうえで中心的な数学 API であり、毎回座標変換を展開するより名前付き theorem にする価値が高い。0165 と同様、内部座標実装と外部数学 API を分離するための有益な重複である。

## 最適化候補

候補は次の通りである。

1. 現行の `by decide` を維持し、閉じた計算として扱う。
2. `rfl` で閉じるか Lean build で確認し、可能なら definitional equality を強調する。
3. `norm_num [goldenConj, goldenPhi, goldenSub, goldenOne, goldenAdd, goldenNeg]` のように計算経路を明示する。
4. 標準 notation 版 `goldenConj goldenPhi = 1 - goldenPhi` を追加して downstream の可読性を高める。

今回は Lean build を行わないため、2 の可否は未検証である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用する。本 theorem 自体が直接必要とするのは、上流の `GoldenInt` 定義群、整数算術、decidable equality、`decide` である。

したがって本 theorem 単独のために `Mathlib` 全体が必要とは考えにくい。ただし `GoldenOrder` モジュール全体は algebra typeclass、ring tactic、`Zsqrtd` 等を利用するため、実際の最小 import はモジュール全体の依存に支配される。今回は build を行わないため具体的最小集合は未検証である。

## Comparator challenge 化の可否

適している。比較候補は、

- `by decide`
- `by rfl` が可能か
- `by norm_num [...]`
- `ext <;> norm_num [...]`

である。

比較軸は proof term の単純さ、定義変更への耐性、エラーメッセージ、計算過程の透明性、import 依存である。

API 設計としても、raw theorem

```lean
goldenConj goldenPhi = goldenSub goldenOne goldenPhi
```

と標準 notation theorem

```lean
goldenConj goldenPhi = 1 - goldenPhi
```

のどちらを主要 simp rule にするか比較できる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `DkMath/FLT/Five/GoldenOrder.lean` generated section である。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在するが、本 theorem に対応する具体的な PDF ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は、Lean source 上で `goldenConj_phi` の直後に置かれる共役・ノルム関連の宣言をリポジトリ正本から再確認して選ぶべきである。特に `goldenNorm_phi`、`goldenConj_invol` などが近接するため、次回は source 順を再取得して機械的な思い込みを避ける。