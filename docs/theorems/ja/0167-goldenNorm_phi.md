# 0167 — `goldenNorm_phi`

## Lean の型

```lean
/-- The basis unit `φ` has norm `-1`. -/
@[simp] theorem goldenNorm_phi : goldenNorm goldenPhi = -1 := by
  norm_num [goldenNorm, goldenPhi]
```

これは `theorem` であり、黄金整数環の生成元 `goldenPhi` のノルムが `-1` であることを明示する `@[simp]` 補題である。

## 数学的主張または宣言の意味

0161 で

```lean
def goldenPhi : GoldenInt := ⟨0, 1⟩
```

と定義し、0164 で

```lean
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

と定義している。したがって

$$
N(\varphi)=0^2+0\cdot1-1^2=-1.
$$

通常の二次体の言葉では、$\varphi=(1+\sqrt5)/2$ の共役は $1-\varphi$ であり、

$$
\varphi(1-\varphi)=-1
$$

である。本 theorem はこの生成元のノルムを整数 `-1` として Lean API に固定する。

## 証明全体での役割

0165 `golden_phi_sq` が $\varphi^2=\varphi+1$ を、0166 `goldenConj_phi` が $\overline\varphi=1-\varphi$ を公開したのに続き、本 theorem は生成元の三つ目の基本事実

$$
N(\varphi)=-1
$$

を公開する。

ノルムが `±1` の元は黄金整数環の単元判定に現れるため、これは `goldenPhi` が単元であることの算術的証拠になる。実際、後続の `goldenUnit_phi` は `goldenUnit_of_norm_eq_neg_one` を用いて同じ計算を再度行っている。

さらに `goldenPhi` の冪を単元係数として扱う第五冪分解・unit-sector の議論にもつながる。

## 直接依存する定義・補題

直接依存は次である。

- `GoldenInt`
- 0161 `goldenPhi`
- 0164 `goldenNorm`
- 整数算術と `norm_num`

本 theorem 自体は 0165 `golden_phi_sq` や 0166 `goldenConj_phi` を証明上は使用しない。数学的には密接に関連するが、Lean proof は座標定義を直接評価する独立な閉計算である。

## 証明または構築の流れ

証明は

```lean
by
  norm_num [goldenNorm, goldenPhi]
```

のみである。

`goldenPhi` を `⟨0,1⟩` に展開し、`goldenNorm` を

$$
a^2+ab-b^2
$$

に展開すると、目標は整数上の

$$
0^2+0\cdot1-1^2=-1
$$

へ落ちる。`norm_num` がこの数値計算を閉じる。

## Lean 固有の処理

`norm_num` は具体的な数値式を正規化する tactic である。ここでは抽象的な ring 推論ではなく、定義展開後の閉じた整数式を評価している。

また `@[simp]` により、simp は

```lean
goldenNorm goldenPhi
```

を直接

```lean
-1
```

へ正規化できる。これにより `goldenPhi` を含む unit / norm 計算で生成元のノルムを毎回展開する必要がなくなる。

## 冗長・重複箇所

本 theorem の値 `-1` は `goldenNorm` と `goldenPhi` の定義から即座に再計算できるため、情報としては導出可能である。しかし生成元のノルムは二次整数環の中心的 API なので、名前付き `@[simp]` theorem にする価値は高い。

一方、後続の `goldenUnit_phi` は

```lean
theorem goldenUnit_phi : GoldenUnit goldenPhi := by
  apply goldenUnit_of_norm_eq_neg_one
  norm_num [goldenNorm, goldenPhi]
```

と同じ数値計算を再実行している。ここは本 theorem を利用して

```lean
simpa using goldenNorm_phi
```

または同等の短い証明へ寄せられる可能性があり、明確な重複候補である。

## 最適化候補

候補は次の通りである。

1. 現行の `norm_num [goldenNorm, goldenPhi]` を維持する。
2. 定義的等価性だけで `rfl` が成立するか Lean build で確認する。
3. `decide` で閉じる closed computation と比較する。
4. 後続の `goldenUnit_phi` で本 theorem を再利用し、ノルム計算の重複を除く。
5. 共役積による theorem `goldenPhi * goldenConj goldenPhi = -1` との API 関係を整理する。

今回は Lean build を行わないため、2 の可否は未検証である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 単独では、上流の `GoldenInt` / `goldenNorm` / `goldenPhi` 定義、整数算術、`norm_num` tactic が主な依存である。

したがって本 theorem のためだけに Mathlib 全体が必要とは考えにくい。ただし `GoldenOrder` モジュール全体は algebra typeclass、`ring`、`Zsqrtd` などを利用しており、実際の最小 import はモジュール全体の依存に支配される。今回は build を行わないため具体的最小集合は未検証である。

## Comparator challenge 化の可否

適している。比較候補は、

- `norm_num [goldenNorm, goldenPhi]`
- `rfl` が可能か
- `decide`
- `ring_nf` / `norm_num` の組合せ

である。

比較軸は proof term の単純さ、定義変更への耐性、エラーメッセージの明瞭さ、必要 import、計算過程の透明性である。

また API 設計として、本 theorem を後続 `goldenUnit_phi` が実際に再利用する版と、各所で定義を再展開する版との比較も有益である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `DkMath/FLT/Five/GoldenOrder.lean` generated section である。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし、本 theorem に対応する具体的な PDF ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

Lean source 上で直後に置かれている次の宣言は

```lean
/-- Conjugation fixes the embedded rational integers. -/
@[simp] theorem goldenConj_ofInt (a : ℤ) :
    goldenConj (goldenOfInt a) = goldenOfInt a := by
  ...
```

である。したがって依存順の次は **0168 `goldenConj_ofInt`** とするのが自然である。生成元 `φ` に対する共役作用を確認した後、今度は整数部分が共役で固定されることを示す段階へ進む。
