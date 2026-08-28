# 0261 — `goldenPhi_pow_two`

## Lean の型

```lean
theorem goldenPhi_pow_two :
    goldenPow goldenPhi 2 = ⟨1, 1⟩ := by
  decide
```

これは `theorem` であり、黄金整数の基底元 `goldenPhi` の 2 乗が具体座標 `⟨1,1⟩` に等しいことを示す。

## 数学的主張

黄金比の基底元を $\varphi$ とすると、その基本関係

$$
\varphi^2=\varphi+1
$$

より、`GoldenInt` の座標表示では

$$
\varphi^2=1+1\varphi=\langle1,1\rangle
$$

となる。

したがって本 theorem は、raw power `goldenPow goldenPhi 2` を具体的な黄金整数座標へ落とす

$$
goldenPow(\varphi,2)=\langle1,1\rangle
$$

という finite unit-representative table の 2 番目の非自明なエントリである。

## 証明全体での役割

0259–0263 の小ブロックは、第五冪まで unit class を整理するための代表元

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

を具体座標として固定する。

正本 source では次の順に並ぶ。

```lean
theorem goldenPhi_pow_zero : goldenPow goldenPhi 0 = ⟨1, 0⟩ := rfl
theorem goldenPhi_pow_one : goldenPow goldenPhi 1 = ⟨0, 1⟩ := by decide
theorem goldenPhi_pow_two : goldenPow goldenPhi 2 = ⟨1, 1⟩ := by decide
theorem goldenPhi_pow_three : goldenPow goldenPhi 3 = ⟨1, 2⟩ := by decide
theorem goldenPhi_pow_four : goldenPow goldenPhi 4 = ⟨2, 3⟩ := by decide
```

本 theorem は unit representative `φ²`、すなわち sector index `2` を担当する。

後続の `golden_unit_two_mul_fifth_snd` では実際に

```lean
rw [goldenPhi_pow_two]
simp only [goldenMul]
rw [goldenPow_five_fst, goldenPow_five_snd]
ring
```

という流れで使われる。

その theorem は

```lean
theorem golden_unit_two_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 2) (goldenPow gamma 5)).snd =
      goldenFifthFstPoly gamma.fst gamma.snd +
        2 * goldenFifthSndPoly gamma.fst gamma.snd := by
  ...
```

を与えるので、`φ² * γ⁵` の第二座標を explicit polynomial に落とす際、本 theorem が raw unit power を座標 `⟨1,1⟩` へ変換する入口になる。

したがって数学的には小さな恒等式だが、証明全体では **unit sector 2 の canonical representative を具体座標として固定する rewrite interface** である。

## 直接依存する定義・補題

直接依存する主な定義は次の通り。

- `GoldenInt`
- `goldenPhi`
- `goldenPow`
- `goldenMul`
- `goldenOne`

proof は `by decide` だけであり、named theorem を直接呼び出してはいない。

`goldenPow goldenPhi 2` を再帰的に展開すると、概念的には

$$
\varphi^2
=\varphi\cdot\varphi
$$

である。

黄金整数の乗法は $\varphi^2=\varphi+1$ を組み込んだ座標演算なので、`⟨0,1⟩ * ⟨0,1⟩` を計算すれば `⟨1,1⟩` が得られる。

0259 `goldenPhi_pow_zero` や 0260 `goldenPhi_pow_one` は論理上の前提として theorem 名を呼び出してはいないが、同じ finite representative table を構成する隣接宣言である。

## 証明または構築の流れ

proof は

```lean
by
  decide
```

のみである。

目標は閉じた `GoldenInt` 同士の equality であるため、Lean は `Decidable` instance を用いて命題を計算できる。

概念的な評価順は次のようになる。

1. `goldenPow goldenPhi 2` を固定指数 2 で再帰評価する。
2. `goldenPhi = ⟨0,1⟩` を使う。
3. `goldenMul` の座標演算を評価する。
4. 黄金比関係を組み込んだ乗法結果として `⟨1,1⟩` を得る。
5. 左右の structure equality を整数座標 equality に落として `decide` が閉じる。

数学的には

$$
\varphi^2
=1+\varphi
$$

の一行である。

## Lean 固有の処理

`decide` は、目標命題の `Decidable` instance を評価して proof term を生成する。

ここでは一般的な環論 theorem を適用するのではなく、固定された指数と固定された要素をそのまま計算している。したがって proof は非常に短い。

`GoldenInt` は整数座標を持つ structure であり、具体 term 間の equality は二つの整数 equality へ還元できるため decidable である。

なお raw `goldenPow` は後に標準 `^` と接続されているため、別設計では `golden_pow_eq` と標準の冪 API を使うこともできる。しかし、この固定指数 theorem に対しては closed computation の方が依存が浅い。

## 冗長・重複箇所

数学的には本 theorem の情報は基本関係

$$
\varphi^2=\varphi+1
$$

そのものであり、黄金整数の乗法定義にも同じ情報が既に埋め込まれている。

したがって必要箇所で

```lean
simp [goldenPow, goldenPhi, goldenMul, goldenOne]
```

のように展開すれば、named theorem を置かずとも同じ計算は可能である。

一方、0259–0263 を五つの representative theorem として明示する利点は大きい。

- unit sector と具体座標の対応が source 上で一目で分かる。
- downstream が `goldenPow` の実装を知らず `rw` だけで利用できる。
- sector 0–4 の proof pattern が対称になる。
- 実装変更時も unit-representative API を安定させられる。

よって、論理的には重複していても proof architecture 上は有用である。

## 最適化候補

1. **現行の `by decide` を維持する**
   - 固定指数・固定座標の closed computation として最小に近い。

2. **`simp` による定義展開と比較する**
   - `simp [goldenPow, goldenPhi, goldenMul, goldenOne]` が通るなら、どの定義を評価したかが明示される。
   - ただし定義変更への耐性では `decide` の方が高い可能性がある。

3. **標準冪 API へ寄せる**
   - `golden_pow_eq` を介して標準 `^` に移し、`pow_two` と黄金比の二次関係を使う設計。
   - 一般性は増すが、この theorem 単独では依存が深くなる。

4. **`Fin 5` representative table を一括定義する**
   - `i : Fin 5` に対して `φ^i` の座標を返す table を定義し、0259–0263 を specialization とする。

5. **Fibonacci 座標公式へ一般化する**
   - $\varphi^n$ の座標は Fibonacci recurrence で表現できるので、一般 theorem から `n=2` を導くこともできる。
   - FLT5 では mod 5 の五代表だけが必要なので、現行 finite table の方が軽い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は

```lean
import Mathlib
```

を使用している。

本 theorem 自身が必要とする Mathlib 機能は非常に少なく、主として closed equality を処理する `decide` と、`GoldenInt` の基礎定義群である。`ring`、`omega`、整除、`Fin 5` などは本 theorem 単独では不要である。

ただし同じ `GoldenFifthPowerCoordinates.lean` module には、0255–0258 の多項式展開で `ring` が使われ、さらに後続 sector arithmetic では追加の代数処理が必要になる。

今回は Lean build を行わないため、正確な最小 import 集合は検証していない。したがって import 最適化は候補としてのみ記録する。

## Comparator challenge 化の可否

本 theorem 単独では小さすぎるが、0259–0263 の representative block 全体なら Comparator challenge に適している。

比較案は次の通り。

- A: 現行の `rfl` / `decide` による個別 closed computation
- B: `simp` による explicit reduction
- C: 標準 power API を使う proof
- D: `Fin 5` table による一括実装
- E: Fibonacci recurrence による一般座標 theorem からの specialization

比較軸は proof term の短さ、依存深度、定義変更への耐性、downstream rewrite usability、五 sector の対称性、一般化可能性である。

0261 単独では現行 `by decide` が十分に簡潔なので、局所最適化の優先度は低い。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenFifthPowerCoordinates.lean` generated section である。

正本 source では 0260 `goldenPhi_pow_one` の直後に本 theorem があり、その後 0262 `goldenPhi_pow_three`、0263 `goldenPhi_pow_four` が続く。

さらに downstream の `golden_unit_two_mul_fifth_snd` が本 theorem を直接 `rw [goldenPhi_pow_two]` で利用していることを確認した。

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的な PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0262 `goldenPhi_pow_three`** である。

```lean
theorem goldenPhi_pow_three :
    goldenPow goldenPhi 3 = ⟨1, 2⟩ := by
  decide
```

これは

$$
\varphi^3
=\varphi(\varphi+1)
=1+2\varphi
$$

を具体座標 `⟨1,2⟩` として unit representative table に固定し、sector index `3` の後続 arithmetic へ渡す theorem である。
