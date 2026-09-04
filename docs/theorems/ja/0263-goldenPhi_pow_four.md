# 0263 — `goldenPhi_pow_four`

## Lean の型

```lean
theorem goldenPhi_pow_four :
    goldenPow goldenPhi 4 = ⟨2, 3⟩ := by
  decide
```

これは `theorem` であり、黄金整数の基底元 `goldenPhi` の 4 乗が具体座標 `⟨2,3⟩` に等しいことを示す。

## 数学的主張

黄金比の基底元を $\varphi$ とし、基本関係

$$
\varphi^2=\varphi+1
$$

を使うと、

$$
\varphi^4
=\varphi\varphi^3
=\varphi(1+2\varphi)
=\varphi+2(1+\varphi)
=2+3\varphi.
$$

したがって `GoldenInt` の座標表示では

$$
\varphi^4=\langle2,3\rangle.
$$

本 theorem は raw power `goldenPow goldenPhi 4` をこの具体座標へ落とす

$$
goldenPow(\varphi,4)=\langle2,3\rangle
$$

という finite unit-representative table の index `4` のエントリである。

## 証明全体での役割

正本 source の `GoldenFifthPowerCoordinates.lean` 部分では、第五冪までの unit class を扱うために

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

の五代表を具体座標として固定している。

```lean
theorem goldenPhi_pow_zero : goldenPow goldenPhi 0 = ⟨1, 0⟩ := rfl
theorem goldenPhi_pow_one : goldenPow goldenPhi 1 = ⟨0, 1⟩ := by decide
theorem goldenPhi_pow_two : goldenPow goldenPhi 2 = ⟨1, 1⟩ := by decide
theorem goldenPhi_pow_three : goldenPow goldenPhi 3 = ⟨1, 2⟩ := by decide
theorem goldenPhi_pow_four : goldenPow goldenPhi 4 = ⟨2, 3⟩ := by decide
```

本 theorem はその最後、unit representative $\varphi^4$、すなわち sector index `4` を担当し、これで五代表表が完成する。

この module のコメントは、`gamma=p+q*φ` の第五冪の二座標を名前付き多項式にし、その後 `1,φ,...,φ^4` を掛けた第二座標を計算して、unit class modulo fifth powers を五つの explicit arithmetic sectors に変換する、と説明している。したがって 0259–0263 は、その sector routing に必要な unit 側の具体化層である。

後続の `golden_unit_four_mul_fifth_snd` では実際に

```lean
rw [goldenPhi_pow_four]
simp only [goldenMul]
rw [goldenPow_five_fst, goldenPow_five_snd]
ring
```

と本 theorem が使われる。`gamma^5=A+B\varphi` と書けば、$\varphi^4=2+3\varphi$ より

$$
(2+3\varphi)(A+B\varphi)
$$

の $\varphi$ 座標は

$$
3A+5B
$$

となる。正本 Lean source でも sector 4 の第二座標は

```lean
3 * goldenFifthFstPoly gamma.fst gamma.snd +
  5 * goldenFifthSndPoly gamma.fst gamma.snd
```

として証明されている。

したがって本 theorem は数学的には小さな closed identity だが、証明全体では  **unit sector 4 の canonical representative を explicit coordinate に固定し、第五冪座標の算術 sector 解析へ接続して五代表表を閉じる rewrite interface**  である。

## 直接依存する定義・補題

直接依存する主な定義は次の通り。

- `GoldenInt`
- `goldenPhi`
- `goldenPow`
- `goldenMul`
- `goldenOne`

正本 source では

```lean
def goldenPhi : GoldenInt := ⟨0, 1⟩
```

であり、自然数冪は

```lean
def goldenPow (x : GoldenInt) : ℕ → GoldenInt
  | 0 => goldenOne
  | n + 1 => goldenMul (goldenPow x n) x
```

として定義されている。また黄金整数の積は

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

で、第二成分の `x.snd * y.snd` が $\varphi^2=1+\varphi$ の関係を座標乗法へ組み込んでいる。

proof は `by decide` のみであり、直前の `goldenPhi_pow_three` を theorem として直接呼び出してはいない。数学的説明では $\varphi^3=1+2\varphi$ を利用できるが、Lean 上の論理依存は固定された `goldenPow goldenPhi 4` の定義計算で完結する。

## 証明または構築の流れ

proof は

```lean
by
  decide
```

だけである。

概念的な評価は次の通り。

1. `goldenPow goldenPhi 4` を固定指数 4 で再帰評価する。
2. `goldenPhi = ⟨0,1⟩` を使う。
3. `goldenMul` の座標乗法を 4 乗まで繰り返す。
4. `goldenMul` に組み込まれた $\varphi^2=\varphi+1$ により各積が二座標へ正規化される。
5. 左辺が具体座標 `⟨2,3⟩` に評価され、structure equality を `decide` が閉じる。

数学的な再帰表示では

$$
\varphi^3=1+2\varphi
$$

から

$$
\varphi^4
=\varphi(1+2\varphi)
=2+3\varphi
$$

である。

## Lean 固有の処理

`decide` は目標命題の `Decidable` instance を実行し、真と判定された閉じた命題の proof term を生成する。

今回の目標には自由変数がないため、一般的な環論補題を適用するより closed computation として評価するのが自然である。`GoldenInt` は整数座標を持つ structure なので、計算後の equality は具体的な整数座標の equality に還元できる。

`⟨2,3⟩` の型は目標の右辺から `GoldenInt` と推論され、数値 `2`, `3` はその整数座標として解釈される。

一方、後続の `golden_unit_four_mul_fifth_snd` は変数 `gamma` を含むため `decide` だけでは閉じない。本 theorem で unit 側を `⟨2,3⟩` に具体化した後、`goldenMul` を展開し、0257 `goldenPow_five_fst` と 0258 `goldenPow_five_snd` で第五冪の座標を named polynomial に置き換え、最後に `ring` で symbolic polynomial identity を閉じる。この境界が closed computation と symbolic arithmetic の役割分担である。

## 冗長・重複箇所

0259–0263 の五 theorem は、いずれも固定された $\varphi^k$ の具体座標を列挙するため形が非常によく似ている。数学的には Fibonacci 型の再帰

$$
\varphi^n=F_{n-1}+F_n\varphi
$$

から一括して得られる情報であり、`goldenPow` と `goldenMul` の定義を直接展開しても同じ座標を計算できる。

しかし named theorem として個別に残す利点は大きい。

- sector index `0` から `4` と具体座標の対応が source 上で一目で分かる。
- downstream は `goldenPow` の再帰実装を知らず `rw [goldenPhi_pow_four]` だけでよい。
- 五 sector theorem と一対一に対応し、監査しやすい。
- `goldenPow` の実装変更を representative theorem 境界で吸収しやすい。
- sector 4 の係数 `3A+5B` の `3,5` が `⟨2,3⟩` から来ることを追跡しやすい。

したがって論理情報としては重複しているが、proof architecture 上は意図的で有用な重複である。

## 最適化候補

1.  **現行の `by decide` を維持する**
   - 固定指数・固定要素の closed computation として最短級である。
   - theorem 単体の保守性も高い。

2.  **`simp` による explicit reduction と比較する**
   - `simp [goldenPow, goldenPhi, goldenMul, goldenOne]` のような proof にすれば、どの定義から座標が生じるかを表に出せる。
   - ただし内部実装への依存は増える。

3.  **`goldenPhi_pow_three` から再帰的に導く**
   - $\varphi^4=\varphi\cdot\varphi^3$ を数学の説明通りに formalize できる。
   - ただし現行 proof より長くなり、論理依存も一段増える。

4.  **五代表を table 化する**
   - `i : Fin 5` から代表座標を返す定義を作り、0259–0263 を specialization とする方法がある。
   - unit-class routing をさらに一般化するなら有力だが、五件だけなら現在の named theorem 群も十分明快である。

5.  **Fibonacci 座標公式へ一般化する**
   - 一般の $n$ について $\varphi^n$ の座標を Fibonacci 数で記述できる。
   - ただし FLT5 の局所目的は modulo fifth powers の五代表なので、この module に一般理論を持ち込むことが本当に簡潔化になるかは別途評価が必要である。

今回は Lean build を行わないため、これら最適化案のコンパイル可否・proof term サイズ・実際の import 削減量は検証していない。

## 必要 Mathlib import と import 最適化候補

生成済み standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem 単独が直接使う機能は小さく、主に次の範囲である。

- `Decidable` equality と `decide`
- `GoldenInt` の整数座標に必要な基礎
- 上流で定義された `goldenPhi`、`goldenPow`、`goldenMul`、`goldenOne`

本 theorem 自身は `ring`、`omega`、gcd、整除、valuation などを使わない。`decide` 自体は Lean の基礎機構であり、本 theorem だけのために Mathlib 全体が必要という意味ではない。

ただし同じ `GoldenFifthPowerCoordinates.lean` 相当部分では第五冪座標と sector の symbolic polynomial 証明に `ring` が使われるため、module 単位の必要 import は theorem 単体より広い。

リポジトリには元の分割 module の単独ファイルが配置されておらず、このブランチで確認できる正本は生成済み standalone artifact である。そのため具体的にどの細分化 Mathlib import まで削れるかは、Lean build を行わない今回の条件では確認できない。import 最適化は候補としてのみ記録する。

## Comparator challenge 化の可否

本 theorem 単独は難度が低いが、closed computation の proof strategy 比較として Comparator challenge 化できる。より有意義なのは 0259–0263 の representative block 全体を一組として比較することである。

比較候補は次の通り。

- A: 現行の `rfl` / `decide` による個別 closed computation
- B: `simp` で `goldenPow`、`goldenPhi`、`goldenMul` を explicit 展開する proof
- C: 前指数の representative theorem から再帰的に導く proof
- D: Fibonacci 座標公式を一般証明して各指数へ specialize する proof

評価軸は proof term の短さ、定義変更への耐性、数学的説明性、依存の浅さ、downstream の `rw` 利便性である。

特に 0263 は五代表表の終端なので、局所的な closed computation 五本を維持する方がよいのか、一般 theorem 一本から生成する方がよいのかを比較する小さな benchmark に向く。

## PDF との対応

対象ブランチには次の PDF が存在することを今回改めて確認した。

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

ただし今回、0263 `goldenPhi_pow_four` に対応する具体的な PDF ページまたは節番号までは特定していない。そのため PDF 上の位置や文言を推測して引用することはしない。

技術的意味については、リポジトリ正本の `Flt5DkMath/FLT5StandAlone.lean` に収録された `GoldenFifthPowerCoordinates.lean` の module コメント、実際の `goldenPhi_pow_four`、および downstream の `golden_unit_four_mul_fifth_snd` を主根拠とした。

## 次に読むべき宣言

source 順で本 theorem の直後は

```lean
/-- Second coordinate after the representative unit `1`. -/
theorem golden_unit_zero_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 0) (goldenPow gamma 5)).snd =
      goldenFifthSndPoly gamma.fst gamma.snd := by
```

すなわち次に読むべき宣言は  **0264 `golden_unit_zero_mul_fifth_snd`**  である。

0263 までで五つの unit representative の具体座標が揃った。0264 からは、その代表を `gamma^5` に掛けたときの第二座標を sector ごとに explicit polynomial として計算する段階へ移る。最初の zero sector は unit `1=\varphi^0` なので、第二座標がそのまま `goldenFifthSndPoly` になる。