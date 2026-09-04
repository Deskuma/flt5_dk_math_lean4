# 0260 — `goldenPhi_pow_one`

## Lean の型

```lean
theorem goldenPhi_pow_one : goldenPow goldenPhi 1 = ⟨0, 1⟩ := by decide
```

これは `theorem` であり、黄金整数の基底元 `goldenPhi` の 1 乗が、その定義座標 `⟨0,1⟩` に等しいことを示す。

## 数学的主張

数学的内容は

$$
\varphi^1=\varphi
$$

そのものである。

`GoldenInt` では

$$
a+b\varphi
$$

を座標 `⟨a,b⟩` で表し、`goldenPhi` 自身が

$$
\varphi=0+1\varphi
$$

すなわち `⟨0,1⟩` と定義されている。

したがって本 theorem は

$$
goldenPow(\varphi,1)=\langle0,1\rangle
$$

という、1 乗の具体座標表示を公開する小さな rewrite theorem である。

## 証明全体での役割

0259 から始まった小ブロックでは、unit representative

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

を raw power `goldenPow goldenPhi i` の具体座標として固定している。

正本 source では

```lean
theorem goldenPhi_pow_zero : goldenPow goldenPhi 0 = ⟨1, 0⟩ := rfl
theorem goldenPhi_pow_one : goldenPow goldenPhi 1 = ⟨0, 1⟩ := by decide
theorem goldenPhi_pow_two : goldenPow goldenPhi 2 = ⟨1, 1⟩ := by decide
theorem goldenPhi_pow_three : goldenPow goldenPhi 3 = ⟨1, 2⟩ := by decide
theorem goldenPhi_pow_four : goldenPow goldenPhi 4 = ⟨2, 3⟩ := by decide
```

と並ぶ。

これらは後続の unit-sector arithmetic で

$$
\varphi^i\gamma^5
$$

の第二座標を sector ごとに展開するための finite table として働く。

本 theorem は index `1`、すなわち unit representative `φ` の sector を担当する。後続の `golden_unit_one_mul_fifth_snd` では最初に

```lean
rw [goldenPhi_pow_one]
```

を行い、`φ * γ^5` の raw multiplication を座標 `⟨0,1⟩` との積へ落としてから、0257 `goldenPow_five_fst` と 0258 `goldenPow_five_snd` を使って explicit polynomial へ展開する。

その結果、unit class `φ` に属する fifth-power-up-to-unit 表現の第二座標を、0255・0256 の多項式から直接解析できる。

したがって本 theorem は自明な 1 乗則そのものではあるが、**unit sector 1 の canonical representative を downstream が安定して rewrite できる API にする** 役割を持つ。

## 直接依存する定義・補題

直接依存する定義は次の通りである。

- `GoldenInt`
- `goldenPhi`
- `goldenPow`
- `goldenMul`
- `goldenOne`

proof は `by decide` だけなので、上流の named theorem を直接呼び出してはいない。

`goldenPow goldenPhi 1` は再帰定義により

$$
goldenMul\;(goldenPow\;goldenPhi\;0)\;goldenPhi
$$

へ落ち、さらに 0 乗と `goldenPhi` の具体座標を評価すると `⟨0,1⟩` になる。

概念的には

$$
\varphi^1
=1\cdot\varphi
=\varphi
=\langle0,1\rangle
$$

である。

## 証明の流れ

proof は

```lean
by decide
```

だけである。

両辺は完全に閉じた `GoldenInt` の等式であり、`GoldenInt` の equality が decidable なので、Lean は `goldenPow`、`goldenMul`、`goldenPhi` 等を計算して equality proposition を判定できる。

数学的な帰納法や環の一般 theorem を使うのではなく、固定された指数 `1` と固定された座標を直接評価している。

## Lean 固有の処理

`decide` は、目標命題に `Decidable` instance があるとき、その決定手続きで命題が真であることを計算して proof term を生成する。

ここでは `GoldenInt` が整数二座標を持つ有限構造ではないものの、与えられた二つの具体 term の equality 自体は整数 equality に還元できるため decidable である。

0259 `goldenPhi_pow_zero` は `rfl` だったのに対し、0260 では再帰的な乗法を一段評価する必要があるため、現行 source は `decide` を選んでいる。

ただし数学的には `φ^1=φ` なので、標準冪 API を使えば `pow_one` に相当する一般 lemma へ寄せる設計も可能である。0160 `golden_pow_eq` により raw `goldenPow` と標準 `^` は既に接続されている。

## 冗長・重複箇所

数学的情報量は非常に小さい。

- `goldenPhi` は既に `⟨0,1⟩` と定義されている。
- `goldenPow` の指数 1 は 0 乗と一回の乗法から計算できる。
- 標準代数 API には一般的な `pow_one` がある。

したがって必要な場所で定義展開すれば本 theorem 自体は省略できる。

一方、0259–0263 の五つの unit representative theorem を対称な API として揃える意味は大きい。

- downstream が raw power の内部実装を知らずに `rw` できる。
- sector index と具体座標の対応が source 上で一覧化される。
- 後続の五 sector theorem が同じ proof patternを使える。
- `goldenPow` の実装が変わっても代表座標 theorem を interface として維持できる。

したがって論理的には冗長でも、finite unit-sector table の構成要素として有用な named theorem である。

## 最適化候補

1. **現行の個別 theorem を維持する**
   - downstream の `rw [goldenPhi_pow_one]` が明快で、五 sector の対称性も保てる。

2. **`simp` / `norm_num` / `rfl` 系 proof と比較する**
   - `decide` が最も安定か、`simp [goldenPow, goldenPhi, goldenMul, goldenOne]` の方が意図を説明しやすいかを build で比較できる。

3. **標準 `pow_one` から導く**
   - `golden_pow_eq` を介して標準 `^` に移し、一般的な `pow_one` を使う設計も可能である。
   - ただし一行の closed computation に対して依存が深くなる可能性がある。

4. **`Fin 5` の unit representative table を導入する**
   - `i : Fin 5` から `φ^i` の座標を返す関数・定理を用意し、0259–0263 を specialization にする。

5. **Fibonacci 型 recurrence を一般化する**
   - `φ^n` の座標が Fibonacci 系列で記述できることを一般 theorem として証明し、0〜4 はその corollary にする設計も考えられる。
   - FLT5 で必要なのが mod 5 の五代表だけなら現行の有限表の方が軽量である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem 単独では `decide` と、`GoldenInt` / `goldenPow` / `goldenPhi` の基礎定義があれば足りる。`ring`、`omega`、整除 API などは本 theorem 自身では使わない。

ただし同じ `GoldenFifthPowerCoordinates.lean` module には、0255–0258 の `ring`、後続の `Fin 5`、`fin_cases`、整除、sector arithmetic などが含まれるため、module 全体の最小 import は本 theorem 単独より広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

単独 theorem としては小さいが、0259–0263 の representative block 全体なら Comparator challenge に適している。

比較候補は次の通り。

- A: 現行の個別 closed computation (`rfl` / `decide`)
- B: `simp` / `norm_num` による explicit reduction
- C: 標準冪 notation と `pow_zero` / `pow_one` / 再帰 lemma を利用
- D: `Fin 5` table による一括証明
- E: Fibonacci recurrence から一般 `φ^n` 座標 theorem を導出

比較軸は proof term の短さ、依存深度、計算透明性、downstream rewrite usability、五 sector の対称性、一般化可能性である。

0260 単独では現行 `by decide` は十分短く、局所最適化の優先度は低い。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenFifthPowerCoordinates.lean` generated section である。

正本 source では 0259 `goldenPhi_pow_zero` の直後に本 theorem が置かれ、その後に `goldenPhi_pow_two`、`goldenPhi_pow_three`、`goldenPhi_pow_four` が続く。

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的な PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0261 `goldenPhi_pow_two`** である。

```lean
theorem goldenPhi_pow_two : goldenPow goldenPhi 2 = ⟨1, 1⟩ := by decide
```

これは

$$
\varphi^2=\varphi+1
$$

を具体座標 `⟨1,1⟩` として unit representative table に固定し、sector index `2` の後続 arithmetic へ渡す theorem である。
