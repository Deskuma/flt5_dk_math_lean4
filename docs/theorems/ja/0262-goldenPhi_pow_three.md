# 0262 — `goldenPhi_pow_three`

## Lean の型

```lean
theorem goldenPhi_pow_three :
    goldenPow goldenPhi 3 = ⟨1, 2⟩ := by
  decide
```

これは `theorem` であり、黄金整数の基底元 `goldenPhi` の 3 乗が具体座標 `⟨1,2⟩` に等しいことを示す。

## 数学的主張

黄金比の基底元を $\varphi$ とし、基本関係

$$
\varphi^2=\varphi+1
$$

を使うと、

$$
\varphi^3
=\varphi(\varphi+1)
=\varphi^2+\varphi
=1+2\varphi.
$$

したがって `GoldenInt` の座標表示では

$$
\varphi^3=\langle1,2\rangle.
$$

本 theorem は raw power `goldenPow goldenPhi 3` をこの具体座標へ落とす

$$
goldenPow(\varphi,3)=\langle1,2\rangle
$$

という finite unit-representative table の index `3` のエントリである。

## 証明全体での役割

`GoldenFifthPowerCoordinates.lean` では、第五冪までの unit class を扱うために

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

の五代表を具体座標として固定している。正本 source では次の順に並ぶ。

```lean
theorem goldenPhi_pow_zero : goldenPow goldenPhi 0 = ⟨1, 0⟩ := rfl
theorem goldenPhi_pow_one : goldenPow goldenPhi 1 = ⟨0, 1⟩ := by decide
theorem goldenPhi_pow_two : goldenPow goldenPhi 2 = ⟨1, 1⟩ := by decide
theorem goldenPhi_pow_three : goldenPow goldenPhi 3 = ⟨1, 2⟩ := by decide
theorem goldenPhi_pow_four : goldenPow goldenPhi 4 = ⟨2, 3⟩ := by decide
```

本 theorem はそのうち unit representative $\varphi^3$、すなわち sector index `3` を担当する。

直後の sector theorem `golden_unit_three_mul_fifth_snd` では、実際に

```lean
rw [goldenPhi_pow_three]
simp only [goldenMul]
rw [goldenPow_five_fst, goldenPow_five_snd]
ring
```

という流れで本 theorem が使われる。そこで得られる第二座標は

$$
2A(p,q)+3B(p,q),
$$

ただし

$$
A(p,q)=goldenFifthFstPoly(p,q),
$$

$$
B(p,q)=goldenFifthSndPoly(p,q)
$$

である。

なぜ係数が `2` と `3` になるかは、`goldenMul` の座標乗法と $\varphi^3=1+2\varphi$ を合わせれば分かる。`gamma^5 = A+B\varphi` と書くと、

$$
(1+2\varphi)(A+B\varphi)
$$

の $\varphi$ 座標は、$\varphi^2=1+\varphi$ を使って

$$
2A+3B
$$

となる。

したがって本 theorem は数学的には小さな closed identity だが、証明全体では **unit sector 3 の canonical representative を explicit coordinate に固定し、第五冪座標の算術 sector 解析へ接続する rewrite interface** である。

## 直接依存する定義・補題

直接依存する主な定義は次の通り。

- `GoldenInt`
- `goldenPhi`
- `goldenPow`
- `goldenMul`
- `goldenOne`

proof は `by decide` のみであり、0259–0261 の theorem 名を直接呼び出してはいない。

概念的には

$$
\varphi^3=\varphi\cdot\varphi^2
$$

を評価しているが、Lean 上では固定された `goldenPow goldenPhi 3` を定義計算し、具体構造体 `⟨1,2⟩` との equality を decidable computation で閉じている。

論理依存という意味では前の `goldenPhi_pow_two` は不要である。一方で proof architecture 上は 0259–0263 が一つの unit-representative table を構成している。

## 証明または構築の流れ

proof は

```lean
by
  decide
```

だけである。

概念的な評価は次の通り。

1. `goldenPow goldenPhi 3` を固定指数 3 で再帰評価する。
2. `goldenPhi` の座標 `⟨0,1⟩` を使う。
3. `goldenMul` の座標乗法を繰り返す。
4. 乗法定義に組み込まれた $\varphi^2=\varphi+1$ により結果を正規化する。
5. 左辺が具体座標 `⟨1,2⟩` に評価され、structure equality を `decide` が証明する。

数学的には

$$
\varphi^3
=\varphi(\varphi^2)
=\varphi(1+\varphi)
=1+2\varphi
$$

である。

## Lean 固有の処理

`decide` は目標命題の `Decidable` instance を実行し、真であると評価された命題の proof term を生成する。

今回の目標は変数を含まない閉じた equality なので、この方法と相性がよい。一般的な環論補題を適用する必要はなく、固定値の演算をそのまま評価できる。

また `GoldenInt` は整数座標を持つ structure なので、具体 term 同士の equality は最終的に整数座標の equality に還元できる。

一方、後続の `golden_unit_three_mul_fifth_snd` は変数 `gamma` を含むため `decide` だけでは閉じず、本 theorem で unit 側を具体化した後に `goldenPow_five_fst`、`goldenPow_five_snd`、`ring` を使う。この違いは、closed computation と symbolic polynomial proof の境界をよく表している。

## 冗長・重複箇所

数学的には本 theorem の情報は黄金比の二次関係から即座に導かれ、`goldenMul` の定義にも同じ構造が埋め込まれている。

したがって利用箇所で毎回

```lean
simp [goldenPow, goldenPhi, goldenMul, goldenOne]
```

などと展開しても、同じ具体座標を得られる可能性がある。

しかし named theorem として残す利点は明確である。

- unit sector `3` と座標 `⟨1,2⟩` の対応が source 上で明示される。
- downstream は `goldenPow` の再帰定義を知らず `rw [goldenPhi_pow_three]` だけでよい。
- 0259–0263 の五代表が対称な API になる。
- `goldenPow` の内部実装が変わっても、representative theorem を境界として downstream を保護できる。
- sector theorem の数式係数 `2,3` の由来を追跡しやすくなる。

よって論理情報としては重複するが、proof architecture 上は有用な重複である。

## 最適化候補

1. **現行の `by decide` を維持する**
   - 固定指数・固定要素の closed computation として非常に短い。
   - theorem 単体の保守性も高い。

2. **`simp` による explicit reduction と比較する**
   - `simp [goldenPow, goldenPhi, goldenMul, goldenOne]` 型の proof にすると、どの定義で座標が計算されたかが見える。
   - ただし実装詳細への依存は増える。

3. **直前 theorem から再帰的に導く**
   - `goldenPhi_pow_two` と `goldenMul` を使い、$\varphi^3=\varphi\cdot\varphi^2$ として証明する。
   - 数学的説明性は上がるが、closed computation より proof は長くなる。

4. **`Fin 5` の representative table を一括定義する**
   - `i : Fin 5` に対して $\varphi^i$ の座標を返す table を作り、0259–0263 を specialization にする。
   - unit class routing が増えるなら有力だが、五件だけなら現行の個別 theorem も十分明快である。

5. **Fibonacci 座標公式へ一般化する**
   - $\varphi^n$ は Fibonacci recurrence に従い、概念的には

$$
\varphi^n=F_{n-1}+F_n\varphi
$$

   と書ける。`n=3` なら $F_2=1,F_3=2$ から `⟨1,2⟩` が得られる。
   - ただし FLT5 で必要なのは mod fifth powers の五代表なので、一般化がこの局所 module に必要かは別問題である。

## 必要 Mathlib import と import 最適化候補

standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem 単独が直接必要とする Mathlib 側の機能は少なく、主に次の範囲である。

- `Decidable` equality と `decide`
- `GoldenInt` の座標に使う整数型の基礎
- 上流で定義された `goldenPhi`、`goldenPow`、`goldenMul`

本 theorem 自身は `ring`、`omega`、gcd、整除、valuation などを使用しない。

ただし同じ `GoldenFifthPowerCoordinates.lean` module では、第五冪の座標展開と sector arithmetic に `ring` が必要である。このため module 単位の最小 import は theorem 単体より広くなる。

今回は Lean build を行わないという制約があるため、`import Mathlib` をどこまで細分化できるかは実機検証していない。したがって import 最適化は候補としてのみ記録する。

## Comparator challenge 化の可否

本 theorem 単独では難度が低すぎるが、0259–0263 の representative block 全体なら Comparator challenge 化に向く。

比較候補は次の通り。

- A: 現行の `rfl` / `decide` による個別 closed computation
- B: `simp` で `goldenPow` と `goldenMul` を explicit 展開する proof
- C: 前指数の representative theorem から再帰的に導く proof
- D: Fibonacci 座標公式を一般証明して specialization する proof

評価軸としては、proof term の短さ、定義変更への耐性、数学的説明性、依存の浅さ、五つの sector theorem との接続の明瞭さが考えられる。

特に Comparator challenge としては、**局所的な closed computation を一般理論へ持ち上げることが本当に最適化なのか** を比較できる点が興味深い。

## PDF との対応

対象ブランチには次の PDF が存在する。

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

今回、0262 `goldenPhi_pow_three` に対応する具体的な PDF ページまたは節番号までは確認できていない。そのため PDF 上の位置を推測して引用することはしない。

技術的意味については、リポジトリ正本の Lean source にある `GoldenFifthPowerCoordinates.lean` の module コメントと、実際の `goldenPhi_pow_three`、`golden_unit_three_mul_fifth_snd` の依存関係を主根拠とした。

## 次に読むべき宣言

次は source 順に

```lean
theorem goldenPhi_pow_four :
    goldenPow goldenPhi 4 = ⟨2, 3⟩ := by
  decide
```

すなわち **0263 `goldenPhi_pow_four`** を読むべきである。

数学的には

$$
\varphi^4=2+3\varphi
$$

を具体座標 `⟨2,3⟩` として固定する theorem であり、これで

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

の五 unit representative table が完成する。その後 `golden_unit_zero_mul_fifth_snd` から、各 unit sector の第二座標を explicit polynomial として解析する段階へ進む。