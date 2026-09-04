# 0259 — `goldenPhi_pow_zero`

## Lean の型

```lean
theorem goldenPhi_pow_zero : goldenPow goldenPhi 0 = ⟨1, 0⟩ := rfl
```

これは `theorem` であり、黄金整数の基底元 `goldenPhi` の 0 乗が、座標 `⟨1, 0⟩`、すなわち黄金整数環の乗法単位元 `1` に等しいことを示す。

## 数学的主張

数学的内容は通常の 0 乗則

$$
\varphi^0=1
$$

そのものである。

`GoldenInt` では元を

$$
a+b\varphi
$$

の座標 `⟨a,b⟩` として表すため、単位元 `1` は

$$
1=1+0\varphi
$$

に対応し、座標では `⟨1,0⟩` となる。

したがって本 theorem は

$$
goldenPow(\varphi,0)=\langle1,0\rangle
$$

を公開するだけの非常に小さな宣言である。

## 証明全体での役割

0255–0258 では、任意の黄金整数 `gamma = p + qφ` の第五冪を二つの明示多項式

$$
A(p,q),\qquad B(p,q)
$$

へ展開した。

0259 からは別の小ブロックに入り、unit representative

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

を raw power `goldenPow goldenPhi i` の具体座標として固定する。

正本 source では本 theorem の直後に

```lean
theorem goldenPhi_pow_one : goldenPow goldenPhi 1 = ⟨0, 1⟩ := by decide
theorem goldenPhi_pow_two : goldenPow goldenPhi 2 = ⟨1, 1⟩ := by decide
theorem goldenPhi_pow_three : goldenPow goldenPhi 3 = ⟨1, 2⟩ := by decide
theorem goldenPhi_pow_four : goldenPow goldenPhi 4 = ⟨2, 3⟩ := by decide
```

が続く。

これら五つの代表は、後続の unit-sector arithmetic で

$$
\varphi^i\gamma^5
$$

の第二座標を sector ごとに展開するために使われる。

特に本 theorem は zero sector、すなわち unit representative が `1 = φ^0` の場合を支える。後段 source では `golden_unit_zero_mul_fifth_snd` が最初に `rw [goldenPhi_pow_zero]` を行い、

$$
1\cdot\gamma^5=\gamma^5
$$

へ還元してから 0258 `goldenPow_five_snd` を適用している。

さらに後続の zero-sector inversion でも、unit index `i = 0` を確定した後に `goldenPhi_pow_zero` を用いて sector equation から純粋な第五冪 equation を取り出す。

したがって theorem 自体は自明でも、unit class decomposition の **zero representative を名前付き rewrite API にする** 役割を持つ。

## 直接依存する定義・補題

直接依存するものは非常に少ない。

- `GoldenInt`
- `goldenPhi`
- `goldenPow`
- `goldenOne` の定義内容
- `GoldenInt` の座標 constructor `⟨_, _⟩`

proof は `rfl` だけなので、named theorem や tactic への直接依存はない。

`goldenPow` は 0 乗で `goldenOne` を返す raw recursion として定義され、`goldenOne` は座標 `⟨1,0⟩` である。そのため両辺は定義展開だけで同一になる。

概念的には

$$
goldenPow\;goldenPhi\;0
\equiv goldenOne
\equiv\langle1,0\rangle
$$

という definitional equality である。

## 証明の流れ

proof は

```lean
:= rfl
```

だけで終わる。

Lean が確認しているのは、左辺 `goldenPow goldenPhi 0` を定義展開すると `goldenOne` になり、さらにその実装が右辺 `⟨1,0⟩` と定義的に一致することである。

数学的推論、帰納法、rewrite、算術 tactic は一切必要ない。

## Lean 固有の処理

ここで重要なのは、これは propositional proof を組み立てているのではなく **definitional equality** を利用していることである。

`rfl` が通るためには、elaborator が両辺を reduction したとき同じ term にならなければならない。

本 theorem は raw power API `goldenPow` を使っているため、その 0 ケースが definition equation として直接見える。一方、Mathlib 標準記法の

```lean
goldenPhi ^ 0 = 1
```

なら、一般的な `pow_zero` や simp API を使う書き方も可能である。

0160 `golden_pow_eq` により raw `goldenPow` と標準 `^` は既に接続されているが、本ブロックは unit representative の具体座標を直接扱うため raw API を維持している。

## 冗長・重複箇所

数学的には本 theorem は `goldenPow` の定義 equation そのものであり、情報量はほぼゼロである。

また `goldenOne` が既に `⟨1,0⟩` と定義されているため、必要な場所で `rfl` や `simp [goldenPow, goldenOne]` を使えば theorem を置かずに済む。

それでも named theorem として残す価値はある。

- `φ^0` という unit representative の意味が theorem 名で明示される。
- downstream が `goldenPow` の内部定義を知らずに `rw [goldenPhi_pow_zero]` できる。
- `goldenPhi_pow_one` から `goldenPhi_pow_four` までの五つの representative theorem と API が対称になる。
- `goldenPow` の実装を変更しても downstream の rewrite 名を維持できる。

したがって論理的には冗長だが、unit-sector API の整形としては有用な冗長性である。

## 最適化候補

1. **現行 theorem を維持する**
   - unit representative block の対称性と downstream rewrite の読みやすさを優先する。

2. **`@[simp]` を付ける**
   - `goldenPow goldenPhi 0` を頻繁に正規化するなら simp theorem 化が候補になる。
   - ただし raw `goldenPow` 自体の recursion equation が simp 可能なら重複するため、実際の simp set を Lean build で確認する必要がある。

3. **五つの `φ^i` theorem を一つの finite table API にまとめる**
   - `i : Fin 5` に対する代表座標関数を定義し、個別 theorem を projection / specialization にできる。

4. **標準冪 notation に統一する**
   - `goldenPhi ^ i` を canonical API にし、`golden_pow_eq` 経由で raw power を隠す設計も可能である。

5. **`goldenOne` を右辺に使う**
   - statement を `goldenPow goldenPhi 0 = goldenOne` とすれば抽象度は上がる。
   - 一方、現行の `⟨1,0⟩` は unit representative の座標を即座に可視化する利点がある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem 単独では外部 tactic は一切使わず、必要なのは `GoldenInt`、`goldenPow`、`goldenPhi` とそれらの基礎定義だけである。そのため宣言単独の Mathlib 依存は極めて小さい。

ただし同じ `GoldenFifthPowerCoordinates.lean` module では、後続に `decide`、`ring`、整除、`Fin 5`、`fin_cases`、`omega` 等を使う theorem が並ぶため、module 全体の最小 import は本 theorem 単独より広い。

今回は Lean build を行わないので、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

単独 theorem としては簡単すぎるが、unit representative block 全体を対象にすれば Comparator challenge に適している。

比較候補は次の通り。

- A: 現行の `goldenPhi_pow_zero` ～ `goldenPhi_pow_four` を個別 theorem とする
- B: `Fin 5` の代表座標 table を一つ定義して個別 theorem を導く
- C: 標準 `^` と一般 Fibonacci 型 recurrence から `φ^i` の座標を導く
- D: `decide` / `norm_num` / `simp` / `rfl` の proof style を各指数で比較する

比較軸は API の単純さ、proof 重複、downstream rewrite usability、raw / standard power API の境界、拡張性である。

0259 単独なら `rfl` が最小であり、これ以上の proof 最適化余地はほぼない。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenFifthPowerCoordinates.lean` generated section である。

正本 source では 0258 `goldenPow_five_snd` の直後に本 theorem が置かれ、その直後に `goldenPhi_pow_one`、`goldenPhi_pow_two`、`goldenPhi_pow_three`、`goldenPhi_pow_four` が続く。

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的な PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0260 `goldenPhi_pow_one`** である。

```lean
theorem goldenPhi_pow_one : goldenPow goldenPhi 1 = ⟨0, 1⟩ := by decide
```

0259 が unit representative `1 = φ^0` を固定したので、0260 は `φ` 自身の座標 `⟨0,1⟩` を固定する。そこから `φ^2`, `φ^3`, `φ^4` の具体座標へ進み、五つの unit sector representative が揃う。