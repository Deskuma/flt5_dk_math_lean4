# 0254 — `signedGoldenFifthPowerUpToUnitCore_of_coprimeFactor`

## Lean の型

```lean
/-- Any implementation of the generic coprime-factor theorem supplies the stripped
packet's unit-times-fifth-power representation. -/
theorem signedGoldenFifthPowerUpToUnitCore_of_coprimeFactor
    (hFactor : GoldenCoprimeFactorOfFifthPower) :
    SignedGoldenFifthPowerUpToUnitCore := by
  intro u v w p
  exact hFactor p.beta (goldenConj p.beta)
    (goldenOfInt (p.exceptional.powerSplit.b : ℤ))
    p.beta_relPrime_conj p.beta_mul_conj_eq_fifth
```

これは `theorem` である。

0253 `GoldenCoprimeFactorOfFifthPower` で抽象化した一般的な第五冪因子抽出 contract を、`SignedGoldenRamifierStrippedPacket` の `beta` とその共役に具体適用し、0239 以前から要求されている `SignedGoldenFifthPowerUpToUnitCore` を構成する adapter theorem になっている。

## 数学的主張

0253 の contract は、黄金整数 `x,y,z` が

$$
\operatorname{GoldenRelPrime}(x,y)
$$

かつ

$$
xy=z^5
$$

を満たすなら、ある単元 $\varepsilon$ と黄金整数 $\gamma$ が存在して

$$
x=\varepsilon\gamma^5
$$

と書ける、という主張であった。

本 theorem は stripped packet `p` に対して

$$
x:=\beta,
\qquad
y:=\overline{\beta},
\qquad
z:=\operatorname{goldenOfInt}(b)
$$

と代入する。

ここで上流から既に、

$$
\operatorname{GoldenRelPrime}(\beta,\overline{\beta})
$$

と

$$
\beta\overline{\beta}
=
(\operatorname{goldenOfInt}b)^5
$$

が証明済みである。したがって `hFactor` を適用すれば

$$
\exists \varepsilon,\gamma,
\quad
\operatorname{GoldenUnit}(\varepsilon)
\land
\beta=\varepsilon\gamma^5
$$

を得る。

これはまさに `SignedGoldenFifthPowerUpToUnitCore` の要求そのものである。

## 証明全体での役割

0241–0244 では `beta` と `goldenConj beta` の相対素性を確立した。0251–0252 ではその積が埋め込まれた整数 `b` の第五冪であることを確立した。0253 は、この二つの入力から一方の因子が unit を除いて第五冪になるという一般代数 contract を切り出した。

0254 はそれら三層を接続する。

$$
\text{stripped packet}
\Longrightarrow
\begin{cases}
\operatorname{RelPrime}(\beta,\overline{\beta}),\\
\beta\overline{\beta}=z^5
\end{cases}
\Longrightarrow
\beta=\varepsilon\gamma^5.
$$

このため、本 theorem 自体には新しい数論計算はないが、FLT5 固有 packet arithmetic と一般 gcd/UFD 型因子抽出 theorem の境界を閉じる重要な integration point である。

後段では `GoldenCoprimeFactor.lean` が `GoldenCoprimeFactorOfFifthPower` の具体実装を与えるため、その theorem を本 adapter に渡すだけで `SignedGoldenFifthPowerUpToUnitCore` が得られる。

## 直接依存する定義・補題

直接利用するものは次の通り。

- 0253 `GoldenCoprimeFactorOfFifthPower`
- 0240 `SignedGoldenFifthPowerUpToUnitCore`
- `SignedGoldenRamifierStrippedPacket`
- 0244 `SignedGoldenRamifierStrippedPacket.beta_relPrime_conj`
- 0252 `SignedGoldenRamifierStrippedPacket.beta_mul_conj_eq_fifth`
- `goldenConj`
- `goldenOfInt`

proof の本質は、0253 の関数型 contract に必要な引数を順に供給するだけである。

概念的には、

$$
hFactor
+
\operatorname{RelPrime}(\beta,\overline{\beta})
+
\beta\overline{\beta}=z^5
\Longrightarrow
\beta=\varepsilon\gamma^5.
$$

## 証明の流れ

proof は極めて短い。

```lean
by
  intro u v w p
  exact hFactor p.beta (goldenConj p.beta)
    (goldenOfInt (p.exceptional.powerSplit.b : ℤ))
    p.beta_relPrime_conj p.beta_mul_conj_eq_fifth
```

1. `SignedGoldenFifthPowerUpToUnitCore` を展開した結果として、任意の `u v w` と stripped packet `p` を受け取る。
2. `hFactor` の `x` に `p.beta` を与える。
3. `y` に `goldenConj p.beta` を与える。
4. `z` に `goldenOfInt (p.exceptional.powerSplit.b : ℤ)` を与える。
5. coprimality hypothesis として `p.beta_relPrime_conj` を与える。
6. product-is-fifth-power hypothesis として `p.beta_mul_conj_eq_fifth` を与える。
7. `hFactor` の結論がそのまま `SignedGoldenFifthPowerUpToUnitCore` の結論になる。

したがって `rw`、`simp`、`ring`、`norm_num` は不要である。

## Lean 固有の処理

`SignedGoldenFifthPowerUpToUnitCore` は `abbrev : Prop` なので、`intro u v w p` によって透明に展開され、通常の関数型として扱われる。

同様に `GoldenCoprimeFactorOfFifthPower` も `abbrev : Prop` なので、`hFactor` は theorem 名ではなく関数値として直接適用できる。

```lean
hFactor p.beta (goldenConj p.beta)
  (goldenOfInt ...)
  p.beta_relPrime_conj
  p.beta_mul_conj_eq_fifth
```

という形は、Lean の dependent field projection と transparent abbreviation がうまく噛み合った例である。

また `(p.exceptional.powerSplit.b : ℤ)` では、packet 内の自然数 `b` を整数へ coercion し、その後 `goldenOfInt` で `GoldenInt` へ埋め込んでいる。

## 冗長・重複箇所

論理的には本 theorem は非常に薄い adapter であり、consumer が直接

```lean
hFactor p.beta (goldenConj p.beta)
  (goldenOfInt ...)
  p.beta_relPrime_conj p.beta_mul_conj_eq_fifth
```

と書けば同じ結果を得られる。

しかし named theorem として置く価値は明確である。

- FLT5 固有 packet から generic factor theorem への接続点を一名で参照できる。
- downstream は `beta_relPrime_conj` や `beta_mul_conj_eq_fifth` の provenance を知らずに済む。
- 0253 の具体実装を gcd、UFD、valuation 等で差し替えても consumer interface を保てる。
- proof graph 上で「一般因子抽出 contract が stripped core を満たす」という依存関係が明示される。

したがってこれは意図的な API-level redundancy と見るのが妥当である。

## 最適化候補

1. **現行 adapter theorem を維持する**
   - module boundary が最も読みやすい。

2. **`simpa` 形式へする**
   - 結論型が完全に一致するため、型推論次第ではより短い書き方も考えられるが、現行 `exact` は既に十分明瞭である。

3. **packet 専用 helper method にする**
   - `p.fifthPowerUpToUnit hFactor` のような namespace method にすれば consumer code はさらに短くできる。

4. **0253 を一般 `Associated` theorem にする**
   - その場合、本 adapter で `Associated` から具体 unit witness を取り出す処理が必要になる。

5. **generic factor theorem の具体実装を直接呼ぶ**
   - 層は減るが、dependency inversion が失われるため現行設計の方が module 分離には優れる。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem 自体は tactic を実質的に使用せず、必要な表面は上流の黄金整数 API と packet theorem のみである。

- `SignedGoldenFifthPowerUpToUnitCore`
- `GoldenCoprimeFactorOfFifthPower`
- `goldenConj`
- `goldenOfInt`
- packet projection theorem 群

一方、`GoldenCoprimeFactorOfFifthPower` の具体実装は後段 `GoldenCoprimeFactor.lean` で gcd / `IsUnit` / associated-power API を利用するため、module 全体としての最小 import は本 theorem 単独より広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証である。

## Comparator challenge 化の可否

適している。proof 自体ではなく **adapter architecture** の比較に向く。

候補は次の通り。

- A: 現行 contract injection + thin adapter
- B: generic theorem を直接 downstream から呼ぶ設計
- C: packet namespace method として factor extraction を提供する設計
- D: `Associated` ベースの generic theorem + witness recovery adapter
- E: exponent-generalized contract を `n=5` で特殊化する設計

比較軸は、依存方向、consumer の簡潔さ、generic theorem の差し替え容易性、witness の取り出しやすさ、型推論負荷、standalone 監査性である。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenFifthPower.lean` generated section である。

正本 source では、0253 `GoldenCoprimeFactorOfFifthPower` の直後に本 theorem が置かれ、本 theorem の直後で `SignedGoldenFifthPower.lean` が終了する。

standalone artifact は `import Mathlib` を使用している。

対象ブランチには `docs/pdf/FLT5-main-ja-v0-r1.pdf` と `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は、次 module `GoldenFifthPowerCoordinates.lean` の先頭宣言 **0255 `goldenFifthFstPoly`** である。

```lean
def goldenFifthFstPoly (p q : ℤ) : ℤ :=
  p ^ 5 + 10 * p ^ 3 * q ^ 2 + 10 * p ^ 2 * q ^ 3 +
    10 * p * q ^ 4 + 3 * q ^ 5
```

0254 で `beta = epsilon * gamma^5` という抽象的な fifth-power extraction が consumer contract として完成した。0255 からは `gamma = p + qφ` の第五冪を具体的な二座標多項式へ展開し、unit class ごとの arithmetic sector を解析する段階へ進む。
