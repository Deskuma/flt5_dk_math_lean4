# 0217 — `goldenQuotientNumerator_fst`

## Lean の型

```lean
theorem goldenQuotientNumerator_fst (x y : GoldenInt) :
    (goldenQuotientNumerator x y).fst =
      x.fst * (y.fst + y.snd) - x.snd * y.snd := by
  simp [goldenQuotientNumerator, goldenMul, goldenConj]
  ring
```

これは `theorem` であり、0216 `goldenQuotientNumerator` で定義した `x * conjugate(y)` の第一座標を、`x,y` の整数座標だけからなる明示式へ展開する。

## 数学的主張

`x=a+bφ`、`y=c+dφ` とする。0163 `goldenConj` により

$$
\overline y=(c+d)-d\varphi
$$

であり、黄金整数の乗法則

$$
(a+b\varphi)(e+f\varphi)=(ae+bf)+(af+be+bf)\varphi
$$

に `e=c+d`、`f=-d` を代入すると、第一座標は

$$
a(c+d)+b(-d)=a(c+d)-bd
$$

となる。本 theorem はこれを Lean 座標で

$$
(x\overline y).\mathrm{fst}
=x.\mathrm{fst}(y.\mathrm{fst}+y.\mathrm{snd})
-x.\mathrm{snd}\,y.\mathrm{snd}
$$

として公開する。

## 証明全体での役割

`GoldenEuclidean.lean` では非零 `y` に対する商を

$$
\frac{x\overline y}{N(y)}
$$

として有理座標へ移し、それを最近接整数へ丸めて Euclidean quotient を作る。0216 は分子 `x\overline y` を `GoldenInt` として固定したが、実際に `GoldenRat = ℚ × ℚ` へ移るには二つの整数座標を明示する必要がある。

0217 はその第一座標公式を与える。続く 0218 `goldenQuotientNumerator_snd` が第二座標を与え、この二本を `goldenQuotientCoords` が `goldenNorm y` で割ることで rational quotient coordinates を構成する。

後続の remainder identity では、これらの座標式を逆向きに利用して、`x - q*y` の rationalized error が quotient-coordinate rounding error と一致することを示す。したがって 0217 は単なる projection lemma ではなく、Euclidean remainder contraction の座標代数を固定する API の半分である。

## 直接依存する定義・補題

直接依存は次の定義である。

- 0216 `goldenQuotientNumerator`
- 0124 `goldenMul`
- 0163 `goldenConj`
- `GoldenInt`

証明 tactic として `simp` と `ring` を使う。新しい数論 lemma への依存はなく、raw coordinate definitions を展開した多項式恒等式として閉じる。

## 証明の流れ

```lean
simp [goldenQuotientNumerator, goldenMul, goldenConj]
ring
```

第一段階の `simp` で、

1. `goldenQuotientNumerator x y` を `goldenMul x (goldenConj y)` へ展開する。
2. `goldenConj y` を座標 `⟨y.fst + y.snd, -y.snd⟩` へ展開する。
3. `goldenMul` の第一座標を展開する。

この時点で目標は整数上の多項式等式へ還元される。最後の `ring` が加法・減法・符号の正規化を行って閉じる。

## Lean 固有の処理

本 theorem は `GoldenInt.ext` を使わず、結果の `.fst` だけを対象とする projection theorem なので、`simp` により第一座標だけを直接計算できる。

また右辺では標準整数演算を使う一方、左辺の内部は raw `goldenMul` / `goldenConj` API である。`simp` がこの表現境界を消し、`ring` が algebraic normal form の差を吸収する。

`ring` を最後に置く設計は、座標式の括弧や `-d` の展開順に proof を依存させないため頑健である。

## 冗長・重複箇所

0217 と続く 0218 は、同じ `goldenQuotientNumerator` を二座標へ射影する対の theorem であり、展開 pattern はほぼ共通する。

理論上は `goldenQuotientNumerator` 自体を明示座標 pair として定義すれば、この二本を `rfl` に近づけられる可能性がある。しかし現行方式では「共役を掛ける」という数学的定義を正本に保ち、必要な座標式を theorem として派生させているため、数学的 provenance は明瞭である。

## 最適化候補

1. `goldenQuotientNumerator` を標準 `x * goldenConj y` notation で定義し、raw/standard API 境界を減らす。
2. 0217・0218 を一つの pair equality theorem にまとめ、必要に応じて `.fst` / `.snd` を射影する。
3. quotient numerator の座標式を専用 structure / helper へまとめ、`goldenQuotientCoords` で重複展開を避ける。
4. 一般二次環の `x * conj y` 座標公式へ抽象化し、黄金整数を特殊化として扱う。
5. 現行の二本の projection theorem を維持し、downstream simp/rewrite の局所性を優先する。

現行方式は theorem の粒度が細かい代わりに、後続 proof から第一座標だけを明示的に参照できる利点がある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が直接必要とする Mathlib 表面は主に `simp` と `ring` であり、数学的 object は上流の `GoldenInt` API に依存する。

宣言単独なら `Mathlib` 全体より小さい import で足りる可能性が高いが、`GoldenEuclidean.lean` 全体では `round`、`abs_sub_round`、`nlinarith`、`linarith`、`field_simp`、Euclidean-domain API なども使う。今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は、現行の `simp + ring`、完全な `ring_nf` ベース、pair equality を一度証明して projection する方式、`goldenQuotientNumerator` を明示座標定義へ変更する方式、一般 quadratic-order abstraction である。

比較軸は proof 長、raw definition 変更への頑健性、数学的由来の見えやすさ、後続 rewrite usability、simp set への依存度である。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

リポジトリ正本では 0216 `goldenQuotientNumerator` が本 theorem を次宣言として明示し、その Lean 型と proof も記録している。対象ブランチには日本語・英語 PDF も存在するが、本 theorem に対応する具体的ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0218 `goldenQuotientNumerator_snd`** である。

0217 が `x * conjugate(y)` の第一座標を明示したので、0218 は第二座標

$$
(x\overline y).\mathrm{snd}=x.\mathrm{snd}\,y.\mathrm{fst}-x.\mathrm{fst}\,y.\mathrm{snd}
$$

を公開する。二座標が揃った後、`goldenQuotientCoords` がそれらを `N(y)` で割って実際の rational quotient coordinates を構成する段階へ進む。
