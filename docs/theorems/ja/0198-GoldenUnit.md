# 0198 — `GoldenUnit`

## Lean の型

```lean
/-- A two-sided unit in the coordinate order.  Later theorems identify this predicate
with Mathlib's `IsUnit` and with norm `±1`. -/
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧ goldenMul eta epsilon = goldenOne
```

これは theorem ではなく `def` であり、黄金整数 `epsilon` が両側逆元を持つことを表す専用 predicate を定義する。

## 数学的主張・宣言の意味

`GoldenUnit ε` は、ある黄金整数 `η` が存在して

$$
\varepsilon\eta=1,
\qquad
\eta\varepsilon=1
$$

を同時に満たすことを意味する。

したがって数学的には、`ε` が環 $\mathbb Z[\varphi]$ の単元であることを raw coordinate API で表した定義である。

`GoldenInt` はすでに可換環として構成されているため、可換環では片側逆元があればもう片側も従う。しかし本定義では両側の積を明示的に要求している。これは一般の monoid 的な unit 定義に近い形を保ちつつ、`goldenMul` と `goldenOne` だけで意味が読めるようにした設計と解釈できる。

## 証明全体での役割

0187–0197 では黄金整数の整除、共役、ノルム、冪の互換性を整備した。本定義からは、そのノルム情報を単元性へ変換するブロックに入る。

直後の source では、

- `goldenUnit_of_norm_eq_one`
- `goldenUnit_of_norm_eq_neg_one`
- `goldenUnit_of_norm_eq_one_or_neg_one`
- `goldenNorm_eq_one_or_neg_one_of_unit`

が続き、最終的に

$$
GoldenUnit(x)
\iff
N(x)=1\ \text{or}\ N(x)=-1
$$

という黄金整数環における標準的な unit criterion を構成する。

さらに `goldenUnit_phi`、`goldenUnit_one`、`goldenUnit_neg`、`goldenUnit_mul`、`goldenUnit_pow` を通じて単元性の閉性を整備し、最後に `GoldenRelPrime` が

```lean
def GoldenRelPrime (x y : GoldenInt) : Prop :=
  ∀ d : GoldenInt, GoldenDivides d x → GoldenDivides d y → GoldenUnit d
```

として定義される。したがって `GoldenUnit` は「共通因子がすべて単元である」という Bézout-free な相対素性の基礎語彙になる。

## 直接依存する定義・補題

本宣言は定義なので theorem への直接依存はない。直接必要なのは次の定義である。

- `GoldenInt`
- 0124 `goldenMul`
- `goldenOne`
- existential proposition `∃`

概念的には

$$
\texttt{GoldenInt}
+\texttt{goldenMul}
+\texttt{goldenOne}
\longrightarrow
\texttt{GoldenUnit}
$$

である。

後続 theorem では 0176 `golden_mul_conj` と norm 計算が、本定義の witness `eta` を具体的に構成するために使われる。

## 構築の流れ

定義は次の二段階を一つの existential にまとめている。

```lean
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧ goldenMul eta epsilon = goldenOne
```

1. 逆元候補 `eta : GoldenInt` の存在を要求する。
2. `epsilon * eta = 1` と `eta * epsilon = 1` の両方を要求する。

仮定

```lean
h : GoldenUnit epsilon
```

を使う側では、

```lean
rcases h with ⟨eta, hleft, hright⟩
```

のように witness と両側逆元等式を取り出せる。

## Lean 固有の処理

`GoldenUnit epsilon : Prop` は structure ではなく existential proposition なので、unit witness 自体を data として保持する型ではない。必要なときに proof から `eta` を取り出す形式である。

また statement は標準乗法 `*` ではなく raw `goldenMul`、標準 `1` ではなく raw `goldenOne` を使う。`GoldenInt` では両者が typeclass instance と definitionally 接続されているため、Mathlib の標準 algebra API との橋渡しは軽い `simpa` や `change` で行える。

コメントには後続 theorem が Mathlib の `IsUnit` と結びつける意図が記されているが、今回確認した source 近傍では、まず norm `±1` との同値化が直接展開されている。

## 冗長・重複箇所

`GoldenUnit` は Mathlib 標準の `IsUnit epsilon` と数学的には重複する domain-specific wrapper である。

一方で、本開発では explicit coordinate API を先に構築しており、`goldenMul` と `goldenOne` だけで単元性を記述できる利点がある。また `GoldenRelPrime` の定義を「すべての共通黄金因子が `GoldenUnit`」と読めるため、FLT5 の証明監査では domain-specific な名前が意味を明示する。

さらに可換環である以上、両側逆元条件は論理的には片側だけでも十分である。その意味でも定義は一般性・明示性を優先した冗長さを持つ。

## 最適化候補

1. **現行 wrapper を維持する**
   - raw coordinate layer の監査性と theorem 名の読みやすさを優先できる。

2. **標準 `IsUnit` へ統一する**
   - Mathlib の unit API を直接利用でき、専用 theorem 群の一部を generic lemma に置換できる可能性がある。

3. **`GoldenUnit` を `IsUnit` の alias / bridge として薄くする**
   - domain-specific 名を残しつつ、実装を標準 API 側へ寄せる設計。

4. **片側逆元だけで定義する**
   - `CommRing GoldenInt` を前提にすれば短くできるが、raw API としての対称性は失われる。

5. **unit witness を structure として保持する**
   - inverse と証明を data として再利用する必要が増えるなら候補だが、現状の Prop-based API では過剰設計になりやすい。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本定義単独で必要なのは、`GoldenInt`、`goldenMul`、`goldenOne` と基本的な existential syntax だけであり、高度な tactic や number-theory import は不要である。

ただし同じ `GoldenDivisibility` section では `IsUnit`、整数ノルム、整除、`norm_num`、`simp` などを広く使うため、module 全体の最小 import は本定義単独より大きい。今回は Lean build を行わないため、正確な最小 import 集合は未検証である。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 `GoldenUnit` existential wrapper
- B: Mathlib 標準 `IsUnit` のみを使用
- C: `GoldenUnit := IsUnit` に近い薄い alias + domain-specific theorem 名
- D: inverse witness を保持する structure
- E: 片側逆元のみを要求する定義

比較軸は、downstream theorem の行数、Mathlib 標準 API の再利用度、raw / standard algebra layer の露出、証明監査性、witness の取り扱いやすさ、refactor 耐性である。

特に A と B の比較は、`GoldenDivides` と同様に「domain-specific wrapper が FLT5 証明の可読性にどれだけ寄与するか」を測る良い Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

正本 source では 0197 `goldenNorm_pow` の直後に本定義が置かれ、その直後に `goldenUnit_of_norm_eq_one` が続く。

対象ブランチには `docs/pdf/FLT5-main-ja-v0-r1.pdf` と `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし本定義に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0199 `goldenUnit_of_norm_eq_one`** である。

```lean
theorem goldenUnit_of_norm_eq_one {x : GoldenInt} (h : goldenNorm x = 1) :
    GoldenUnit x := by
  refine ⟨goldenConj x, ?_, ?_⟩
  · simpa [h, goldenOfInt, goldenOne] using golden_mul_conj x
  · have hc : goldenMul (goldenConj x) x =
        goldenMul x (goldenConj x) := by
      change goldenConj x * x = x * goldenConj x
      exact mul_comm _ _
    rw [hc]
    simpa [h, goldenOfInt, goldenOne] using golden_mul_conj x
```

0198 で単元性を「両側逆元の存在」として定義した直後、0199 は `N(x)=1` なら共役 `goldenConj x` がその逆元になることを具体的に構成する。ここから norm `±1` と unit 性の対応が始まる。