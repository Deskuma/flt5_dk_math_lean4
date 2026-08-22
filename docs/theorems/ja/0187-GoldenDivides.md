# 0187 — `GoldenDivides`

## Lean の型

```lean
/-- Explicit golden divisibility, definitionally compatible with ring divisibility. -/
def GoldenDivides (d x : GoldenInt) : Prop :=
  ∃ q : GoldenInt, x = goldenMul d q
```

これは `theorem` ではなく `def` であり、黄金整数環 `GoldenInt` における整除関係を、明示的な商 `q` の存在として定義する。

## 数学的主張・宣言の意味

`GoldenDivides d x` は

$$
d\mid x
$$

を黄金整数の raw API で表したものであり、定義そのものは

$$
\exists q\in\mathbb Z[\varphi],\quad x=dq
$$

である。

Lean では標準の環整除 `d ∣ x` も同様に「ある商が存在して `x = d * q`」という意味を持つが、本定義では乗法を標準記法 `*` ではなく raw operation `goldenMul` で固定している。

したがって `GoldenDivides` は新しい数論的概念を導入するというより、FLT5 黄金整数部分の明示座標 API と Mathlib 標準 algebra API の間に置かれた、監査しやすい整除インターフェースである。

## 証明全体での役割

0186 `exists_goldenTau_factor_of_five_dvd` では、整数条件

$$
5\mid 2M+N
$$

から具体的な `beta` を構成し、

$$
M+N\varphi=\tau\beta
$$

を得た。0187 はその直後、module `GoldenDivisibility.lean` の入口で、こうした「黄金整数が黄金整数を因子として持つ」という関係を一般概念として名前付けする。

ここから source では、

- `goldenDivides_iff_dvd`
- `goldenDivides_refl`
- `goldenDivides_trans`
- `goldenDivides_sub`
- `goldenNorm_dvd_of_goldenDivides`

と、整除の基本 API が順に整備される。

特に後段の relative-primality 証明では、共通因子 `d` に対して

```lean
have hddiff : GoldenDivides d (p.beta - goldenConj p.beta) :=
  goldenDivides_sub hdbeta hdconj
```

のように使用され、さらに `goldenNorm_dvd_of_goldenDivides` で黄金整数の整除を整数ノルムの整除へ送る。最終的には `GoldenRelPrime` が

```lean
def GoldenRelPrime (x y : GoldenInt) : Prop :=
  ∀ d : GoldenInt, GoldenDivides d x → GoldenDivides d y → GoldenUnit d
```

として定義されるため、`GoldenDivides` は後続の共役因子の互いに素性を支える基礎語彙になる。

## 直接依存する定義・補題

直接依存する定義は非常に少ない。

- `GoldenInt`
- 0124 `goldenMul`
- Lean の existential proposition `∃`

定義なので proof script はなく、既存 theorem への直接依存もない。

概念的な依存は

$$
\texttt{GoldenInt}
+\texttt{goldenMul}
\longrightarrow
\texttt{GoldenDivides}
$$

である。

直後の `goldenDivides_iff_dvd` により、標準の `Dvd.dvd` と同値であることが証明される。

## 構築の流れ

定義は一段だけである。

```lean
def GoldenDivides (d x : GoldenInt) : Prop :=
  ∃ q : GoldenInt, x = goldenMul d q
```

1. `d` を候補因子、`x` を被整除元として受け取る。
2. `GoldenInt` 型の商 `q` の存在を要求する。
3. `x` が `goldenMul d q` と一致することを要求する。

数学的には通常の整除の定義そのものであり、違いは乗法を `GoldenInt` の raw coordinate multiplication で明示している点にある。

## Lean 固有の処理

`GoldenDivides d x` の値域は `Prop` なので、これは計算データではなく命題である。

`∃ q : GoldenInt, ...` という existential 定義にしているため、仮定

```lean
h : GoldenDivides d x
```

は後続で

```lean
rcases h with ⟨q, hq⟩
```

のように分解し、実際の商 `q` と factorization equality を取り出せる。

また `goldenMul` は既に `Mul GoldenInt` instance と definitionally 接続されているため、直後の

```lean
theorem goldenDivides_iff_dvd {d x : GoldenInt} :
    GoldenDivides d x ↔ d ∣ x := by
  constructor <;> rintro ⟨q, hq⟩
  · exact ⟨q, by simpa using hq⟩
  · exact ⟨q, by simpa using hq⟩
```

では `simpa` だけで raw 整除と標準整除を往復できる。

この definitional compatibility が本定義の設計上の重要点である。

## 冗長・重複箇所

`GoldenDivides` は Mathlib 標準の `d ∣ x` と数学的には重複している。直後に完全同値 `goldenDivides_iff_dvd` が証明されるため、論理的な表現力は増えていない。

それでも専用名を置く利点はある。

- raw `goldenMul` 層だけでも整除を記述できる。
- FLT5 の黄金整数部分で「どの整除概念を使っているか」が theorem 名から明示される。
- downstream の Bézout-free / norm-based argument を、一般 `dvd` より domain-specific な語彙で読める。
- Mathlib のより強い Euclidean-domain structure を構築する前から整除 API を利用できる。

一方、`GoldenInt` が既に `CommRing`、`IsDomain` を持つ段階まで来ているため、標準 `∣` のみで統一する設計も十分可能である。

## 最適化候補

1. **現行の domain-specific wrapper を維持する**
   - 数学監査では意味が読みやすく、raw API と標準 API の橋も明瞭。

2. **`GoldenDivides` を削除し標準 `∣` に統一する**
   - wrapper theorem 群 `goldenDivides_refl/trans/sub` も標準 lemma へ置換でき、コード量を減らせる。

3. **notation を導入する**
   - 専用記法を導入すれば読みやすくなる可能性があるが、標準 `∣` と競合しやすく推奨度は低い。

4. **構造構築前の bootstrap API として配置理由を明記する**
   - 今後 module 分割を変えるなら、なぜ標準 `dvd` だけではなく wrapper を残すのかコメントで明文化すると監査性が上がる。

現状では `goldenDivides_iff_dvd` が直後にあり、標準 API との相互運用性が十分確保されているため、実装上の問題は小さい。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本定義そのものが要求するものは、実質的には

- `GoldenInt`
- `goldenMul`
- 基本的な `Prop` / existential syntax

だけであり、高度な Mathlib theorem や tactic は不要である。

ただし同じ `GoldenDivisibility.lean` では直後から標準整除 lemma、整数整除、ノルム、単元関連の theorem を利用するため、module 全体の最小 import は本定義単独より広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は明快である。

- A: 現行 `GoldenDivides` wrapper + bridge theorem
- B: 標準 `d ∣ x` のみを使用
- C: raw coordinate factorization を theorem ごとに existential で直接書く
- D: `EuclideanDomain GoldenInt` 構築後の gcd / associated API を中心に再設計

比較軸は、

- downstream theorem の行数
- theorem 名からの意味の読みやすさ
- typeclass dependency depth
- Euclidean-domain 構築前に利用できるか
- `simp` / rewrite の負担
- Mathlib 標準 API との相互運用性

である。

特に A と B の比較は、「domain-specific wrapper が証明監査にどれだけ価値を持つか」を測る良い Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

source の冒頭コメントでは、この module が黄金整数の divisibility / unit / relative primality を扱い、共役因子分解に必要な「すべての共通因子が unit」という Bézout-free な表現を提供すると説明されている。

対象ブランチには日本語・英語 PDF も存在するが、本定義に対応する具体的なページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0188 `goldenDivides_iff_dvd`** である。

```lean
theorem goldenDivides_iff_dvd {d x : GoldenInt} : GoldenDivides d x ↔ d ∣ x := by
  constructor <;> rintro ⟨q, hq⟩
  · exact ⟨q, by simpa using hq⟩
  · exact ⟨q, by simpa using hq⟩
```

0187 が domain-specific な raw divisibility を定義した直後、0188 はそれが Mathlib 標準の ring divisibility と完全に同値であることを確立する。ここから reflexivity・transitivity・subtraction closure を標準 `dvd` API から再利用できるようになる。