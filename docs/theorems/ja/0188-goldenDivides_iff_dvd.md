# 0188 — `goldenDivides_iff_dvd`

## Lean の型

```lean
theorem goldenDivides_iff_dvd {d x : GoldenInt} : GoldenDivides d x ↔ d ∣ x := by
  constructor <;> rintro ⟨q, hq⟩
  · exact ⟨q, by simpa using hq⟩
  · exact ⟨q, by simpa using hq⟩
```

これは `theorem` であり、0187 で定義した黄金整数専用の整除関係 `GoldenDivides` と、Lean / Mathlib 標準の整除記法 `d ∣ x` が完全に同値であることを示す。

## 数学的主張

0187 の定義は

```lean
def GoldenDivides (d x : GoldenInt) : Prop :=
  ∃ q : GoldenInt, x = goldenMul d q
```

である。一方、標準の環整除 `d ∣ x` も

$$
\exists q,\quad x=dq
$$

という商の存在で表される。

したがって本 theorem の数学的内容は

$$
\mathrm{GoldenDivides}(d,x)
\iff
d\mid x
$$

であり、raw operation `goldenMul` で記述した局所 API と、`Mul GoldenInt` instance を通した標準 `*` による Mathlib API が同じ整除概念を表すことを保証する。

新しい整除理論を作る theorem ではなく、同じ数学を二つの表現層の間で往復可能にする **representation bridge** である。

## 証明全体での役割

`GoldenDivisibility.lean` は 0187 `GoldenDivides` で domain-specific な整除語彙を導入するが、そのまま独自 API を孤立させない。本 0188 を直後に置くことで、Mathlib が既に持つ整除の一般 theorem をすぐ再利用できるようにしている。

実際、直後の source は

```lean
theorem goldenDivides_refl (x : GoldenInt) : GoldenDivides x x := by
  rw [goldenDivides_iff_dvd]

 theorem goldenDivides_trans {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hxy : GoldenDivides x y) :
    GoldenDivides d y := by
  rw [goldenDivides_iff_dvd] at hdx hxy ⊢
  exact dvd_trans hdx hxy

 theorem goldenDivides_sub {d x y : GoldenInt}
    (hdx : GoldenDivides d x) (hdy : GoldenDivides d y) :
    GoldenDivides d (x - y) := by
  rw [goldenDivides_iff_dvd] at hdx hdy ⊢
  exact dvd_sub hdx hdy
```

という構造になっている。

つまり本 theorem があることで、専用語彙 `GoldenDivides` の読みやすさを保ったまま、反射性・推移性・差に対する閉性を Mathlib 標準 `dvd` API へ委譲できる。

さらに後段の `GoldenCoprimeFactor.lean` では、`GCDMonoid GoldenInt` の標準 gcd theorem

```lean
exact gcd_dvd_left x y
exact gcd_dvd_right x y
```

を `rw [←/→ goldenDivides_iff_dvd]` によって `GoldenRelPrime` 側へ接続している。したがって 0188 は、初期の explicit-coordinate divisibility と、後に構築される Euclidean-domain / gcd machinery の間をつなぐ長距離 bridge でもある。

## 直接依存する定義・補題

直接依存は次の通りである。

- 0187 `GoldenDivides`
- `GoldenInt`
- 0124 `goldenMul`
- `Mul GoldenInt` instance
- Lean / Mathlib 標準の `Dvd.dvd`

proof script では named theorem を明示的に呼ばず、両側の existential witness を分解して `simpa` で factorization equality を移している。

`goldenMul` と標準 `*` は既に同じ乗法へ接続されているため、概念的依存は

$$
\texttt{GoldenDivides}
+\texttt{Mul GoldenInt}
\longrightarrow
\texttt{goldenDivides\_iff\_dvd}
$$

である。

## 証明の流れ

証明は完全に対称である。

```lean
constructor <;> rintro ⟨q, hq⟩
```

で `↔` を二方向に分け、それぞれの側の existential witness `q` と factorization equality `hq` を取り出す。

### `GoldenDivides d x → d ∣ x`

仮定から

$$
x=goldenMul\ d\ q
$$

を得る。標準整除の witness として同じ `q` を返し、

```lean
exact ⟨q, by simpa using hq⟩
```

で `goldenMul d q` を標準乗法 `d * q` と同一視する。

### `d ∣ x → GoldenDivides d x`

標準整除から同じ形の witness `q` を取り出し、同じく

```lean
exact ⟨q, by simpa using hq⟩
```

で raw multiplication 側へ戻す。

両方向の proof term が同形であること自体が、二つの整除表現の差がほぼ notation / API layer だけであることを示している。

## Lean 固有の処理

この theorem で重要なのは `constructor <;> rintro ⟨q, hq⟩` と `simpa` の組み合わせである。

`constructor` は `P ↔ Q` を

```lean
P → Q
Q → P
```

の二ゴールへ分解する。`<;>` によって後続の `rintro ⟨q, hq⟩` を両ゴールへ適用し、どちらの existential proposition からも witness を同じ形で取り出している。

`simpa using hq` は、factorization equality の raw / standard multiplication の表現差を simp 正規化で吸収する。上流には

```lean
@[simp] theorem golden_mul_eq (x y : GoldenInt) :
    goldenMul x y = x * y := rfl
```

もあり、さらに `Mul GoldenInt` 自体が `goldenMul` を登録しているため、この bridge は非常に薄い。

この薄さこそ設計上の検査点であり、もし `simpa` が大量の補題を必要としたなら raw API と標準 API のずれを疑うべきところである。

## 冗長・重複箇所

本 theorem 自体が示す通り、`GoldenDivides` と標準 `∣` は論理的に同じである。そのため API 全体としては意図的な重複がある。

さらに proof の二方向は完全に対称で、コードも同じ

```lean
exact ⟨q, by simpa using hq⟩
```

を二度書いている。

ただしこの重複は小さく、`↔` の左右を明示するため可読性は高い。tactic golf で一行に圧縮しても数学的価値は増えない。

より大きな重複は、0188 以後に `goldenDivides_refl/trans/sub` の wrapper theorem を個別に置いている点である。標準 `dvd` だけを使えば不要だが、domain-specific theorem 名を残すことで FLT5 の証明を黄金整数語彙のまま読める利点がある。

## 最適化候補

1. **現行 bridge を維持する**
   - domain-specific API と Mathlib 標準 API の相互運用点が一箇所に明示される。

2. **`GoldenDivides` 自体を標準 `∣` の abbrev に寄せる**
   - 例えば概念上 `abbrev GoldenDivides (d x) := d ∣ x` とすれば bridge theorem は不要になる。
   - ただし raw `goldenMul` から始める監査可能性は薄れる。

3. **wrapper theorem 群を減らす**
   - `goldenDivides_refl/trans/sub` を標準 theorem の直接利用へ置換できる。
   - downstream の theorem 名の可読性との trade-off がある。

4. **bridge を simp theorem として扱うか検討する**
   - `↔` theorem に `[simp]` を付ければ自動的に標準 `dvd` へ正規化できる可能性がある。
   - ただし proposition-level rewrite が広範囲に走るため、simp normal form と証明の透明性を確認してから採用すべきである。

現行は explicit wrapper を残しつつ、必要な場所だけ `rw [goldenDivides_iff_dvd]` する保守的で監査しやすい設計である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem 単独で必要な表面は小さい。

- `GoldenInt` / `GoldenDivides`
- 標準 `Dvd` relation と `∣` notation
- `constructor`, `rintro`, `simpa` が利用できる tactic environment
- `Mul GoldenInt` の instance

`dvd_trans` や `dvd_sub` は本 theorem 自身では使わず、直後の theorem 群で使われる。

Mathlib の細粒度 import 名については今回 Lean build を行わないため確定しない。`Mathlib` 全体 import から algebraic divisibility と basic tactic 群へ縮小できる可能性は高いが、正確な最小集合は未検証の最適化候補である。

## Comparator challenge 化の可否

適している。比較対象は次のように構成できる。

- A: 現行 `GoldenDivides` + `goldenDivides_iff_dvd`
- B: `GoldenDivides` を廃止して標準 `∣` のみ使用
- C: `GoldenDivides` を `abbrev` として標準 `∣` に直接定義
- D: 現行 wrapper を維持し、本 bridge に `[simp]` を付けて自動正規化

比較軸は、

- downstream の theorem 行数
- simp の安定性
- raw coordinate layer の監査可能性
- Mathlib API との相互運用性
- EuclideanDomain / GCDMonoid 構築後の proof burden
- theorem 名から読み取れる domain semantics

である。

特に A と B は、「専用 API 層が数学監査の読みやすさにどれだけ寄与するか」を測る良い比較になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

source では

```lean
def GoldenDivides (d x : GoldenInt) : Prop :=
  ∃ q : GoldenInt, x = goldenMul d q

theorem goldenDivides_iff_dvd {d x : GoldenInt} : GoldenDivides d x ↔ d ∣ x := by
  constructor <;> rintro ⟨q, hq⟩
  · exact ⟨q, by simpa using hq⟩
  · exact ⟨q, by simpa using hq⟩
```

と連続しており、この module が explicit coordinate vocabulary を ordinary commutative-ring divisibility に接続する目的であることも header に明記されている。

standalone artifact の ordered source modules に `GoldenDivisibility.lean` が含まれ、artifact 自体は `import Mathlib` を使用している。

対象ブランチには日本語・英語 PDF も存在するが、本 bridge theorem に対応する具体的なページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0189 `goldenDivides_refl`** である。

```lean
theorem goldenDivides_refl (x : GoldenInt) : GoldenDivides x x := by
  rw [goldenDivides_iff_dvd]
```

0188 で `GoldenDivides` と標準 `∣` の往復路が開いたため、0189 からは専用整除 API の基本法則を Mathlib 標準 theorem へ委譲する段階に入る。最初は反射性、その後 `goldenDivides_trans`、`goldenDivides_sub` と続く。
