# 0240 — `SignedGoldenFifthPowerUpToUnitCore`

## Lean の型

```lean
/--
The algebraic output requested from a stripped packet: `beta` is a fifth power up to a
golden unit.  `GoldenCoprimeFactor.signedGoldenFifthPowerUpToUnitCore` proves this
contract unconditionally after conjugate relative primality is certified.
-/
abbrev SignedGoldenFifthPowerUpToUnitCore : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w),
    ∃ epsilon gamma : GoldenInt,
      GoldenUnit epsilon ∧
      p.beta = goldenMul epsilon (goldenPow gamma 5)
```

これは `theorem` ではなく `abbrev` であり、ramifier-stripped packet から今後取り出したい代数的出力を一つの命題型として名前付けする宣言である。

## 数学的主張・宣言の意味

`SignedGoldenRamifierStrippedPacket u v w` は、exceptional branch から可視 ramifier `tau` を一度取り除いた黄金整数 `beta` を保持している。0231 までに packet は概略

$$
\alpha=\tau\beta,
$$

$$
N(\beta)=b^5,
$$

$$
5\nmid N(\beta),
$$

$$
\tau\nmid\beta
$$

という情報を持つ。

0240 は、その stripped element `beta` がさらに

$$
\beta=\varepsilon\gamma^5
$$

と書けることを要求する contract である。ここで

- $\varepsilon$ は黄金整数環の unit、
- $\gamma$ は黄金整数、
- `goldenPow gamma 5` は $\gamma^5$、
- `goldenMul epsilon (...)` は $\varepsilon\gamma^5$

を表す。

したがってこの命題は「`beta` は unit を除けば完全な第五冪である」という fifth-power extraction の核心を表している。

## 証明全体での役割

0237–0239 では、ramifier-stripped packet から矛盾を返す receiver contract と、それを上流 Branch-A / Branch-B routing へ戻す bridge が整備された。一方 0240 は `False` を直接要求しない。

代わりに、stripped packet から次の本質的な代数出力

$$
\beta=\varepsilon\gamma^5
$$

を返すことを要求する。

この分離は重要である。最終矛盾を一気に証明するのではなく、まず Euclidean-domain / gcd / coprimality machinery が提供すべき algebraic payload を contract として切り出している。

正本 source のコメントでは、後続の `GoldenCoprimeFactor.signedGoldenFifthPowerUpToUnitCore` が、`beta` とその共役の relative primality を証明した後、この contract を無条件に満たすと説明されている。

したがって概念的な pipeline は

$$
\text{ramifier-stripped packet}
\longrightarrow
\text{conjugate relative primality}
\longrightarrow
\beta=\varepsilon\gamma^5
\longrightarrow
\text{unit-sector / zero-sector analysis}
\longrightarrow
\bot
$$

となる。

0240 はこのうち「conjugate-coprime factor of a fifth power から第五冪を抽出する」部分の公開 contract である。

## 直接依存する定義・補題

この宣言は `abbrev` なので proof script を持たず、直接の theorem 依存はない。型として直接参照するのは次の定義・概念である。

- `SignedGoldenRamifierStrippedPacket`
- `GoldenInt`
- `GoldenUnit`
- `goldenMul`
- `goldenPow`
- 自然数 `ℕ`
- existential proposition `∃`

依存関係は概念的に

$$
\texttt{SignedGoldenRamifierStrippedPacket}
+\texttt{GoldenUnit}
+\texttt{goldenPow}
\longrightarrow
\texttt{SignedGoldenFifthPowerUpToUnitCore}
$$

である。

なお packet の `beta_norm : goldenNorm beta = b^5` だけから本 contract は直ちには従わない。ノルムが第五冪であることと、元自身が unit times fifth power であることの間には、factorization / coprimality の議論が必要である。そこが後続 module の仕事になる。

## 構築の流れ

宣言そのものは命題の別名を一段で定義している。

```lean
abbrev SignedGoldenFifthPowerUpToUnitCore : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w),
    ∃ epsilon gamma : GoldenInt,
      GoldenUnit epsilon ∧
      p.beta = goldenMul epsilon (goldenPow gamma 5)
```

論理構造は次の通り。

1. 任意の indices `u v w` を取る。
2. 任意の stripped packet `p` を取る。
3. unit 候補 `epsilon` と fifth-power base `gamma` の存在を要求する。
4. `epsilon` が `GoldenUnit` であることを要求する。
5. `p.beta = epsilon * gamma^5` を要求する。

ここでは witness の構成方法は一切指定しない。0240 は producer の実装ではなく、producer が満たすべき interface である。

## Lean 固有の処理

`abbrev ... : Prop := ...` なので、Lean はこの名前を透明な略記として扱う。`def` よりも展開しやすく、receiver theorem では必要に応じて本体の `∀` / `∃` 型へほぼそのまま展開できる。

binder

```lean
∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w), ...
```

の `u v w` は implicit であり、通常は `p` の型から推論される。

また

```lean
∃ epsilon gamma : GoldenInt,
  GoldenUnit epsilon ∧
  p.beta = goldenMul epsilon (goldenPow gamma 5)
```

は nested existential であり、producer 側では典型的に

```lean
refine ⟨epsilon, gamma, hUnit, hBeta⟩
```

の形で witness を組み立てられる。

`goldenMul` / `goldenPow` を raw API として statement に残している点も特徴である。標準 notation なら

```lean
p.beta = epsilon * gamma ^ 5
```

と書けるが、現行 statement は explicit golden API を維持している。

## 冗長・重複箇所

0240 は数学 theorem そのものではなく contract alias なので、論理的には本体の `∀ ... ∃ ...` を downstream theorem の仮定や結論へ直接書けば不要である。

それでも named contract を置く利点は大きい。

- stripped packet 層が最終的に何を要求しているかを一つの名前で表せる。
- producer 側の gcd / Euclidean-domain 実装と consumer 側の unit-sector exclusion を分離できる。
- theorem 名から dependency graph を読める。
- 後で fifth-power extraction の内部実装が変わっても public contract を保ちやすい。

また `GoldenUnit epsilon ∧ beta = ...` を existential の中に持つ形は、Mathlib の `IsUnit` や `Associated` を使う表現と意味的に重なる可能性がある。

数学的には

$$
\beta \sim \gamma^5
$$

という associated relation で表現する選択肢もある。ただし現行形式は unit witness `epsilon` を明示的に保持するため、後続の unit-sector mod fifth 分類へそのまま渡しやすい。

## 最適化候補

1. **現行 `abbrev` を維持する**
   - producer / consumer boundary が明瞭で、展開も軽い。

2. **標準 algebra notation に寄せる**

```lean
p.beta = epsilon * gamma ^ 5
```

   とすれば Mathlib の generic rewriting と馴染みやすい。raw API を維持する監査性との比較が必要である。

3. **`IsUnit` / `Associated` で表す**
   - `beta` が fifth power と associated である、という一般環論 API に寄せられる可能性がある。
   - ただし後続で concrete unit witness が必要なら再び witness extraction が必要になる。

4. **結果を structure に bundle する**
   - `epsilon`, `gamma`, `GoldenUnit epsilon`, `beta_eq` を fields に持つ `SignedGoldenFifthPowerData` のような structure を作る案。
   - downstream で同じ witness を複数 theorem が利用するなら有効。

5. **指数 `5` を一般化する**
   - generic `n`-th-power-up-to-unit contract へ抽象化できるが、本 module は FLT5 専用なので抽象化コストとの比較が必要である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 `abbrev` 自身が要求する Mathlib 表面は非常に小さく、基本的には

- `Prop`
- `∀` / `∃`
- `ℕ`

程度である。実質的な依存は project 内の `GoldenInt`, `GoldenUnit`, `goldenMul`, `goldenPow`, `SignedGoldenRamifierStrippedPacket` にある。

したがってこの宣言単独のために `Mathlib` 全体が必要とは考えにくい。ただし実際の `SignedGoldenRamifierStripped.lean` は five-adic packet construction、ノルム、整除、ring tactic など広い依存を持つため、最小 import は module 単位で測る必要がある。

今回は Lean build を行わないので、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 `abbrev` + raw `goldenMul` / `goldenPow`
- B: `def` として opaque boundary を作る
- C: 標準 notation `epsilon * gamma ^ 5`
- D: `IsUnit` / `Associated` を使う generic algebra formulation
- E: witness を structure に bundle する

比較軸は、statement の読みやすさ、definitional transparency、downstream witness 利用の容易さ、Mathlib 標準 API との相互運用性、proof audit の透明性、将来の一般化可能性である。

特に A と D の比較は、「FLT5 専用の明示座標 API」と「一般環論の associated / unit API」のどちらが証明全体を短く保てるかを見る良い Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` generated section である。

正本 source では 0239 `branchB_false_of_goldenRamifierStrippedCore` の直後に本 `abbrev` が置かれ、この宣言で `SignedGoldenRamifierStripped.lean` が終了する。

source コメントは、後続 `GoldenCoprimeFactor.signedGoldenFifthPowerUpToUnitCore` が conjugate relative primality を経てこの contract を無条件に証明すると明記している。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 contract に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は、次 module `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` の先頭 theorem、**0241 `golden_sub_conj_eq_snd_mul_sqrtFive`** である。

```lean
/-- Subtracting the conjugate isolates the square-root-of-five direction. -/
theorem golden_sub_conj_eq_snd_mul_sqrtFive (x : GoldenInt) :
    x - goldenConj x = goldenMul (goldenOfInt x.snd) sqrtFiveElement := by
  apply GoldenInt.ext
  · simp [goldenConj, goldenOfInt, goldenSqrtFive, goldenMul]
  · simp [goldenConj, goldenOfInt, goldenSqrtFive, goldenMul]
    ring
```

0240 で fifth-power extraction の目標 contract が明示された。0241 からは、その contract を得るために必要な `beta` と `conj beta` の relative primality を証明する module へ入り、まず差

$$
x-\overline{x}
$$

が第二座標と $\sqrt5$ 方向だけに乗ることを明示する。