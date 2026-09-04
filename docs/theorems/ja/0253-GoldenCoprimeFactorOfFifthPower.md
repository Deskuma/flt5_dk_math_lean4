# 0253 — `GoldenCoprimeFactorOfFifthPower`

## Lean の型

```lean
/--
The generic factorization contract: a factor of a fifth power that is relatively prime
to its complementary factor is itself a fifth power up to a unit.
-/
abbrev GoldenCoprimeFactorOfFifthPower : Prop :=
  ∀ x y z : GoldenInt,
    GoldenRelPrime x y →
    goldenMul x y = goldenPow z 5 →
    ∃ epsilon gamma : GoldenInt,
      GoldenUnit epsilon ∧
      x = goldenMul epsilon (goldenPow gamma 5)
```

これは theorem ではなく、`Prop` の **`abbrev`** である。

黄金整数環における一般的な第五冪因子抽出の「契約」を、証明そのものとは分離して名前付けしている。

## 数学的主張・宣言の意味

この contract が表す数学的内容は、

$$
xy=z^5,
\qquad
\operatorname{RelPrime}(x,y)
$$

ならば、ある単元 $\varepsilon$ と黄金整数 $\gamma$ が存在して

$$
x=\varepsilon\gamma^5
$$

と書ける、というものである。

Lean の raw API では、

- `GoldenRelPrime x y` が「任意の共通因子は `GoldenUnit`」という相対素性、
- `goldenMul x y = goldenPow z 5` が「積が第五冪」、
- `GoldenUnit epsilon` が単元性、
- `x = goldenMul epsilon (goldenPow gamma 5)` が「unit × fifth power」表示

に対応する。

これは UFD / gcd domain で知られる標準的な原理の黄金整数版である。互いに素な二因子の積が第五冪なら、各因子は unit を除いて第五冪になる。

## 証明全体での役割

0252 までで stripped packet の `beta` について、後続の一般論へ渡す二つの入力が揃った。

1. 0244 により

$$
\operatorname{GoldenRelPrime}(\beta,\overline{\beta})
$$

が得られている。

2. 0252 により

$$
\beta\overline{\beta}
=
(\operatorname{goldenOfInt} b)^5
$$

が得られている。

0253 は、この packet 固有の状況をいったん忘れて、

$$
\text{coprime factors of a fifth power}
\Longrightarrow
\text{one factor is a fifth power up to a unit}
$$

という **一般代数 contract** だけを切り出す。

直後の 0254 `signedGoldenFifthPowerUpToUnitCore_of_coprimeFactor` は、この contract を `beta` と `goldenConj beta` に適用し、0239 以前から要求されていた

$$
\beta=\varepsilon\gamma^5
$$

という `SignedGoldenFifthPowerUpToUnitCore` を構成する。

さらに source 後段の `GoldenCoprimeFactor.lean` では、0230 で構築済みの `EuclideanDomain GoldenInt` から `GCDMonoid GoldenInt` を得て、実際に `goldenCoprimeFactorOfFifthPower : GoldenCoprimeFactorOfFifthPower` を証明する。

したがって 0253 は、**FLT5 固有の packet 算術** と **一般的な gcd/UFD 型の第五冪因子抽出** を分離する module boundary になっている。

## 直接依存する定義・補題

これは `abbrev` なので proof script はなく、直接依存する theorem はない。

statement が利用する主要な定義・宣言は次の通りである。

- `GoldenInt`
- 0208 `GoldenRelPrime`
- 0198 `GoldenUnit`
- 0124 `goldenMul`
- `goldenPow`

概念的には、

$$
\operatorname{RelPrime}(x,y)
+
xy=z^5
\Longrightarrow
\exists \varepsilon,\gamma,
\quad
\operatorname{Unit}(\varepsilon)
\land
x=\varepsilon\gamma^5
$$

という一つの implication schema を `Prop` として束ねている。

この contract 自体の実装は後段の `GoldenCoprimeFactor.lean` に委ねられている。

## 構築の流れ

`abbrev` の本体は全称量化と含意の連鎖だけである。

```lean
abbrev GoldenCoprimeFactorOfFifthPower : Prop :=
  ∀ x y z : GoldenInt,
    GoldenRelPrime x y →
    goldenMul x y = goldenPow z 5 →
    ∃ epsilon gamma : GoldenInt,
      GoldenUnit epsilon ∧
      x = goldenMul epsilon (goldenPow gamma 5)
```

流れを分解すると、

1. 任意の `x y z : GoldenInt` を受け取る。
2. `x` と `y` が `GoldenRelPrime` であることを仮定する。
3. `goldenMul x y` が `z` の第五冪であることを仮定する。
4. 単元 `epsilon` と黄金整数 `gamma` の存在を要求する。
5. `x = epsilon * gamma^5` を raw golden API で要求する。

ここでは factor extraction の方法そのものは一切指定しない。gcd、unique factorization、valuation、prime factorization のどの実装でこの contract を満たしても downstream は利用できる。

## Lean 固有の処理

`abbrev ... : Prop := ...` を使っている点が重要である。

`def` ではなく `abbrev` なので、この名前は透明に展開されやすく、consumer 側では単なる関数型として扱える。例えば後段の theorem は

```lean
(hFactor : GoldenCoprimeFactorOfFifthPower)
```

を受け取ると、そのまま

```lean
hFactor p.beta (goldenConj p.beta) ...
```

と関数適用できる。

また `GoldenRelPrime` と `GoldenUnit` は Mathlib 標準の `IsCoprime` / `IsUnit` そのものではなく、この FLT5 開発で導入した明示 API である。そのため 0253 は標準 UFD theorem の型を直接露出せず、既存の黄金整数 API 境界を維持した contract になっている。

## 冗長・重複箇所

数学的には、この proposition は一般環論の「互いに素な因子の積が $n$ 乗なら各因子も unit を除いて $n$ 乗」という既知の形を第五冪・`GoldenInt` に特殊化したものなので、抽象化余地は大きい。

考えられる重複は次の通りである。

- 指数 `5` が固定されている。
- 型が `GoldenInt` に固定されている。
- `GoldenRelPrime` が専用 wrapper である。
- `GoldenUnit` が専用 wrapper である。
- raw `goldenMul` / `goldenPow` を使っており、標準 `*` / `^` と意味が重なる。

一方、FLT5 downstream が必要とする exact shape を一つの名前に閉じ込めることで、consumer は Mathlib の gcd/UFD theorem の細部を知らずに済む。したがってこれは論理的重複というより **dependency inversion のための contract layer** と見るのが自然である。

## 最適化候補

1. **現行 contract を維持する**
   - FLT5 consumer が必要とする型に完全一致し、module 分離が明瞭。

2. **指数を一般化する**
   - 例えば `CoprimeFactorOfPow (n : ℕ)` のようにして、第五冪は `n = 5` の特殊化とする。

3. **型を一般化する**
   - `GCDMonoid` / `UniqueFactorizationMonoid` 等を仮定した一般 theorem に持ち上げる。

4. **Mathlib 標準 API へ寄せる**
   - `GoldenRelPrime ↔ IsCoprime`、`GoldenUnit ↔ IsUnit`、raw operation と標準 notation の bridge を使い、contract 自体を標準 algebra vocabulary で書く。

5. **`Associated` を用いる**
   - `x = epsilon * gamma^5` の代わりに `Associated x (gamma^5)` と表現すれば、unit witness を構造的に隠せる。
   - ただし downstream が実際の `epsilon` を必要とする場合、現在の existential form の方が便利である。

現行設計は「証明 engine を差し替え可能にしつつ downstream の witness shape を固定する」という目的にはかなり適している。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

0253 自体は `abbrev : Prop` なので tactic を一切使わない。直接必要なのは、

- `GoldenInt`
- `GoldenRelPrime`
- `GoldenUnit`
- `goldenMul`
- `goldenPow`

を定義している上流 module だけである。

一方、実際にこの contract を証明する後段 `GoldenCoprimeFactor.lean` では、

- `EuclideanDomain.gcdMonoid`
- `gcd`
- `IsUnit`
- `exists_associated_pow_of_mul_eq_pow`

など Mathlib の gcd / associated / power factorization API を利用する。

したがって import 最適化は、0253 単独より `SignedGoldenFifthPower.lean` と `GoldenCoprimeFactor.lean` の module boundary を基準に測るべきである。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、候補としてのみ記録する。

## Comparator challenge 化の可否

非常に適している。これは proof 一個の比較というより **抽象化レベルの比較** に向く。

比較候補は次の通り。

- A: 現行 `GoldenInt` / exponent 5 固定 contract
- B: exponent を一般化した contract
- C: `GCDMonoid` 上の一般 theorem
- D: `UniqueFactorizationMonoid` / prime multiplicity による theorem
- E: `Associated x (gamma ^ 5)` を結論にする標準 API 版

比較軸は、

- downstream witness の使いやすさ
- Mathlib 標準 API 再利用率
- theorem の一般性
- Lean typeclass dependency の重さ
- standalone 監査性
- FLT5 固有コード量の削減量

である。

特に現行 contract と `Associated` ベースの一般 theorem の比較は、「具体 witness を保持する FLT5 向け API」と「一般環論として自然な API」の差を測る良い Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenFifthPower.lean` generated section である。

正本 source では、0252 `SignedGoldenRamifierStrippedPacket.beta_mul_conj_eq_fifth` の直後に本 `abbrev` が置かれ、その次に `signedGoldenFifthPowerUpToUnitCore_of_coprimeFactor` が続く。

さらに後段 `GoldenCoprimeFactor.lean` では、`EuclideanDomain.gcdMonoid GoldenInt` と `exists_associated_pow_of_mul_eq_pow` を使って、この contract の具体実装 `goldenCoprimeFactorOfFifthPower` が証明されることを確認した。

対象ブランチには `docs/pdf/FLT5-main-ja-v0-r1.pdf` と `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし本 `abbrev` に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0254 `signedGoldenFifthPowerUpToUnitCore_of_coprimeFactor`** である。

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

0253 が generic factor-extraction contract を定義し、0254 は 0244 の相対素性と 0252 の第五冪積等式をその contract に渡して、

$$
\beta=\varepsilon\gamma^5
$$

という stripped packet 用の core を実際に構成する。
