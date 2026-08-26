# 0208 — `GoldenRelPrime`

## Lean の型

```lean
/-- Relative primality expressed by saying that every common divisor is a unit, hence
has norm `±1`. -/
def GoldenRelPrime (x y : GoldenInt) : Prop :=
  ∀ d : GoldenInt, GoldenDivides d x → GoldenDivides d y → GoldenUnit d
```

これは `theorem` ではなく `def` であり、黄金整数 `x`,`y` の相対素性を「任意の共通因子が unit である」という形で定義する。

## 数学的主張・宣言の意味

数学的には、

$$
GoldenRelPrime(x,y)
$$

を

$$
\forall d\in\mathbb Z[\varphi],\quad d\mid x\land d\mid y\Longrightarrow d\in\mathbb Z[\varphi]^\times
$$

として定義している。

通常の整域や Euclidean domain では「gcd が unit」「Bézout 係数が存在する」「共通非単元因子を持たない」など、相対素性にはいくつか同値な表現がある。本定義はその中でも最も直接的な、**すべての共通因子が unit** という表現を選んでいる。

0198–0207 で `GoldenUnit` とその基本 API が完成しているため、ここで初めて「共通因子の終着点」を `GoldenUnit d` として一つの predicate にまとめられる。

また 0202 により unit はノルム `±1` と同値なので、数学的には

$$
d\mid x,\ d\mid y
\Longrightarrow
N(d)=\pm1
$$

という整数側の判定へ移せる。この点が後続の共役因子の相対素性証明で重要になる。

## 証明全体での役割

`GoldenRelPrime` は `GoldenDivisibility.lean` の末尾に置かれる基礎 predicate であり、次の `GoldenEuclidean.lean` と、その後の fifth-power factor extraction へ渡す契約になる。

この定義が狙っている典型的な状況は、ある黄金整数 `beta` とその共役 `goldenConj beta` に対して、共通因子 `d` を任意に取る場合である。

後続の相対素性証明では、概念的に次の流れを使う。

1. `d` が `beta` と `conj beta` の双方を割ると仮定する。
2. 0191 `goldenDivides_sub` により `d` は差 `beta - conj beta` も割る。
3. 0192 `goldenNorm_dvd_of_goldenDivides` により、`N(d)` は `N(beta)` と `N(beta-conj beta)` の双方を割る。
4. packet 側の整数 coprimality から、この二つの整数 mass の gcd が unit であることを使う。
5. 結果として `N(d)=±1` を得る。
6. 0201 `goldenUnit_of_norm_eq_one_or_neg_one` により `GoldenUnit d` を結論する。

つまり本定義は、黄金整数環内部の共通因子問題を、整数ノルムの整除問題へ射影して解くための最終 goal shape を与える。

FLT5 の第五冪因子抽出では、互いに素な因子の積が第五冪であるとき、各因子が unit を除いて第五冪になる、という Euclidean-domain 的な分離が必要になる。`GoldenRelPrime` はその「互いに素」の hypothesis を明示的に供給する。

## 直接依存する定義・補題

定義そのものの直接依存は三つだけである。

- `GoldenInt`
- 0187 `GoldenDivides`
- 0198 `GoldenUnit`

Lean の全称量化と implication 以外に、theorem や tactic への直接依存はない。

概念的な依存関係は

$$
GoldenDivides
+GoldenUnit
\longrightarrow
GoldenRelPrime
$$

である。

ただし実際に `GoldenRelPrime` を証明する後続 theorem は、0191 `goldenDivides_sub`、0192 `goldenNorm_dvd_of_goldenDivides`、0201/0202 の unit–norm criterion を主要な部品として使うことになる。

## 構築の流れ

`GoldenRelPrime x y` は一行の predicate 定義である。

```lean
def GoldenRelPrime (x y : GoldenInt) : Prop :=
  ∀ d : GoldenInt, GoldenDivides d x → GoldenDivides d y → GoldenUnit d
```

読み方はそのまま次の四段階である。

1. 任意の黄金整数 `d` を取る。
2. `d` が `x` を割ると仮定する。
3. `d` が `y` も割ると仮定する。
4. その `d` が unit であることを要求する。

存在量化による gcd witness や Bézout 係数を保持せず、共通因子に対する universal property のみを保存している。

## Lean 固有の処理

この定義の値域は `Prop` であり、データ構造を作るのではなく theorem hypothesis として使う logical contract である。

仮に

```lean
hrel : GoldenRelPrime x y
```

があれば、共通因子 `d` と

```lean
hdx : GoldenDivides d x
hdy : GoldenDivides d y
```

に対して

```lean
exact hrel d hdx hdy
```

とするだけで `GoldenUnit d` を得られる。

逆に `GoldenRelPrime x y` を証明するときは通常、

```lean
intro d hdx hdy
```

から始め、任意の共通因子を unit に押し込む証明になる。

これは `Nat.Coprime` や ideal-theoretic coprimality のように bundle された gcd 情報を使う方式と比べ、proof goal が非常に直接的である。

## 冗長・重複箇所

数学的には `GoldenRelPrime` は標準 algebra API の coprimality 概念と重複する可能性がある。

`GoldenInt` はすでに `IsDomain` を持ち、後続で `EuclideanDomain` も構築されるため、最終的には gcd / `IsCoprime` / associated-unit 系の Mathlib API によって相対素性を表現できる可能性が高い。

それでも専用 predicate を置く利点は明確である。

- Euclidean-domain 構築前でも使える。
- Bézout 係数を不要にできる。
- FLT5 の proof で実際に必要なのは「共通因子が unit」であり、それをそのまま goal にできる。
- `GoldenDivides` と `GoldenUnit` という既存の監査可能な raw API をそのまま組み合わせられる。

したがって一般性では標準 coprimality API に劣るが、証明の局所目的には非常に適した domain-specific wrapper である。

## 最適化候補

1. **現行の universal common-divisor definition を維持する**
   - downstream goal が直接 `GoldenUnit d` になり、監査しやすい。

2. **標準 coprimality との bridge theorem を追加する**
   - `GoldenRelPrime x y ↔ ...` の形で Mathlib の gcd / coprime predicate と接続すれば一般 API を再利用できる。

3. **`GoldenDivides` / `GoldenUnit` を標準 `∣` / `IsUnit` に統合する**
   - wrapper layer を減らせるが、explicit-coordinate proof の可読性は下がる可能性がある。

4. **symmetric theorem を公開する**
   - 定義から `GoldenRelPrime x y → GoldenRelPrime y x` は容易に示せる。downstream で頻用されるなら named theorem 化を検討できる。

5. **gcd = unit を主定義にする方式と比較する**
   - `EuclideanDomain GoldenInt` 完成後は gcd を使う実装も可能になる。現行定義との proof size と dependency depth を比較できる。

現行定義は非常に小さく、局所的な最適化よりも標準 API との bridge 整備が主な改善候補である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は全体として `import Mathlib` を使用している。

本定義単独で直接必要なのは、ほぼ上流の project-local declarations だけである。

- `GoldenInt`
- `GoldenDivides`
- `GoldenUnit`
- 基本的な `Prop` / `∀` / `→`

本定義自身は `ring`、`norm_num`、gcd theorem、整数整除 theorem を使用しない。

一方、`GoldenDivisibility.lean` module 全体では norm、integer divisibility、共役、unit 判定などを使うため、実際の最小 import は module 単位で測る必要がある。

今回 Lean build は行わないため、exact な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。相対素性の representation を比較する小さな challenge にできる。

比較候補は次の通り。

- A: 現行 `GoldenRelPrime` — すべての共通因子が `GoldenUnit`
- B: 標準 `IsCoprime` / gcd API
- C: Bézout relation `∃ a b, a*x + b*y = 1`
- D: `gcd x y` が unit / associated to `1`
- E: norm-side coprimalityを主 predicate にする設計

比較軸は、Euclidean-domain 構築前の利用可能性、proof dependency depth、witness の大きさ、Mathlib 再利用率、FLT5 downstream theorem の短さ、数学的読みやすさである。

特に A と C の比較は、この development が意図的に Bézout-free な相対素性を選んでいる意味を測るよい Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

0207 正本文書でも、本定義が `GoldenDivisibility.lean` の unit block の直後に置かれる次宣言として確認できる。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本定義に対応する具体的な PDF ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

`GoldenRelPrime` は `GoldenDivisibility.lean` の末尾に位置し、その後は `GoldenEuclidean.lean` に移る。

依存順の次は **0209 `GoldenRat`**、すなわち黄金整数の Euclidean division を構成するための有理座標型

```lean
abbrev GoldenRat := ℚ × ℚ
```

である。

0208 で「互いに素」の契約を確定した後、次 module では rational quotient を座標ごとに丸め、remainder の norm を divisor より小さくする Euclidean-domain 構築へ進む。