# 0207 — `goldenUnit_pow`

## Lean の型

```lean
theorem goldenUnit_pow {x : GoldenInt} (hx : GoldenUnit x) (n : ℕ) :
    GoldenUnit (goldenPow x n) := by
  induction n with
  | zero => exact goldenUnit_one
  | succ n ih => exact goldenUnit_mul ih hx
```

これは `theorem` であり、黄金整数 `x` が `GoldenUnit` なら、その raw 自然数冪 `goldenPow x n` も任意の `n : ℕ` に対して `GoldenUnit` であることを示す。

## 数学的主張・宣言の意味

数学的には、単元の自然数冪も単元であるという標準的な閉性を表す。

$$
GoldenUnit(x)\Longrightarrow GoldenUnit(x^n)
$$

ここで `goldenPow` は 0125 で定義された黄金整数の明示的な再帰冪で、

```lean
def goldenPow (x : GoldenInt) : ℕ → GoldenInt
  | 0 => goldenOne
  | n + 1 => goldenMul (goldenPow x n) x
```

という形を持つ。したがって本 theorem の帰納構造は `goldenPow` の定義そのものと一致する。

`n = 0` では

$$
x^0=1
$$

なので 0204 `goldenUnit_one` を使う。`n+1` では

$$
x^{n+1}=x^n x
$$

であり、帰納法の仮定から `x^n` が unit、元の仮定 `hx` から `x` が unit なので、0206 `goldenUnit_mul` により積も unit となる。

特に FLT5 では `n=5` を代入して、unit の第五冪が再び unit であることをただちに得られる。黄金整数上で unit factor と fifth-power factor を分離・再結合する後続の議論に直接つながる性質である。

## 証明全体での役割

0198–0207 は `GoldenUnit` の基礎 API を完成させる block である。

- 0198 `GoldenUnit` — 両側逆元の存在として unit を定義。
- 0199–0202 — `GoldenUnit x` と `goldenNorm x = ±1` の双方向判定。
- 0203 `goldenUnit_phi` — 生成元 `φ` が unit。
- 0204 `goldenUnit_one` — `1` が unit。
- 0205 `goldenUnit_neg` — 符号反転に対する閉性。
- 0206 `goldenUnit_mul` — 乗法に対する閉性。
- 0207 本 theorem — 自然数冪に対する閉性。

0207 はこの unit block の最後の theorem であり、0204 と 0206 を自然数帰納法で合成して「任意冪」を一つの reusable API にまとめる。

その直後には

```lean
def GoldenRelPrime (x y : GoldenInt) : Prop :=
  ∀ d : GoldenInt, GoldenDivides d x → GoldenDivides d y → GoldenUnit d
```

が置かれる。したがって source の構造としても、0207 で unit の基本演算閉性を完成させた後、その完成済み `GoldenUnit` を使って「すべての共通因子が unit」という relative primality の概念へ移る。

FLT5 の黄金整数側では、共役因子を互いに素な第五冪因子へ分離するために unit の扱いが不可欠である。本 theorem は、unit を冪操作の中でも安定に保持するための最後の基礎部品である。

## 直接依存する定義・補題

現行 proof の直接依存は非常に小さい。

- 0198 `GoldenUnit`
- 0125 `goldenPow`
- 0204 `goldenUnit_one`
- 0206 `goldenUnit_mul`
- Lean の自然数帰納法 `induction`

論理構造は

$$
GoldenUnit(1)
$$

と

$$
GoldenUnit(a)\land GoldenUnit(x)
\Longrightarrow
GoldenUnit(ax)
$$

を使って、再帰的に

$$
GoldenUnit(x^n)
$$

を構成するだけである。

なお `goldenPow` は 0160 `golden_pow_eq` により標準冪 `x ^ n` と定義的に一致することが既に公開されている。そのため本 theorem は raw API 上の statement だが、標準冪に対する unit 閉性と数学的内容は同じである。

## 証明・構築の流れ

proof は自然数 `n` に関する構造帰納法そのものである。

### 1. `n = 0`

```lean
| zero => exact goldenUnit_one
```

`goldenPow x 0` は定義により `goldenOne` なので、0204 `goldenUnit_one` がそのまま goal を閉じる。

### 2. `n + 1`

```lean
| succ n ih => exact goldenUnit_mul ih hx
```

帰納法の仮定

```lean
ih : GoldenUnit (goldenPow x n)
```

と元の仮定

```lean
hx : GoldenUnit x
```

を 0206 `goldenUnit_mul` へ渡す。

`goldenPow x (n + 1)` は定義により

```lean
goldenMul (goldenPow x n) x
```

なので、`goldenUnit_mul ih hx` の結論と goal は定義的に一致し、追加の `rw`、`change`、`simp` を必要としない。

## Lean 固有の処理

この theorem で最も重要な Lean 固有の点は、帰納法の形と `goldenPow` の再帰定義が完全に揃っていることである。

```lean
induction n with
| zero => ...
| succ n ih => ...
```

とすると、successor goal は elaboration 時に `goldenPow` の再帰式を反映した形になり、

```lean
exact goldenUnit_mul ih hx
```

だけで閉じる。

これは 0196 `goldenConj_pow` や 0197 `goldenNorm_pow` との興味深い対照である。そちらは statement が標準冪 `x ^ n` を使うため、`pow_succ` と raw `goldenMul` の間に `change` が必要だった。一方 0207 は statement 自体が raw `goldenPow` を使っているので、再帰式との definitional alignment が最も強く、proof が極端に短い。

また 0160

```lean
@[simp] theorem golden_pow_eq (x : GoldenInt) (n : ℕ) :
    goldenPow x n = x ^ n := rfl
```

があるため、必要なら downstream で標準冪へ容易に変換できる。

## 冗長・重複箇所

数学的には「unit の冪は unit」は一般環論の標準事実であり、Mathlib の `IsUnit` を使えば専用帰納 theorem を再証明せずに済む可能性が高い。

また `goldenPow` と標準 `Pow.pow` は 0160 で定義的に一致しているため、API-level では

- `GoldenUnit (goldenPow x n)`
- `GoldenUnit (x ^ n)`

という二つの表現候補がある。現行 theorem は raw operation layer を優先して前者を採用している。

一方、この raw statement には明確な利点もある。`goldenPow` の定義と induction shape が一致するため、proof は `goldenUnit_one` と `goldenUnit_mul` の二行だけで済む。標準冪 statement にすると `golden_pow_eq` や一般 `pow_succ` API を介する層が増える可能性がある。

したがって重複は存在するが、raw bootstrap API の透明性と proof simplicity を得るための意図的な重複と評価できる。

## 最適化候補

1. **現行 raw-power theorem を維持する**
   - 再帰定義と帰納法が完全一致し、proof が最小である。

2. **標準冪版 theorem を追加する**
   - 例えば

```lean
theorem goldenUnit_pow_std {x : GoldenInt} (hx : GoldenUnit x) (n : ℕ) :
    GoldenUnit (x ^ n) := by
  simpa using goldenUnit_pow hx n
```

   のような bridge が候補になる。ただし exact な `simpa` 動作は今回 build 未検証である。

3. **`GoldenUnit ↔ IsUnit` を利用する**
   - Mathlib の一般 `IsUnit.pow` 相当 API に委譲できれば、専用帰納 proof 自体を削減できる可能性がある。

4. **0201/0202 の unit criterion を iff として bundle する**
   - `N(x^n)=N(x)^n` と組み合わせて norm 側から冪閉性を示す別 proof architecture が可能になる。

5. **`goldenPow` を完全に標準 `Pow` API へ吸収する**
   - raw operation の監査目的が薄れた段階で検討できる。ただし現状の theorem museum では明示座標実装を追跡する価値が高い。

局所 proof は既に非常に良いため、最適化余地は proof 圧縮ではなく raw/standard API の整理にある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が直接必要とする表面は極めて小さい。

- `Nat` と自然数帰納法
- `GoldenUnit`
- `goldenPow`
- `goldenUnit_one`
- `goldenUnit_mul`

本 theorem では `ring`、`norm_num`、`simp`、整数整除 theorem などは直接使用しない。

したがって宣言単体なら Mathlib 全体よりはるかに小さい import で足りる可能性が高い。ただし `GoldenDivisibility.lean` module 全体は整除・共役・ノルム・整数算術などを利用するため、実際の import 最適化は module 単位で測定すべきである。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、候補としてのみ記録する。

## Comparator challenge 化の可否

適している。小さな theorem だが API 設計の比較が明瞭である。

比較候補は次の通り。

- A: 現行 raw `goldenPow` に対する直接帰納 proof
- B: 標準冪 `x ^ n` に対する帰納 proof
- C: `GoldenUnit ↔ IsUnit` と Mathlib 標準 unit-power API を使う proof
- D: `N(x)=±1` と `goldenNorm_pow` を使う norm-based proof
- E: inverse witness の冪を直接構成する proof

比較軸は、proof term の短さ、raw/standard API 間の変換数、typeclass dependency depth、数学的 provenance、Mathlib 再利用率、将来の refactor 耐性である。

特に A と D は、0205–0206 が norm criterion を中心に証明されている一方、0207 は再帰構造を直接利用しているという設計差を比較できる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

正本 source では 0206 の直後に本 theorem があり、その直後に `GoldenRelPrime` の定義が続くことを確認した。

standalone artifact は `DkMath/FLT/Five/GoldenDivisibility.lean` を ordered source module として含み、全体として `import Mathlib` を使用している。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的 PDF ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0208 `GoldenRelPrime`** である。

```lean
/-- Relative primality expressed by saying that every common divisor is a unit, hence
has norm `±1`. -/
def GoldenRelPrime (x y : GoldenInt) : Prop :=
  ∀ d : GoldenInt, GoldenDivides d x → GoldenDivides d y → GoldenUnit d
```

0207 までで `GoldenUnit` の定義・ノルム判定・基本演算閉性が揃った。0208 はその完成済み unit predicate を使い、「`x` と `y` の任意の共通因子 `d` は unit である」と定義する。

これは Bézout 係数を直接構成せずに相対素性を表現する API であり、元とその共役の共通因子を排除して第五冪因子分解へ進む後続証明の入口になる。