# 0197 — `goldenNorm_pow`

## Lean の型

```lean
theorem goldenNorm_pow (x : GoldenInt) (n : ℕ) :
    goldenNorm (x ^ n) = goldenNorm x ^ n := by
  induction n with
  | zero => norm_num [goldenNorm]
  | succ n ih =>
      rw [pow_succ]
      change goldenNorm (goldenMul (x ^ n) x) = _
      rw [goldenNorm_mul, ih, pow_succ]
```

これは `theorem` であり、黄金整数ノルム `goldenNorm` が自然数冪を保存することを示す。

## 数学的主張

任意の黄金整数 $x\in\mathbb Z[\varphi]$ と自然数 $n$ に対して、

$$
N(x^n)=N(x)^n
$$

が成立することを主張する。

0174 `goldenNorm_mul` で既に

$$
N(xy)=N(x)N(y)
$$

が証明されているため、本 theorem はその乗法性を自然数冪へ帰納的に反復したものに相当する。

FLT5 では第五冪が中心に現れるので、特に

$$
N(x^5)=N(x)^5
$$

を標準冪 API 上で直接使えることが重要である。

## 証明全体での役割

`GoldenDivisibility.lean` では 0196 `goldenConj_pow` により共役と冪の互換性を整備した直後、本 theorem でノルムと冪の互換性を確立する。

この結果により、黄金整数の第五冪という環内部の情報を、整数の第五冪という通常の整数算術へ移せる。後続の単元・整除・第五冪因子分解では、ノルムを整数側の不変量として使うため、

$$
x=y^5
$$

のような関係から

$$
N(x)=N(y)^5
$$

を得られることは直接的な橋になる。

また 0174 `goldenNorm_mul` と 0192 `goldenNorm_dvd_of_goldenDivides` を合わせると、`goldenNorm` は黄金整数環の乗法構造と整除構造を整数へ射影する主要インターフェースになっている。本 theorem はその power-compatible API を完成させる。

## 直接依存する定義・補題

proof が直接使用する主要 theorem / tactic は次の通り。

- 0174 `goldenNorm_mul`
- Lean / Mathlib 標準の `pow_succ`
- 自然数帰納法
- 帰納仮定 `ih`
- 基底ケースの `norm_num`

型・演算としては次に依存する。

- `GoldenInt`
- 0164 `goldenNorm`
- 0124 `goldenMul`
- `CommRing GoldenInt` による標準自然数冪 `x ^ n`

概念的には

$$
\texttt{goldenNorm\_mul}
+\text{自然数帰納法}
\longrightarrow
\texttt{goldenNorm\_pow}
$$

である。

## 証明の流れ

proof は $n$ に関する帰納法である。

### 基底 $n=0$

```lean
| zero => norm_num [goldenNorm]
```

数学的には

$$
N(x^0)=N(1)=1=N(x)^0
$$

である。

`GoldenInt` の `1` は座標 `⟨1,0⟩` なので、`goldenNorm` を展開すると $1$ になる。ここは `rfl` ではなく `norm_num [goldenNorm]` を使い、標準冪の零乗と整数二次式の評価をまとめて正規化している。

### 帰納段階 $n\mapsto n+1$

```lean
| succ n ih =>
    rw [pow_succ]
    change goldenNorm (goldenMul (x ^ n) x) = _
    rw [goldenNorm_mul, ih, pow_succ]
```

1. `pow_succ` で $x^{n+1}$ を $x^n x$ に展開する。
2. `change` で標準乗法を raw operation `goldenMul` の形に見せる。
3. `goldenNorm_mul` により

$$
N(x^n x)=N(x^n)N(x)
$$

へ変換する。
4. 帰納仮定 `ih` で $N(x^n)$ を $N(x)^n$ に置き換える。
5. 右辺の `pow_succ` を展開して一致させる。

数学的には「乗法的写像は自然数冪を保存する」という一般論そのものを、明示的な帰納法で実装している。

## Lean 固有の処理

特徴的なのは 0196 と同じく `change` で raw / standard multiplication の表現を合わせる部分である。

```lean
change goldenNorm (goldenMul (x ^ n) x) = _
```

`pow_succ` 後の左辺は標準乗法 `x ^ n * x` を含む。一方、0174 `goldenNorm_mul` は raw operation `goldenMul` を使って statement されている。

`Mul GoldenInt` instance の実体は `goldenMul` なので両者は definitionally 接続されているが、既存 theorem の表面形へ合わせるため `change` を明示している。

最後の

```lean
rw [goldenNorm_mul, ih, pow_succ]
```

では、ノルムの乗法性・帰納仮定・整数冪の successor law を一続きの rewrite として使う。0196 `goldenConj_pow` よりも最後の raw / standard multiplication の逆変換が少なく、ノルムの値域が `ℤ` であるため右辺は通常の整数冪だけで閉じる。

## 冗長・重複箇所

数学的には本 theorem は 0174 `goldenNorm_mul` の一般的な帰結なので、独立した情報は少ない。

`goldenNorm` が適切な multiplicative morphism として bundle されていれば、Mathlib の generic な `map_pow` 型 theorem から導出できる可能性が高い。その意味で、現行の手書き induction は構造的重複を含む。

ただし `goldenNorm : GoldenInt → ℤ` は通常の ring homomorphism ではない。加法は保存せず、乗法と `1` を保存する種類の写像である。そのため bundle 化するなら `MonoidHom` 相当の乗法構造として設計する必要がある。

現行 theorem はその bundle を導入せずに必要な power law だけを明示しており、局所的には軽量で監査しやすい。

## 最適化候補

1. **現行の帰納 proof を維持する**
   - 依存が浅く、0174 の乗法性からの導出経路が明確。

2. **ノルムを multiplicative morphism として bundle する**
   - `goldenNorm` が $1$ と乗法を保存することを `MonoidHom` 系の API へまとめ、generic `map_pow` を利用する。
   - unit や divisibility の後続 theorem でも再利用できる可能性がある。

3. **raw power `goldenPow` 側で証明する**
   - `goldenPow` の再帰に対して直接 induction し、最後に 0160 `golden_pow_eq` で標準冪へ接続する設計も可能。

4. **標準乗法版の `goldenNorm_mul` を用意する**
   - `goldenNorm (x * y) = goldenNorm x * goldenNorm y` を公開すれば、`change` を消せる可能性がある。

5. **基底ケースの簡約を調べる**
   - `norm_num [goldenNorm]` は十分明瞭だが、より軽い `simp [goldenNorm]` や `rfl` が成立するかは build で比較可能。

今回 Lean build は行わないため、これらは最適化候補として記録する。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem が直接必要とする主な機能は、

- `Nat` induction
- `pow_succ`
- `rw`
- `change`
- `norm_num`
- `GoldenInt` の乗法・冪 API
- `goldenNorm_mul`

である。

`ring` や整除 tactic は本 theorem 自身では直接使用しない。一方、`goldenNorm_mul` の上流証明は `ring` を用い、同 module では divisibility / unit API も扱うため、module 全体の最小 import はより広い。

Lean build を行わないため、正確な最小 import 集合は未検証である。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行の自然数帰納 proof
- B: `goldenNorm` を multiplicative `MonoidHom` として bundle し `map_pow` を使用
- C: raw `goldenPow` で induction して最後に `golden_pow_eq` を適用
- D: 標準乗法版 `goldenNorm_mul` を用意して `change` を排除
- E: tactic 構成を `simp` / `simpa` 中心へ短縮

比較軸は、proof 行数、抽象化コスト、raw / standard API 境界の露出度、後続再利用性、Mathlib 依存、refactor 耐性である。

特に A と B の比較は、明示座標ライブラリでノルムをどこまで抽象的な multiplicative map として扱うべきかを測る良い Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

正本 source では 0196 の直後に本 theorem、その直後に `GoldenUnit` が並ぶ。

```lean
theorem goldenNorm_pow (x : GoldenInt) (n : ℕ) :
    goldenNorm (x ^ n) = goldenNorm x ^ n := by
  induction n with
  | zero => norm_num [goldenNorm]
  | succ n ih =>
      rw [pow_succ]
      change goldenNorm (goldenMul (x ^ n) x) = _
      rw [goldenNorm_mul, ih, pow_succ]

/-- A two-sided unit in the coordinate order.  Later theorems identify this predicate
with Mathlib's `IsUnit` and with norm `±1`. -/
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧ goldenMul eta epsilon = goldenOne
```

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0198 `GoldenUnit`** である。

```lean
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧ goldenMul eta epsilon = goldenOne
```

0197 までで共役・ノルムと冪の互換性が揃った。0198 からは、二側逆元を持つ黄金整数を専用 predicate として定義し、ノルム `±1` と unit 性を結びつけるブロックへ入る。