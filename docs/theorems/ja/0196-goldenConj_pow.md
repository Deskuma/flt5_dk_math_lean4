# 0196 — `goldenConj_pow`

## Lean の型

```lean
theorem goldenConj_pow (x : GoldenInt) (n : ℕ) :
    goldenConj (x ^ n) = goldenConj x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ]
      change goldenConj (goldenMul (x ^ n) x) = _
      rw [goldenConj_mul, ih]
      rw [pow_succ, ← golden_mul_eq]
```

これは `theorem` であり、黄金整数の共役 `goldenConj` が自然数冪を保存することを示す。

## 数学的主張

任意の黄金整数 $x\in\mathbb Z[\varphi]$ と自然数 $n$ に対して、

$$
\overline{x^n}=\overline{x}^{\,n}
$$

が成り立つことを主張する。

0171 `goldenConj_mul` で既に

$$
\overline{xy}=\overline{x}\,\overline{y}
$$

が証明されているため、本 theorem はその乗法保存則を自然数冪へ帰納的に反復した結果である。

## 証明全体での役割

`GoldenDivisibility.lean` のこの位置では、0193–0195 で共役が加法・否定・減算を保存することを整備した後、0196 で冪との互換性を確立する。

FLT5 では第五冪が中心に現れるため、共役を

$$
\overline{x^5}=\overline{x}^{\,5}
$$

として冪の内側へ移せることは重要である。後続の unit / norm / fifth-power factorization では、共役と第五冪を同じ代数 API 上で扱えるようになる。

また 0170 `goldenConj_invol`、0171 `goldenConj_mul`、0193 `goldenConj_add`、0194 `goldenConj_neg`、0195 `goldenConj_sub` と合わせると、`goldenConj` は実質的に `GoldenInt` の環自己同型として振る舞っている。本 theorem はその power-compatible API を補完する。

## 直接依存する定義・補題

proof が直接使用する主要 theorem は次の通り。

- 0171 `goldenConj_mul`
- 0159 `golden_mul_eq`
- Lean / Mathlib 標準の `pow_succ`

加えて、帰納法の仮定 `ih` を使用する。

型・演算としては次に依存する。

- `GoldenInt`
- 0163 `goldenConj`
- `Mul GoldenInt`
- `Pow GoldenInt ℕ` / `npow`
- 0124 `goldenMul`

概念的には

$$
\texttt{goldenConj\_mul}
+\text{自然数帰納法}
\longrightarrow
\texttt{goldenConj\_pow}
$$

である。

## 証明の流れ

proof は $n$ に関する帰納法である。

### 基底 $n=0$

```lean
| zero => rfl
```

`x^0=1` であり、`goldenConj 1 = 1` が定義的に一致するため `rfl` で閉じる。

### 帰納段階 $n\mapsto n+1$

```lean
| succ n ih =>
    rw [pow_succ]
    change goldenConj (goldenMul (x ^ n) x) = _
    rw [goldenConj_mul, ih]
    rw [pow_succ, ← golden_mul_eq]
```

1. `pow_succ` で $x^{n+1}$ を $x^n x$ に展開する。
2. `change` で標準乗法を raw multiplication `goldenMul` として見せる。
3. `goldenConj_mul` で共役を積の内側へ分配する。
4. 帰納仮定 `ih` により `goldenConj (x^n)` を `goldenConj x ^ n` へ置き換える。
5. 右辺も `pow_succ` で展開し、`← golden_mul_eq` で raw / standard multiplication の表現を一致させる。

このように、数学的な乗法準同型の帰納的反復を Lean の representation bridge と組み合わせている。

## Lean 固有の処理

最も特徴的なのは `change` と `← golden_mul_eq` である。

```lean
change goldenConj (goldenMul (x ^ n) x) = _
```

`pow_succ` 後の標準乗法 `x ^ n * x` は、`Mul GoldenInt` instance により `goldenMul` と definitionally 接続されている。ただし `goldenConj_mul` の statement は raw `goldenMul` を使っているため、`change` で goal の表面形を theorem に合わせている。

最後の

```lean
rw [pow_succ, ← golden_mul_eq]
```

も同じ raw / standard API 境界を逆向きに調整する処理である。

この proof は、数学的には単純な homomorphism law でも、Lean 上では「どの表現の乗法を theorem が期待しているか」を明示的に揃える必要があることをよく示している。

## 冗長・重複箇所

本 theorem は 0171 `goldenConj_mul` から一般論として導けるため、数学的には独立情報が少ない。

さらに `goldenConj` を `RingHom` / `RingEquiv` として bundle していれば、`map_pow` 相当の generic theorem によって本結果はほぼ自動で得られる。

現行 source では共役の保存則を個別 theorem として展開しているため、`goldenConj_add`、`goldenConj_mul`、`goldenConj_pow` などに構造的重複がある。

一方で、raw coordinate API の各段階を明示的に監査できる利点は大きい。特に `change` と `golden_mul_eq` の必要性が見えるため、representation layer の確認には有用である。

## 最適化候補

1. **現行の帰納 proof を維持する**
   - 依存関係と representation bridge が明瞭。

2. **`RingHom` 化する**
   - `goldenConj` を ring homomorphism として bundle し、generic `map_pow` を利用する。

3. **`RingEquiv` 化する**
   - 0170 `goldenConj_invol` を inverse law に使い、自己同型として統合する。

4. **標準 notation 側の theorem を先に整備する**
   - `goldenConj (x * y) = goldenConj x * goldenConj y` を標準記法で公開すれば、`change` / `golden_mul_eq` の往復を減らせる可能性がある。

5. **`simpa` を用いる短縮**
   - bundled morphism API がなくても `pow_succ` と simp lemmas の組合せで短縮できる可能性はあるが、今回は Lean build を行わないため未検証である。

局所的には十分短い proof であり、最大の最適化候補は共役全体の morphism bundle 化である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem が直接必要とする主な機能は、

- `Nat` induction
- `pow_succ`
- equality rewrite
- `change`
- `GoldenInt` の multiplication / power API
- `goldenConj_mul`
- `golden_mul_eq`

である。

`ring`、`norm_num`、整除 tactic などは本 theorem 自身では使用しない。

ただし module 全体では divisibility、norm、unit 等を扱うため最小 import は広くなる。今回 Lean build は行わないので、正確な最小 import 集合は未検証であり、最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行の明示的な自然数帰納 proof
- B: 標準 notation の乗法保存 theorem を用いて representation bridge を減らす proof
- C: `RingHom` 化して `map_pow` を利用
- D: `RingEquiv` 化して automorphism API を利用
- E: 各 `n` を raw `goldenPow` 側で帰納し、最後に `golden_pow_eq` で標準冪へ接続

比較軸は、proof 行数、raw / standard API 往復回数、抽象化コスト、数学的 provenance、downstream 再利用性、refactor 耐性である。

特に A と C の比較は、明示座標ライブラリで generic morphism abstraction を導入する価値を測る良い題材になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

正本 source では、0195 の直後に本 theorem、その直後に 0197 `goldenNorm_pow` が並ぶ。

```lean
theorem goldenConj_pow (x : GoldenInt) (n : ℕ) :
    goldenConj (x ^ n) = goldenConj x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ]
      change goldenConj (goldenMul (x ^ n) x) = _
      rw [goldenConj_mul, ih]
      rw [pow_succ, ← golden_mul_eq]

theorem goldenNorm_pow (x : GoldenInt) (n : ℕ) :
    goldenNorm (x ^ n) = goldenNorm x ^ n := by
  induction n with
  | zero => norm_num [goldenNorm]
  | succ n ih =>
      rw [pow_succ]
      change goldenNorm (goldenMul (x ^ n) x) = _
      rw [goldenNorm_mul, ih, pow_succ]
```

対象ブランチには既存の日英 PDF があるが、本 theorem に対応する具体的ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0197 `goldenNorm_pow`** である。

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

0196 が共役の乗法性を自然数冪へ持ち上げたのに対し、0197 は 0174 `goldenNorm_mul` の乗法性を自然数冪へ持ち上げる。第五冪に対して $N(x^5)=N(x)^5$ を使う後続議論への直接の橋になる。