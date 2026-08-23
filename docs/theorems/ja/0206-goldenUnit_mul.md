# 0206 — `goldenUnit_mul`

## Lean の型

```lean
theorem goldenUnit_mul {x y : GoldenInt}
    (hx : GoldenUnit x) (hy : GoldenUnit y) : GoldenUnit (goldenMul x y) := by
  apply goldenUnit_of_norm_eq_one_or_neg_one
  rw [goldenNorm_mul]
  rcases goldenNorm_eq_one_or_neg_one_of_unit hx with hx' | hx' <;>
    rcases goldenNorm_eq_one_or_neg_one_of_unit hy with hy' | hy' <;>
    simp [hx', hy']
```

これは `theorem` であり、二つの黄金整数 `x`,`y` が `GoldenUnit` なら、その積 `goldenMul x y` も `GoldenUnit` であることを示す。

## 数学的主張・宣言の意味

主張は通常の「単元は乗法について閉じている」という性質である。

$$
GoldenUnit(x)\land GoldenUnit(y)
\Longrightarrow
GoldenUnit(xy).
$$

現行 proof は逆元を直接掛け合わせるのではなく、0198–0202 で確立した黄金ノルムによる unit criterion を使う。

`x`,`y` が unit なら 0202 `goldenNorm_eq_one_or_neg_one_of_unit` により

$$
N(x)\in\{1,-1\},\qquad N(y)\in\{1,-1\}.
$$

0174 `goldenNorm_mul` の乗法性から

$$
N(xy)=N(x)N(y).
$$

右辺は `±1` 同士の積なので再び `±1` である。したがって 0201 `goldenUnit_of_norm_eq_one_or_neg_one` により `xy` は unit となる。

四通りの符号は

$$
1\cdot1=1,\qquad
1\cdot(-1)=-1,\qquad
(-1)\cdot1=-1,\qquad
(-1)\cdot(-1)=1
$$

であり、Lean では最後の `simp` がこの有限場合分けを処理する。

## 証明全体での役割

0205–0207 は `GoldenUnit` の基本的な演算閉性 block を形成する。

- 0205 `goldenUnit_neg` — unit の符号反転も unit。
- 0206 本 theorem — unit 同士の積も unit。
- 0207 `goldenUnit_pow` — unit の自然数冪も unit。

特に 0207 は successor case で本 theorem を直接使う。

```lean
| succ n ih => exact goldenUnit_mul ih hx
```

したがって 0206 は、単なる一般環の常識を再証明するだけではなく、`GoldenUnit` を第五冪まで安定して運ぶための直接的な再帰ステップを提供する。

FLT5 の後段では unit factor と第五冪を組み合わせる場面が現れるため、`GoldenUnit` が乗法と冪に対して閉じていることは、unit-class representatives や golden factorization を扱う基礎 API になる。

## 直接依存する定義・補題

現行 proof が直接依存する主要宣言は次の通りである。

- 0198 `GoldenUnit`
- 0201 `goldenUnit_of_norm_eq_one_or_neg_one`
- 0202 `goldenNorm_eq_one_or_neg_one_of_unit`
- 0174 `goldenNorm_mul`
- 0124 `goldenMul`
- `simp`

依存の論理構造は

$$
GoldenUnit(x),GoldenUnit(y)
\Longrightarrow
N(x),N(y)\in\{\pm1\}
\Longrightarrow
N(xy)=N(x)N(y)\in\{\pm1\}
\Longrightarrow
GoldenUnit(xy)
$$

である。

## 証明の流れ

proof は三段階である。

### 1. unit goal を norm criterion へ移す

```lean
apply goldenUnit_of_norm_eq_one_or_neg_one
```

これにより goal は

```lean
goldenNorm (goldenMul x y) = 1 ∨
  goldenNorm (goldenMul x y) = -1
```

となる。

### 2. 積のノルムを因子のノルム積へ書き換える

```lean
rw [goldenNorm_mul]
```

目標は

```lean
goldenNorm x * goldenNorm y = 1 ∨
  goldenNorm x * goldenNorm y = -1
```

へ変わる。

### 3. 二つの unit hypothesis を `±1` の四場合へ分解する

```lean
rcases goldenNorm_eq_one_or_neg_one_of_unit hx with hx' | hx' <;>
  rcases goldenNorm_eq_one_or_neg_one_of_unit hy with hy' | hy' <;>
  simp [hx', hy']
```

`hx` と `hy` をそれぞれ norm `1` / `-1` の二分岐へ展開し、合計四つの goal を生成する。最後の `simp` が各符号積を評価してすべて閉じる。

## Lean 固有の処理

この proof で特徴的なのは、nested `rcases` と `<;>` の組合せである。

```lean
rcases ... hx with hx' | hx' <;>
  rcases ... hy with hy' | hy' <;>
  simp [hx', hy']
```

最初の `rcases` が二つの goal を作り、`<;>` により後続の `rcases` がその両方へ適用される。第二の `rcases` で各 goal がさらに二分され、最後の `simp` が四つすべてへ適用される。

同じ変数名 `hx'` / `hy'` を各 branch で再利用できるため、明示的に四 case を書くより短い。

また `rw [goldenNorm_mul]` は raw multiplication `goldenMul` と norm API が直接噛み合っているため、そのまま適用できる。標準記法 `x * y` へ変換する `change` は不要である。

## 冗長・重複箇所

数学的には unit の積閉性は一般の環で標準的であり、`GoldenUnit` が Mathlib `IsUnit` と接続されれば、専用 theorem の proof を一般 API に委譲できる可能性が高い。

また現行 proof は二つの unit hypothesis をそれぞれ norm `±1` へ変換し、四通りを `simp` で処理している。これは明快だが、実質的には「`±1` の集合が乗法で閉じている」という同じ小さな事実を theorem 内に埋め込んでいる。

別の冗長性として、0201 と 0202 が合わせて

$$
GoldenUnit(x)\iff N(x)=1\lor N(x)=-1
$$

を構成しているのに、まだ一つの named iff theorem として bundle されていない。これを公開すれば unit closure proofs の表現を統一できる可能性がある。

一方、逆元 witness を直接構成する proof なら、`hx` と `hy` から逆元 `x⁻¹`,`y⁻¹` 相当を取り出し、その積を逆元として使える。可換環なので順序処理も容易であり、norm criterion を往復しない別設計が可能である。

## 最適化候補

1. **現行 norm-based proof を維持する**
   - 0201/0202 と 0174 の API 再利用が明瞭で、proof も短い。

2. **逆元 witness を直接構成する**
   - `GoldenUnit` の existential data を展開し、逆元同士の積を witness にする。
   - norm の四場合分けを避けられる。

3. **unit criterion を iff theorem として公開する**
   - `GoldenUnit x ↔ goldenNorm x = 1 ∨ goldenNorm x = -1` を `rw` / `simp` で利用できるようにする。

4. **`GoldenUnit ↔ IsUnit` bridge を前倒しする**
   - Mathlib の一般的な unit multiplication closure を利用できる可能性がある。

5. **`goldenNorm` を multiplicative map として bundle する**
   - `goldenNorm_mul`、`goldenNorm_pow`、unit criterion を一般的な multiplicative API へ統合できる可能性がある。

6. **`±1` 乗法閉性を helper lemma に分離する**
   - 同種の符号場合分けが増える場合に有効。ただし現状では `simp` が十分短く、過剰抽象化になる可能性もある。

現行 proof は局所的にはかなり良く、最適化余地は theorem 自体よりも `GoldenUnit` / norm API の bundle 化にある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が直接使う Mathlib 表面は主に、

- `rcases`
- `<;>` tactical sequencing
- `simp`
- equality rewriting

である。

整数の高度な定理や `ring` / `norm_num` は本 theorem 自身では直接使用しない。unit criterion と norm multiplicativity は同一 development の上流 theorem として再利用している。

ただし `GoldenDivisibility.lean` module 全体では整数整除、`Int.eq_one_or_neg_one_of_mul_eq_one`、`norm_num`、ring arithmetic 等も利用するため、実際の最小 import は module 単位で測る必要がある。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行の norm `±1` 四場合 proof
- B: 逆元 witness を直接掛け合わせる proof
- C: unit criterion iff + simp による proof
- D: `GoldenUnit ↔ IsUnit` bridge + Mathlib 標準 unit API
- E: multiplicative norm を bundle した抽象 proof

比較軸は、proof 長、case split 数、直接依存、Mathlib 標準 API 再利用率、数学的 provenance、座標 API への依存度、将来の refactor 耐性である。

特に A と B は、「unit を norm `±1` で判定する設計」と「逆元 witness を直接操作する設計」の差を明確に比較できる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

正本 source では 0205 の直後に本 theorem があり、その直後に 0207 `goldenUnit_pow` が続くことを確認した。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的 PDF ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0207 `goldenUnit_pow`** である。

```lean
theorem goldenUnit_pow {x : GoldenInt} (hx : GoldenUnit x) (n : ℕ) :
    GoldenUnit (goldenPow x n) := by
  induction n with
  | zero => exact goldenUnit_one
  | succ n ih => exact goldenUnit_mul ih hx
```

0204 `goldenUnit_one` が冪の基底 case を、0206 本 theorem が successor case の乗法閉性を提供する。これにより任意の unit の自然数冪、特に FLT5 で重要な第五冪も unit であることが帰納的に確立される。