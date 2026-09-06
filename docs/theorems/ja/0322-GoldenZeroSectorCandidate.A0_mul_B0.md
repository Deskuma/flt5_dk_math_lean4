# 0322 — `GoldenZeroSectorCandidate.A0_mul_B0`

## 宣言種別

これは **`theorem`** である。

0316–0321 で構築した正の自然数代表 `A0`, `B0` に対して、もともと `ℤ` 上で得られていた zero-sector inversion の積恒等式を、そのまま `ℕ` 上の積恒等式へ移す cast bridge である。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- Natural product identity inherited from the positive integer factors. -/
theorem A0_mul_B0 (p : GoldenZeroSectorCandidate) :
    p.A0 * p.B0 = 4 * zeroSectorQ p.c ^ 5 := by
  have hprod := p.factor_product
  rw [← p.A0_cast, ← p.B0_cast] at hprod
  exact_mod_cast hprod
```

型は

```lean
p.A0 * p.B0 = 4 * zeroSectorQ p.c ^ 5
```

であり、両辺は `ℕ` である。

ここで

- `p.A0 : ℕ`
- `p.B0 : ℕ`
- `zeroSectorQ p.c : ℕ`

なので、結論は完全に自然数算術の世界に戻っている。

## 数学的主張

zero-sector inversion の signed factor を

$$
A=\operatorname{zeroSectorA}(r,s,d),\qquad
B=\operatorname{zeroSectorB}(r,s,d)
$$

と書く。

上流では整数上で

$$
AB=4Q^5
$$

という積恒等式が証明済みである。ここで

$$
Q=\operatorname{zeroSectorQ}(c).
$$

一方、0316–0319 で自然数代表

$$
A_0=|A|,\qquad B_0=|B|
$$

を導入し、0318 `A0_cast` と 0319 `B0_cast` により

$$
(A_0:\mathbb Z)=A,
$$

$$
(B_0:\mathbb Z)=B
$$

を得ている。

したがって signed product identity の $A,B$ をそれぞれ $A_0,B_0$ の整数 cast へ置換すれば

$$
(A_0:\mathbb Z)(B_0:\mathbb Z)=4(Q:\mathbb Z)^5
$$

となる。両辺が自然数 cast から来ているので、整数上の equality を自然数へ引き戻して

$$
A_0B_0=4Q^5
$$

を得る。

本 theorem の数学的内容そのものは「既知の整数恒等式を、正性によって正しい自然数代表へ移した」というものである。新しい因数分解を発見しているのではなく、後続の自然数上の可除性・互いに素性・二進付値・5乗分解が扱いやすい形へ API を変換している。

## 証明全体での役割

本 theorem は zero-sector inversion の **signed integer phase** と **natural factorization phase** の境界にある。

ここまでに

$$
0<A<B,
$$

$$
AB=4Q^5,
$$

$$
B-A=8d^5
$$

という整数因子の情報が得られている。

さらに 0316–0321 により

$$
A_0,B_0\in\mathbb N_{>0},
$$

$$
(A_0:\mathbb Z)=A,
$$

$$
(B_0:\mathbb Z)=B
$$

が整備された。

本 0322 は、その最初の実質的な成果として積恒等式を

$$
A_0B_0=4Q^5
$$

へ変換する。

この形は後続の `GoldenZeroSectorInversionPacket` で `factor_product` フィールドとして保持され、さらに factorization module では共通奇素因子の排除、2進因子の配分、各因子の fifth-power splitting に直接使われる。

特に後続コードでは

```lean
rw [p.factor_product]
```

のように自然数 divisibility の文脈で直接利用できるため、ここで `ℤ` を完全に追い出しておくことが重要である。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate.factor_product`

proof の起点である。

```lean
have hprod := p.factor_product
```

により、signed integer factors について既に証明済みの積恒等式を取得する。

数学的には

$$
AB=4Q^5
$$

に対応する。

本実行で確認した standalone 正本では、この theorem は本宣言より上流で定義されており、本 theorem はその内容を再証明せず再利用している。

### `GoldenZeroSectorCandidate.A0_cast`

0318 の theorem で、

```lean
(p.A0 : ℤ) = zeroSectorA p.r p.s p.d
```

を与える。

すなわち

$$
(A_0:\mathbb Z)=A.
$$

本 theorem では rewrite を逆向きに使い、`A` を `(p.A0 : ℤ)` へ置換する。

### `GoldenZeroSectorCandidate.B0_cast`

0319 の theorem で、

```lean
(p.B0 : ℤ) = zeroSectorB p.r p.s p.d
```

を与える。

すなわち

$$
(B_0:\mathbb Z)=B.
$$

こちらも rewrite を逆向きに使う。

### `zeroSectorQ`

右辺の fifth-power base を与える自然数値である。本 theorem では定義を展開せず opaque な API として保持されている。

### `exact_mod_cast`

整数上で自然数 cast 同士の equality になった `hprod` を、最終ゴールである自然数 equality へ移す Lean tactic である。

## 証明の流れ

1. `p.factor_product` を `hprod` として取得する。
2. `rw [← p.A0_cast, ← p.B0_cast] at hprod` により、signed factors `A`, `B` を自然数代表の整数 cast `(A0 : ℤ)`, `(B0 : ℤ)` に置換する。
3. この時点で `hprod` は実質的に

   ```lean
   (p.A0 : ℤ) * (p.B0 : ℤ) = 4 * (zeroSectorQ p.c : ℤ) ^ 5
   ```

   という形になる。
4. ゴールは

   ```lean
   p.A0 * p.B0 = 4 * zeroSectorQ p.c ^ 5
   ```

   という `ℕ` equality である。
5. `exact_mod_cast hprod` が cast を正規化し、整数 equality を自然数 equality へ戻して証明を完了する。

証明はわずか 3 行だが、FLT5 証明全体では型境界を越える重要な接続点になっている。

## Lean 固有の処理

### `have hprod := ...`

元の theorem の型を手書きせず、Lean に推論させて局所仮定として保存している。後続 rewrite の対象を明示的に分離することで、元 theorem 自体を変更せず加工できる。

### 逆向き rewrite `←`

```lean
rw [← p.A0_cast, ← p.B0_cast] at hprod
```

が本 proof の中心である。

`A0_cast` の向きは

```lean
(p.A0 : ℤ) = A
```

なので、そのまま `rw [p.A0_cast]` とすると `(p.A0 : ℤ)` を `A` へ変換する。ここでは逆に signed expression `A` を natural representative の cast へ戻したいため、`←` が必要になる。

### `exact_mod_cast`

`ℕ` と `ℤ` の間の coercion を人手で一つずつ整理せず、cast 正規化後に元の equality をゴールへ輸送する。

この theorem では非線形項として積と 5 乗が存在するが、`exact_mod_cast` は数論的内容を解くのではなく、既に同じ式であることが分かっている equality の型変換を担当している。

## 冗長・重複箇所

proof script 自体にはほぼ冗長性がない。

```lean
have hprod := p.factor_product
rw [← p.A0_cast, ← p.B0_cast] at hprod
exact_mod_cast hprod
```

は「取得 → cast representative へ rewrite → 型を戻す」という役割分担が明確である。

理論上は `simpa` や `norm_cast` 系 tactic を組み合わせて短縮できる可能性があるが、現在の 3 行は各段階の意味が読みやすく、特に theorem museum の観点では型境界が可視化されている利点が大きい。

また `A0_pos` / `B0_pos` は本 theorem の proof term から直接は参照されない。これは冗長ではない。正性は `A0_cast` / `B0_cast` を成立させる上流で既に消費されており、本 theorem の段階では「正しい cast equality」が API として与えられているからである。

## 最適化候補

最も自然な比較対象は、局所仮定 `hprod` を作らず一度に処理する proof である。概念的には

```lean
  have hprod := p.factor_product
  norm_cast at hprod ⊢
  ...
```

または `simpa` と cast lemma を組み合わせる形が考えられる。

しかし本 theorem の場合、現在の `rw` + `exact_mod_cast` は非常に短く、しかも意図が明瞭なので、短縮による実益は小さい。

別の設計案として、上流の signed product theorem と natural product theorem を一つの generic cast helper で結ぶこともできる。ただし `A0`, `B0` は zero-sector inversion 固有の意味を持つため、専用 theorem として名前を付けておく方が後続 API は読みやすい。

これらの代替案は本作業では Lean build を行っていないため **未検証** である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem 自身が Mathlib から直接必要とする中心機能は

- `rw`
- `exact_mod_cast`
- `ℕ` から `ℤ` への coercion
- multiplication / power に対する cast 正規化

である。

project 側依存は

- `GoldenZeroSectorCandidate.factor_product`
- `GoldenZeroSectorCandidate.A0_cast`
- `GoldenZeroSectorCandidate.B0_cast`
- `zeroSectorQ`

である。

本 theorem 単体なら `Mathlib` 全体より狭い import にできる可能性が高い。特に `exact_mod_cast` / norm-cast infrastructure と `Nat` / `Int` の algebraic cast 基盤を含む module が候補になる。

ただし standalone 全体の dependency closure、および `factor_product` 等の上流宣言が要求する import まで含めた **正確な最小 import 集合は Lean build なしには確認していない**。従って import 最適化は未検証候補である。

## Comparator challenge 化の可否

**可能。小型だが、Lean の型境界処理を比較する challenge として良質である。**

比較候補は

1. 現行の `rw [← A0_cast, ← B0_cast]` + `exact_mod_cast`
2. `norm_cast` 中心の proof
3. `simpa` と cast lemma を明示的に組み合わせる proof
4. generic helper theorem を先に作り、それを適用する proof

である。

評価軸は単純な行数だけではなく、

- `ℕ` / `ℤ` 境界が読者に見えるか
- 上流 API をそのまま再利用できているか
- cast automation への依存が過剰でないか
- エラー時にどの段階で型不一致が起きたか分かりやすいか
- 後続の定義変更に耐えやすいか

を見るのがよい。

特に Comparator では、数学部分を変えずに「同じ equality を異なる型へどう輸送するか」を比較できるため、Lean 学習教材としても価値がある。

## PDF との照合

対象 branch の repository tree には既存の日英 PDF

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを今回あらためて確認した。

ただし GitHub コネクタの通常の text fetch は binary PDF 本文を返さず、今回の取得経路でも PDF 本文を直接解析できなかった。そのため 0322 `A0_mul_B0` に対応する具体的ページ・節・式番号は **未確認** であり、推測していない。

本解説の Lean code、宣言順、`factor_product` / `A0_cast` / `B0_cast` への依存、および直後の `B0_eq_A0_add` は、最新 branch の `Flt5DkMath/FLT5StandAlone.lean` を正本として確認した。

standalone の生成コメントから、この領域は元の ordered source modules のうち `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` に対応する generated section に属することも確認できる。

## 次に読むべき宣言

次の宣言は 0323 `GoldenZeroSectorCandidate.B0_eq_A0_add`、種別は **`theorem`** である。

Lean 正本では本 theorem の直後に

```lean
/-- Additive natural form of the factor difference, avoiding subtraction. -/
theorem B0_eq_A0_add (p : GoldenZeroSectorCandidate) :
    p.B0 = p.A0 + 8 * p.d ^ 5 := by
  have hdiff := p.factor_difference
  have hcasts : (p.B0 : ℤ) =
      (p.A0 : ℤ) + 8 * (p.d : ℤ) ^ 5 := by
    rw [p.A0_cast, p.B0_cast]
    linarith
  exact_mod_cast hcasts
```

と続く。

0322 が signed product identity を自然数積へ移したのに対し、0323 は signed difference

$$
B-A=8d^5
$$

を subtraction-free な自然数加法形

$$
B_0=A_0+8d^5
$$

へ移す。これで自然数 factorization packet に必要な積と差の二本柱が揃う。
