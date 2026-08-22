# 0194 — `goldenConj_neg`

## Lean の型

```lean
theorem goldenConj_neg (x : GoldenInt) :
    goldenConj (-x) = -goldenConj x := by
  ext <;> simp [goldenConj, add_comm]
```

これは `theorem` であり、黄金整数の共役 `goldenConj` が加法逆元を保存することを示す。

## 数学的主張

`GoldenInt` の元を

$$
x=a+b\varphi
$$

と書く。0163 `goldenConj` は座標で

$$
(a,b)\longmapsto(a+b,-b)
$$

と定義されている。

一方、

$$
-x=(-a)+(-b)\varphi
$$

なので、これに共役を作用させると

$$
\overline{-x}=(-a-b)-(-b)\varphi=(-a-b)+b\varphi.
$$

また

$$
-\overline{x}=-(a+b-b\varphi)=(-a-b)+b\varphi
$$

であるから、

$$
\overline{-x}=-\overline{x}
$$

が成り立つ。

本 theorem は、0193 `goldenConj_add` に続いて、共役が `GoldenInt` の加法群構造と両立することを明示する。

## 証明全体での役割

共役 API はこれまで段階的に整備されてきた。

- 0168 `goldenConj_ofInt` — 整数軸を固定する。
- 0170 `goldenConj_invol` — 共役は involution。
- 0171 `goldenConj_mul` — 乗法を保存する。
- 0193 `goldenConj_add` — 加法を保存する。
- 0194 `goldenConj_neg` — 否定を保存する。

0194 により、次の `goldenConj_sub` を標準的な加法・否定の組合せとして処理しやすくなる。特に後続の relative-primality argument では `beta - goldenConj beta` のような差を扱うため、共役を差や符号反転の内側へ移動できる API は重要である。

0171、0193、0194 が揃うことで、`goldenConj` は実質的に ring homomorphism の主要な保存則を持つ。0170 の自己逆性まで含めれば、将来的に `RingEquiv GoldenInt GoldenInt` として束ねる設計が自然になる。

## 直接依存する定義・補題

直接依存は次の通りである。

- `GoldenInt`
- 0163 `goldenConj`
- 0122 `goldenNeg` と `Neg GoldenInt` instance
- 0139 `golden_fst_neg`
- 0140 `golden_snd_neg`
- `GoldenInt.ext`
- 整数の加法・否定に対する simp lemma

proof script は `goldenConj` を明示展開し、`ext` と `simp` で両座標を処理する。`add_comm` を simp 集合へ明示的に加えている。

## 証明の流れ

現行 proof は

```lean
by
  ext <;> simp [goldenConj, add_comm]
```

である。

1. `ext` により `GoldenInt` の等式を第一・第二座標の整数等式へ分解する。
2. `simp [goldenConj, add_comm]` で共役の座標定義、否定の projection simp lemma、整数算術を展開・正規化する。
3. 両座標が同じ整数式へ簡約され、goal が閉じる。

0193 `goldenConj_add` では最後に `ring` を使っていたが、0194 は線形な符号操作だけであるため `simp` だけで閉じている。この差は、0194 の algebraic complexity がより低いことをよく表している。

## Lean 固有の処理

`ext` は `@[ext] theorem GoldenInt.ext` を利用し、structure equality を二つの field equality へ変換する。

`<;>` により、`ext` が生成した両 goal に同じ `simp` を適用する。

`simp [goldenConj, add_comm]` は `goldenConj` を unfolding し、`(-x).fst`、`(-x).snd` を既存の `@[simp]` projection lemma により `-x.fst`、`-x.snd` へ落とす。第一座標では加法項の並びが左右で異なり得るため、`add_comm` を追加して正規形を一致させている。

この proof は `goldenConj_add` を直接再利用していない。したがって「加法準同型なら否定も保存する」という抽象群論ではなく、座標実装を直接監査する proof style を採用している。

## 冗長・重複箇所

0193 `goldenConj_add` が既に共役の加法保存を証明しているため、数学的には 0194 は加法群準同型の一般論から導ける性質である。

また、0171 `goldenConj_mul`、0193 `goldenConj_add`、0194 `goldenConj_neg`、次の `goldenConj_sub` と、morphism 的性質が個別 theorem として分散している。

この構成は theorem 数を増やす一方、各性質が明示座標モデル上で直接検証されているため、FLT5 証明の監査性は高い。

## 最適化候補

1. **現行 proof を維持する**
   - 非常に短く、座標モデルの透明性が高い。

2. **0193 から抽象的に導く**
   - `goldenConj_add` と `goldenConj` が零元を固定する事実から、否定保存を加法群一般論で導く設計が考えられる。
   - ただし現行より proof が複雑になる可能性がある。

3. **`goldenConj` を `AddMonoidHom` / `RingHom` として bundle する**
   - `map_neg` を generic theorem として得られ、0194 を wrapper にできる。

4. **`RingEquiv` として bundle する**
   - 0170 `goldenConj_invol` を inverse として使い、共役の構造を一箇所へ集約できる。

5. **`add_comm` が本当に必要かを再検証する**
   - simp normal form が十分なら省略可能な場合がある。ただし今回は Lean build を行わないため未検証である。

局所的には現行 proof が既に十分簡潔であり、最も大きな最適化余地は共役 API 全体の bundle 化にある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem 自身が直接必要とする表面は、

- structure extensionality
- simp
- 整数の加法・否定
- `GoldenInt` の negation projection API
- `goldenConj`

である。`ring`、整除、ノルム、解析 API は本 theorem 自身では不要である。

ただし `GoldenDivisibility.lean` module 全体では整除・ノルム・unit・relative primality まで扱うため、module 全体の最小 import はより広い。今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 `ext <;> simp [goldenConj, add_comm]`
- B: `GoldenInt.ext` を明示して二座標を個別証明
- C: 0193 `goldenConj_add` から加法群一般論で導出
- D: `goldenConj` を `RingHom` として bundle し `map_neg` を利用
- E: `RingEquiv` 化して generic automorphism API を利用

比較軸は、proof 行数、座標実装の可視性、抽象化コスト、generic API 再利用度、下流 theorem の簡潔さ、refactor 耐性である。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

直前の 0193 正本文書では source 順として、

```lean
theorem goldenConj_add (x y : GoldenInt) :
    goldenConj (x + y) = goldenConj x + goldenConj y := by
  ext <;> simp [goldenConj] <;> ring

theorem goldenConj_neg (x : GoldenInt) :
    goldenConj (-x) = -goldenConj x := by
  ext <;> simp [goldenConj, add_comm]
```

が確認されている。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0195 `goldenConj_sub`** である。

0193 が加法保存、0194 が否定保存を与えたので、次は

$$
\overline{x-y}=\overline{x}-\overline{y}
$$

を明示する段階になる。これは `beta` と `goldenConj beta` の差を扱う後続の relative-primality argument に直接つながる。
