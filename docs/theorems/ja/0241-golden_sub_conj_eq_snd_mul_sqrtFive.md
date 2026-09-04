# 0241 — `golden_sub_conj_eq_snd_mul_sqrtFive`

## Lean の型

```lean
/-- Subtracting the conjugate isolates the square-root-of-five direction. -/
theorem golden_sub_conj_eq_snd_mul_sqrtFive (x : GoldenInt) :
    x - goldenConj x = goldenMul (goldenOfInt x.snd) sqrtFiveElement := by
  apply GoldenInt.ext
  · simp [goldenConj, goldenOfInt, goldenSqrtFive, goldenMul]
  · simp [goldenConj, goldenOfInt, goldenSqrtFive, goldenMul]
    ring
```

これは `theorem` であり、黄金整数 `x` とその共役との差が、第二座標 `x.snd` と `sqrtFiveElement` の積だけで表せることを示す。

## 数学的主張

`x = a + bφ` とする。黄金共役は

$$
\overline{x}=(a+b)-b\varphi
$$

なので、差を取ると

$$
x-\overline{x}
=(a+b\varphi)-((a+b)-b\varphi)
=-b+2b\varphi.
$$

一方、0177 で導入された

$$
\sqrt5=2\varphi-1
$$

に対応する `sqrtFiveElement = goldenSqrtFive = ⟨-1,2⟩` を使えば、

$$
b\sqrt5=b(2\varphi-1)=-b+2b\varphi.
$$

したがって

$$
x-\overline{x}=b\sqrt5.
$$

Lean の statement はこの等式を raw golden API で

```lean
goldenMul (goldenOfInt x.snd) sqrtFiveElement
```

と表している。

## 証明全体での役割

0240 までで、ramifier-stripped packet の `beta` を最終的に

$$
\beta=\varepsilon\gamma^5
$$

と表すことが fifth-power extraction の目標 contract として切り出された。

そのためには `beta` と `goldenConj beta` が相対素であることを証明する必要がある。`SignedGoldenConjugateCoprime.lean` はそのための module であり、本 theorem は最初の座標分解である。

共通因子 `d` が `beta` と `conj beta` の両方を割るなら、0191 `goldenDivides_sub` により

$$
d\mid \beta-\overline\beta
$$

も従う。本 theorem によって差は

$$
\beta-\overline\beta=\beta_{\mathrm{snd}}\sqrt5
$$

と見えるため、そのノルムは次の 0242 で

$$
N(\beta-\overline\beta)=-5\,\beta_{\mathrm{snd}}^2
$$

へ落ちる。さらに stripped packet の

$$
\beta_{\mathrm{snd}}=-5^7a^{10}
$$

を代入すると、差のノルムは

$$
-5^{15}a^{20}
$$

になる。

一方 `N(β)=b^5` なので、共通因子のノルムは `b^5` と `5^15 a^20` の双方を割る。power-split 側の coprimality により、その絶対値は `1` に強制され、最終的に共通因子が unit と判定される。したがって 0241 は conjugate-coprimality proof の入口にある重要な factorization identity である。

## 直接依存する定義・補題

statement と proof が直接依存する主な宣言は次の通りである。

- `GoldenInt`
- 0163 `goldenConj`
- 0162 `goldenOfInt`
- 0177 `goldenSqrtFive`
- 0179 `sqrtFiveElement`
- 0124 `goldenMul`
- `GoldenInt.ext`

proof は既存 theorem を組み合わせるというより、これらの定義を座標まで展開して直接確認している。

概念的な依存は

$$
\text{conjugation formula}
+\sqrt5=2\varphi-1
\Longrightarrow
x-\overline{x}=x_{\mathrm{snd}}\sqrt5
$$

である。

## 証明の流れ

proof は二座標の extensionality に落とす。

```lean
apply GoldenInt.ext
```

これで goal は `fst` と `snd` の二本になる。

第一座標では

```lean
simp [goldenConj, goldenOfInt, goldenSqrtFive, goldenMul]
```

だけで閉じる。定義を展開すると両辺とも `-x.snd` へ正規化される。

第二座標でも同じ定義展開を行い、残った整数多項式等式を

```lean
ring
```

で閉じる。数学的には両辺とも `2 * x.snd` になることを確認している。

## Lean 固有の処理

`GoldenInt.ext` は structure equality を `fst` / `snd` の座標等式へ分解する。この coordinate model では、共役や平方根元の意味を抽象 theorem へ持ち上げるより、定義展開して integer ring arithmetic へ落とす方が短い。

`Simp` の展開対象には `sqrtFiveElement` 自身ではなく `goldenSqrtFive` が指定されている。`sqrtFiveElement` は `abbrev` なので透明に `goldenSqrtFive` へ展開されるためである。

また statement 左辺は標準減算 `x - goldenConj x`、右辺は raw `goldenMul` を使っている。現行 API では raw/standard notation が混在しているが、0158 `golden_sub_eq`、0159 `golden_mul_eq` により定義的・rewrite 的には相互運用できる。

## 冗長・重複箇所

本 theorem は座標定義から直接証明されており、数学的には

$$
x-\overline{x}=b(2\varphi-1)
$$

というほぼ一行の恒等式である。そのため generic quadratic-order conjugation API があれば専用 theorem は自動的に導ける可能性がある。

一方、この named theorem を保持する価値は高い。後続で重要なのは単なる座標差ではなく、差が **平方根5方向に完全に乗る** という factorization だからである。0242 以降はこの形を使って `goldenNorm_mul` と `goldenNorm_sqrtFive` を適用できる。

また `sqrtFiveElement` と `goldenSqrtFive` は alias 層として重複している。public statement では短い `sqrtFiveElement`、proof の unfolding では concrete `goldenSqrtFive` が使われており、内部名と公開名の二層設計が見える。

## 最適化候補

1. **現行 coordinate proof を維持する**
   - 依存が浅く、証明監査が容易である。

2. **標準 ring notation に統一する**

```lean
x - goldenConj x = (x.snd : GoldenInt) * sqrtFiveElement
```

のような statement に寄せられれば generic rewriting と馴染みやすい。ただし整数 cast API の整備が必要になる。

3. **共役を `RingEquiv` として bundle する**
   - 既に involution、加法、乗法、否定、減算、冪保存が揃っているため、quadratic conjugation API を構造化できる。

4. **一般二次環 identity に抽象化する**
   - quadratic extension で `x - conj x` が anti-invariant basis direction に乗る一般 theorem を作れば、黄金整数固有の座標計算を減らせる。

5. **0241–0242 を factor/norm pair として整理する**
   - 0241 の factorization と 0242 の norm formula は常に連続利用されるため、consumer API として一組に整理する余地がある。

現行 proof は非常に短く、局所的な書き換え最適化の優先度は低い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が直接必要とする表面は比較的小さい。

- structure extensionality
- `simp`
- integer ring normalization `ring`
- project 内の `GoldenInt` / conjugation / multiplication / sqrt-five definitions

本 theorem 単独なら `Mathlib` 全体より小さい import で足りる可能性は高い。ただし `SignedGoldenConjugateCoprime.lean` 全体では divisibility、norm、coprimality、`natAbs`、整数・自然数 cast などを利用するため、実際の最小 import は module 全体で測る必要がある。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 `ext + simp + ring` の coordinate proof
- B: `golden_sub_eq` / `golden_mul_eq` を使い標準 notation に寄せる proof
- C: `goldenConj` を `RingEquiv` として bundle した上での抽象 proof
- D: 一般 quadratic-order conjugation theorem の特殊化
- E: `sqrtFiveElement = 2*φ-1` を明示 algebraic rewrite する proof

比較軸は proof 長、直接依存、数学的意味の可視性、raw coordinate API への依存度、Mathlib 標準 algebra API との相互運用性、一般化可能性である。

A は concrete model の監査性が高く、C/D は algebraic structure の再利用性が高い。FLT5 museum ではこの差を比較する題材として良い。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` generated section である。

正本 source では、0240 `SignedGoldenFifthPowerUpToUnitCore` で `SignedGoldenRamifierStripped.lean` が終わった直後に本 module が始まり、本 theorem がその先頭宣言として置かれている。

module コメントは、`beta` と `conj beta` の共通因子が `N(beta)=b^5` と差のノルム `-5^15*a^20` の双方を割ることを利用し、両整数 mass の coprimality から共通因子の norm を `±1` に強制する方針を明示している。

既存の日英 PDF に対応する具体的ページ・節番号は今回直接特定していないため、PDF ページ番号は推測しない。

## 次に読むべき宣言

依存順の次は **0242 `goldenNorm_sub_conj`** である。

```lean
/-- The norm of the conjugate difference is `-5` times the square coordinate. -/
theorem goldenNorm_sub_conj (x : GoldenInt) :
    goldenNorm (x - goldenConj x) = -5 * x.snd ^ 2 := by
  rw [golden_sub_conj_eq_snd_mul_sqrtFive, goldenNorm_mul,
    goldenNorm_sqrtFive]
  simp [goldenNorm, goldenOfInt]
  ring
```

0241 が

$$
x-\overline{x}=x_{\mathrm{snd}}\sqrt5
$$

と factorization したので、0242 はノルム乗法性と $N(\sqrt5)=-5$ を適用して

$$
N(x-\overline{x})=-5x_{\mathrm{snd}}^2
$$

へ移す。これが stripped packet の explicit five-adic mass と共通因子 norm を結ぶ次の橋になる。
