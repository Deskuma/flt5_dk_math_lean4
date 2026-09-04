# 0272 — `signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector`

## 宣言種別

これは **`theorem`** である。

0271 `SignedGoldenUnitFifthPowerExclusion` が「packet の `beta` は unit × fifth power ではありえない」という再利用可能な `Prop` の型だけを定めたのに対し、本 theorem はその contract を、

- unit の mod-fifth class 分類 `GoldenUnitClassesModFifth`
- zero sector 排除 `SignedGoldenZeroSectorExclusion`
- 既に証明済みの nonzero sector 排除

から実際に構築する。

## Lean の型

```lean
/-- Unit classification plus the zero-sector theorem excludes every unit-times-fifth-power. -/
theorem signedGoldenUnitFifthPowerExclusion_of_unitClasses_of_zeroSector
    (hClasses : GoldenUnitClassesModFifth)
    (hZero : SignedGoldenZeroSectorExclusion) :
    SignedGoldenUnitFifthPowerExclusion := by
  intro u v w p epsilon gamma hepsilon hbeta
  obtain ⟨i, delta, hdelta⟩ := hClasses epsilon hepsilon
  let theta := goldenMul delta gamma
  have hSector : p.beta =
      goldenMul (goldenPow goldenPhi i.val) (goldenPow theta 5) := by
    rw [hbeta, hdelta]
    simp only [theta, golden_mul_eq, golden_pow_eq, mul_pow]
    ring
  by_cases hi : i = 0
  · subst i
    apply hZero p theta
    simpa [goldenPhi_pow_zero, golden_mul_eq] using hSector
  · exact signedGolden_nonzero_unitSector_false p hi theta hSector
```

型を数学的に読むと、

$$
\text{GoldenUnitClassesModFifth}
\land
\text{SignedGoldenZeroSectorExclusion}
\Longrightarrow
\text{SignedGoldenUnitFifthPowerExclusion}
$$

である。

つまり、すべての golden unit が fifth power を法として

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

のいずれかに分類でき、さらに sector $0$ すなわち pure fifth-power case が排除できるなら、packet の `beta` が任意の unit times fifth power である可能性をすべて排除できる。

## 数学的主張の意味

`GoldenUnitClassesModFifth` は、任意の unit $\epsilon$ に対して

$$
\epsilon=\varphi^i\delta^5,
\qquad i\in\{0,1,2,3,4\}
$$

と表せるという分類 contract である。

ここで contradiction の入力として

$$
\beta=\epsilon\gamma^5
$$

を仮定する。unit 分類を代入すると

$$
\beta
=\varphi^i\delta^5\gamma^5
=\varphi^i(\delta\gamma)^5.
$$

そこで

$$
\theta:=\delta\gamma
$$

と置けば、問題は有限個の sector

$$
\beta=\varphi^i\theta^5,
\qquad i\in\mathrm{Fin}(5)
$$

へ完全に還元される。

あとは $i=0$ と $i\neq0$ の二つだけである。

- $i=0$ なら $\varphi^0=1$ なので $\beta=\theta^5$。これは `hZero` が排除する。
- $i\neq0$ なら sector $1,2,3,4$ のいずれかであり、`signedGolden_nonzero_unitSector_false` が排除する。

したがって unit × fifth power の全可能性が閉じる。

## 証明全体での役割

本 theorem は signed golden branch における **有限 sector 分解の closure point** である。

これまでの流れは概念的に次のように整理できる。

1. golden unit を fifth powers modulo で有限個の代表 $\varphi^i$ に分類する。
2. sector $1$–$4$ の第二座標を具体計算する。
3. packet の five-adic second-coordinate invariant と比較して nonzero sectors を排除する。
4. sector $0$ は独立した zero-sector arithmetic / descent に委ねる。
5. 本 theorem がその二系統を合流させ、`SignedGoldenUnitFifthPowerExclusion` を生成する。

つまり本 theorem 自身は新しい局所数論を発見する箇所ではない。むしろ、それまで分割されていた finite unit classification と zero-sector theorem を再結合し、後段が一つの contradiction API として利用できる形にする **論理的な接着剤** である。

この contract はさらに downstream の primitive packet refuter へ渡される。

## 直接依存する定義・補題

### `GoldenUnitClassesModFifth`

正本では次の `Prop` である。

```lean
abbrev GoldenUnitClassesModFifth : Prop :=
  ∀ epsilon : GoldenInt,
    GoldenUnit epsilon →
    ∃ i : Fin 5, ∃ delta : GoldenInt,
      epsilon = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

本 proof の

```lean
obtain ⟨i, delta, hdelta⟩ := hClasses epsilon hepsilon
```

がこの分類を直接消費する。

### `SignedGoldenZeroSectorExclusion`

正本では

```lean
abbrev SignedGoldenZeroSectorExclusion : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    (gamma : GoldenInt),
    p.beta = goldenPow gamma 5 → False
```

であり、sector $0$ の pure fifth power を排除する contract である。

### `SignedGoldenUnitFifthPowerExclusion`

0271 で定義された conclusion contract である。

```lean
abbrev SignedGoldenUnitFifthPowerExclusion : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    (epsilon gamma : GoldenInt),
    GoldenUnit epsilon →
    p.beta = goldenMul epsilon (goldenPow gamma 5) →
    False
```

### `signedGolden_nonzero_unitSector_false`

sector $1$–$4$ を一括排除する theorem である。

本 theorem は `i ≠ 0` branch で

```lean
exact signedGolden_nonzero_unitSector_false p hi theta hSector
```

とそのまま利用する。

### `goldenPhi_pow_zero`

sector $0$ で

$$
\varphi^0=1
$$

を concrete golden coordinate へ簡約するために使われる。

### `goldenMul`, `goldenPow`, `golden_mul_eq`, `golden_pow_eq`

project-side golden arithmetic API と underlying ring operation の橋渡しである。

特に `mul_pow` により

$$
\delta^5\gamma^5=(\delta\gamma)^5
$$

へまとめるために使われる。

## 証明の流れ

### 1. exclusion contract の引数を展開

```lean
intro u v w p epsilon gamma hepsilon hbeta
```

0271 の `abbrev` は transparent なので、結論 `SignedGoldenUnitFifthPowerExclusion` を unfolding command なしに直接 `intro` できる。

ここで

```lean
hepsilon : GoldenUnit epsilon
hbeta : p.beta = goldenMul epsilon (goldenPow gamma 5)
```

を得る。

### 2. unit を有限 sector に分類

```lean
obtain ⟨i, delta, hdelta⟩ := hClasses epsilon hepsilon
```

により

```lean
i : Fin 5
delta : GoldenInt
hdelta : epsilon =
  goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

を得る。

### 3. fifth-power base を吸収する

```lean
let theta := goldenMul delta gamma
```

と置く。

これは数学的には $\theta=\delta\gamma$ である。

すると `hbeta` と `hdelta` から

$$
\beta=\varphi^i\theta^5
$$

を作ればよい。

### 4. sector normal form を構築

```lean
have hSector : p.beta =
    goldenMul (goldenPow goldenPhi i.val) (goldenPow theta 5) := by
  rw [hbeta, hdelta]
  simp only [theta, golden_mul_eq, golden_pow_eq, mul_pow]
  ring
```

`rw` で unit classification を代入し、project-side API を ring operation へ下ろし、`mul_pow` で fifth powers を結合し、最後の積の結合・交換を `ring` で正規化している。

### 5. `i = 0` と `i ≠ 0` に分岐

```lean
by_cases hi : i = 0
```

有限五分類を全ケース `fin_cases` するのではなく、zero sector と nonzero sectors の二分類だけを行う。これは proof architecture によく合っている。

### 6. zero sector

```lean
· subst i
  apply hZero p theta
  simpa [goldenPhi_pow_zero, golden_mul_eq] using hSector
```

`i=0` を代入し、`hSector` を

$$
\beta=\theta^5
$$

へ簡約して `hZero` に渡す。

### 7. nonzero sectors

```lean
· exact signedGolden_nonzero_unitSector_false p hi theta hSector
```

sector $1$–$4$ の全算術は既存 theorem に委譲する。

この branch が一行で閉じるのは、直前までの sector arithmetic が良い abstraction boundary を形成している証拠である。

## Lean 固有の処理

### `abbrev` の透明性

conclusion は `SignedGoldenUnitFifthPowerExclusion` という名前だが、`intro` がそのまま通る。これは 0271 が theorem ではなく transparent な `abbrev : Prop` として設計されているためである。

### `obtain`

nested existential

```lean
∃ i : Fin 5, ∃ delta : GoldenInt, ...
```

を

```lean
obtain ⟨i, delta, hdelta⟩ := ...
```

で一度に分解している。

### `let theta`

`delta * gamma` をそのまま証明全体に反復せず、新たな local name として保持する。後段の `hZero` と nonzero-sector theorem の双方が同じ fifth-power base を受け取れる。

### project API から ring API への降下

```lean
simp only [theta, golden_mul_eq, golden_pow_eq, mul_pow]
ring
```

により `goldenMul` / `goldenPow` の表記を underlying multiplication / power へ変換して algebraic normalization を行う。

### `by_cases hi : i = 0`

`i : Fin 5` に対して `fin_cases i` を使わず、proof architecture に必要な区別だけを作っている。

これは 5 sector のうち 4 個を既存 theorem が一括処理できるため、非常に自然である。

### `subst i`

zero branch では `i = 0` を環境へ rewrite し、`Fin 5` の zero representative を concrete exponent `0` に落とす。

## 冗長・重複箇所

proof 本体は比較的よく整理されており、大きな冗長性はない。

特に nonzero sectors を再度 `fin_cases` せず、`signedGolden_nonzero_unitSector_false` に委譲しているため、0264–0268 の coordinate arithmetic をここで繰り返していない点は良い。

考えられる小さな重複は `hSector` の構築である。同じ unit-class normalization

$$
\epsilon=\varphi^i\delta^5,
\qquad
\epsilon\gamma^5=\varphi^i(\delta\gamma)^5
$$

は、近接する finite-sector core theorem でも現れる。正本 standalone source には同型の

```lean
obtain ⟨i, delta, hdelta⟩ := hClasses epsilon hepsilon
refine ⟨i, goldenMul delta gamma, ?_⟩
rw [hbeta, hdelta]
simp only [golden_mul_eq, golden_pow_eq]
rw [mul_pow]
ring
```

という構築も存在する。

したがって将来的には「unit-times-fifth-power representation を canonical `Fin 5` sector representation に変換する」補題を一つ抽出できる余地がある。

ただし現状の proof は短いため、抽象化によってかえって navigation cost が増える可能性もある。

## 最適化候補

### 1. sector normalization helper の抽出

例えば概念的に

```lean
lemma unitFifthPower_to_sector
    (hClasses : GoldenUnitClassesModFifth)
    (hepsilon : GoldenUnit epsilon)
    (hbeta : p.beta = goldenMul epsilon (goldenPow gamma 5)) :
    ∃ i : Fin 5, ∃ theta : GoldenInt,
      p.beta = goldenMul (goldenPow goldenPhi i.val) (goldenPow theta 5) := ...
```

のような helper があれば、本 theorem と finite-sector core の重複を減らせる。

### 2. `ring` を避けられる可能性

`GoldenInt` の乗法が commutative ring として十分 expose されているなら、`mul_pow` と `mul_assoc` 等の rewrite だけで閉じる形にできる可能性がある。

ただし現行 `ring` は意図が明瞭で堅牢であり、最適化の優先度は低い。

### 3. zero/nonzero 二分は維持すべき

ここを `fin_cases i` で 5 branch に展開するのはコード量を増やし、既存 abstraction を壊すため、最適化にはならない。

### 4. `theta` の local definition は妥当

inline 化して `goldenMul delta gamma` を各所に書くより、現行の方が mathematical reading が良い。

## 必要 Mathlib import と import 最適化候補

確認できた generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

manifest 上、本 theorem は `DkMath/FLT/Five/SignedGoldenSectorArithmetic.lean` section に属する。

本 proof が直接利用する Lean / Mathlib 側の主要機能は、

- `Fin 5`
- existential elimination (`obtain`)
- local definitions (`let`)
- equality rewriting (`rw`, `subst`)
- `by_cases`
- `simp` / `simpa`
- `mul_pow`
- `ring`

である。

特に tactic dependency としては `ring` が必要である。

一方、正本 repository では source modules を standalone artifact へ結合した状態を確認しており、元の `SignedGoldenSectorArithmetic.lean` 単独の import 行はこの artifact からは確定できない。したがって最小 Mathlib import 集合は **未確認** である。

import 最適化を行うなら、`Mathlib` umbrella import から `ring`、basic algebra、`Fin`、必要 project modules へ段階的に削る必要があるが、本タスクでは Lean build を行わないため、コンパイル検証済みの最小集合は提示しない。

## Comparator challenge 化の可否

**適している。**

0271 の `abbrev` 単独よりも challenge として価値が高い。

理由は、短い proof の中に

1. existential unit classification の unpack
2. fifth powers の吸収
3. finite sector normal form の構築
4. zero / nonzero sector の論理分岐
5. downstream contradiction theorem の再利用

が含まれており、証明設計を問えるからである。

良い challenge 形式は、statement と以下の dependency を与えて proof body を穴埋めさせる形である。

```lean
hClasses : GoldenUnitClassesModFifth
hZero : SignedGoldenZeroSectorExclusion
signedGolden_nonzero_unitSector_false
goldenPhi_pow_zero
```

難度を上げるなら `theta` の導入方法や `hSector` の中間 statement を隠すとよい。

一方、`GoldenUnitClassesModFifth` や `SignedGoldenUnitFifthPowerExclusion` の定義まで隠すと、challenge は API 探索問題へ寄り過ぎる。

## PDF との対応

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在することを確認した。

ただし今回の実行環境では GitHub 上の PDF binary を本文解析可能な形で取得できず、本 theorem に対応する具体的な PDF ページ番号・節番号・文章との一対一対応は確認できなかった。

したがって PDF に関する具体的対応は推測していない。

本解説の技術的内容は、対象ブランチの generated standalone Lean source と、そこに明示された source-module boundary を主根拠としている。

## 次に読むべき宣言

正本 Lean source で本 theorem の直後は `SignedGoldenSectorArithmetic.lean` section が終了し、次の `SignedGoldenZeroSector.lean` section に入る。

依存順で次に読むべき宣言は

```lean
theorem SignedGoldenRamifierStrippedPacket.zeroSector_gamma_norm_eq_or_eq_neg
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    goldenNorm gamma = (p.exceptional.powerSplit.b : ℤ) ∨
      goldenNorm gamma = -(p.exceptional.powerSplit.b : ℤ) := by
  apply p.gamma_norm_eq_or_eq_neg goldenUnit_one
  rw [hbeta]
  ext <;> simp [goldenOne, goldenMul]
```

である。

本 theorem 0272 で「nonzero sectors はすべて既に排除済みで、残る問題は zero sector だけ」という境界が完成した。次の宣言から、その zero sector を実際に潰すための arithmetic invariant の展開へ進む。