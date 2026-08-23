# 0205 — `goldenUnit_neg`

## Lean の型

```lean
theorem goldenUnit_neg {x : GoldenInt} (hx : GoldenUnit x) : GoldenUnit (-x) := by
  apply goldenUnit_of_norm_eq_one_or_neg_one
  rw [show goldenNorm (-x) = goldenNorm x by simp [goldenNorm]]
  exact goldenNorm_eq_one_or_neg_one_of_unit hx
```

これは `theorem` であり、黄金整数 `x` が `GoldenUnit` なら、その加法逆元 `-x` も `GoldenUnit` であることを示す。

## 数学的主張・宣言の意味

主張は

$$
GoldenUnit(x)\Longrightarrow GoldenUnit(-x)
$$

である。

一般の環でも unit の符号反転は unit であり、もし `y` が `x` の逆元なら `-y` が `-x` の逆元になる。実際、

$$
(-x)(-y)=xy=1.
$$

現行 proof はこの逆元 witness を直接構成せず、0198–0202 で整備した norm criterion を通る。

黄金ノルムは

$$
N(a+b\varphi)=a^2+ab-b^2
$$

という二次形式なので、

$$
N(-x)=N(x)
$$

である。0202 `goldenNorm_eq_one_or_neg_one_of_unit` により `x` が unit なら `N(x)=\pm1`。したがって `N(-x)=\pm1` であり、0201 `goldenUnit_of_norm_eq_one_or_neg_one` に戻せば `-x` も unit となる。

## 証明全体での役割

0198–0204 で unit の定義、norm `±1` criterion、`φ` と `1` の concrete unit certificate が揃った。0205 からは `GoldenUnit` の演算閉性を整備する段階に入る。

source 順では本 theorem の直後に、

- 0206 `goldenUnit_mul`
- 0207 `goldenUnit_pow`

が続く。したがって 0205–0207 は、

$$
\text{unit} \xrightarrow{-} \text{unit},\qquad
\text{unit}\cdot\text{unit}\to\text{unit},\qquad
\text{unit}^n\to\text{unit}
$$

という閉性 block を形成する。

この閉性は後続で単元を第五冪や unit-class representatives と組み合わせる際の基礎 API になる。特に `goldenUnit_pow` は unit の冪が unit であることを帰納的に示すため、0205 は直接その proof に呼ばれなくても、unit API を通常の環演算に対して閉じた形へ整える役割を持つ。

## 直接依存する定義・補題

現行 proof が直接依存するのは次の通りである。

- 0201 `goldenUnit_of_norm_eq_one_or_neg_one`
- 0202 `goldenNorm_eq_one_or_neg_one_of_unit`
- 0164 `goldenNorm`
- `Neg GoldenInt` とその座標 simp API
- `simp`

依存の論理構造は、

$$
GoldenUnit(x)
\Longrightarrow N(x)=\pm1
\Longrightarrow N(-x)=N(x)=\pm1
\Longrightarrow GoldenUnit(-x)
$$

である。

ここで `N(-x)=N(x)` は独立した named theorem を使わず、その場の `show ... by simp [goldenNorm]` で証明している。

## 証明の流れ

proof は三段階である。

### 1. unit goal を norm criterion へ移す

```lean
apply goldenUnit_of_norm_eq_one_or_neg_one
```

により goal

```lean
GoldenUnit (-x)
```

を

```lean
goldenNorm (-x) = 1 ∨ goldenNorm (-x) = -1
```

へ変換する。

### 2. 符号反転で norm が変わらないことを rewrite する

```lean
rw [show goldenNorm (-x) = goldenNorm x by simp [goldenNorm]]
```

局所的に

$$
N(-x)=N(x)
$$

を証明し、goal を

```lean
goldenNorm x = 1 ∨ goldenNorm x = -1
```

へ戻す。

### 3. unit hypothesis を norm `±1` へ射影する

```lean
exact goldenNorm_eq_one_or_neg_one_of_unit hx
```

0202 をそのまま適用して終了する。

## Lean 固有の処理

最も特徴的なのは、

```lean
rw [show goldenNorm (-x) = goldenNorm x by simp [goldenNorm]]
```

という inline theorem の使い方である。

`show ... by ...` により rewrite に必要な等式をその場で構成し、その theorem を `rw` へ渡している。独立した `goldenNorm_neg` theorem を API に追加せず、0205 の局所 proof の中だけで norm invariance under negation を使う設計である。

`simp [goldenNorm]` は `(-x).fst = -x.fst`、`(-x).snd = -x.snd` の既存 simp rules と整数の符号計算を使い、二次形式の符号が相殺されることを正規化する。

また `apply goldenUnit_of_norm_eq_one_or_neg_one` と最後の `exact goldenNorm_eq_one_or_neg_one_of_unit hx` により、0201/0202 が事実上ひとつの bidirectional unit criterion として使われていることが分かる。

## 冗長・重複箇所

本 theorem の数学自体は一般の ring unit API では標準的であり、`GoldenUnit` が Mathlib `IsUnit` と接続されれば専用 proof は不要になる可能性が高い。

現行 source でも後段の `GoldenCoprimeFactor.lean` に

```lean
theorem goldenUnit_iff_isUnit {x : GoldenInt} : GoldenUnit x ↔ IsUnit x := by
  ...
```

が現れるため、長期的には一般 `IsUnit.neg` 相当の API へ寄せる余地がある。

また `N(-x)=N(x)` を inline で再証明している。今後同じ事実が複数箇所で必要なら、

```lean
@[simp] theorem goldenNorm_neg (x : GoldenInt) :
    goldenNorm (-x) = goldenNorm x := by
  simp [goldenNorm]
```

のような named theorem を置けば重複を減らせる。

さらに 0201 と 0202 は実質的に

$$
GoldenUnit(x)\iff N(x)=\pm1
$$

を構成しているので、この iff theorem を一つ公開すれば、0205 はより短い rewrite / simp proof にできる可能性がある。

## 最適化候補

1. **直接逆元 witness を構成する**
   - `hx` から `y` を取り出し、`-y` を `-x` の逆元として与える。
   - norm criterion への往復を避けられる。

2. **`goldenNorm_neg` を named simp theorem にする**
   - 二次形式の符号不変性を再利用可能にする。

3. **unit criterion を iff theorem として公開する**
   - `GoldenUnit x ↔ goldenNorm x = 1 ∨ goldenNorm x = -1` を `rw` / `simp` で使えるようにする。

4. **`GoldenUnit` を `IsUnit` へ統合する**
   - Mathlib 標準の unit closure under negation を利用できる可能性がある。

5. **現行 proof を維持する**
   - 0201/0202 の API が実際に downstream proof を短くする実例として明快であり、監査性は高い。

局所 proof の短さだけなら現行方式は十分優秀で、主な最適化余地は unit API の bundle 化と標準 Mathlib 連携にある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が直接利用する Mathlib 表面は主に、

- `simp`
- equality rewriting
- negation の基本 algebra simp rules

である。

整数ノルムの criterion theorem や `GoldenUnit` 関連は同一 development の上流宣言である。本 theorem 単独なら Mathlib 全体よりかなり小さい import で足りる可能性が高い。

ただし `GoldenDivisibility.lean` module 全体では整数整除、`Int.eq_one_or_neg_one_of_mul_eq_one`、`norm_num`、ring arithmetic なども使用するため、実際の最小 import は module 単位で測る必要がある。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 norm criterion 往復 proof
- B: `GoldenUnit` witness を直接 `-y` へ変換する proof
- C: `goldenNorm_neg` + unit criterion iff を使う proof
- D: `GoldenUnit ↔ IsUnit` bridge 経由で Mathlib 標準 unit API を使う proof
- E: `goldenConj` / norm を bundle した抽象 algebra 設計

比較軸は proof 長、直接依存、Mathlib 標準 API 再利用率、数学的 provenance、座標 API への依存度、将来の refactor 耐性である。

特に A と B は、「ノルムによる unit 判定を中心 API とするか」「逆元 witness の構成を直接使うか」という設計差を明確に比較できる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

正本 source では 0204 の直後に次の順序が確認できる。

```lean
theorem goldenUnit_one : GoldenUnit goldenOne := by
  apply goldenUnit_of_norm_eq_one
  norm_num [goldenNorm, goldenOne]

theorem goldenUnit_neg {x : GoldenInt} (hx : GoldenUnit x) : GoldenUnit (-x) := by
  apply goldenUnit_of_norm_eq_one_or_neg_one
  rw [show goldenNorm (-x) = goldenNorm x by simp [goldenNorm]]
  exact goldenNorm_eq_one_or_neg_one_of_unit hx

theorem goldenUnit_mul {x y : GoldenInt}
    (hx : GoldenUnit x) (hy : GoldenUnit y) : GoldenUnit (goldenMul x y) := by
  ...
```

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的 PDF ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0206 `goldenUnit_mul`** である。

```lean
theorem goldenUnit_mul {x y : GoldenInt}
    (hx : GoldenUnit x) (hy : GoldenUnit y) : GoldenUnit (goldenMul x y) := by
  apply goldenUnit_of_norm_eq_one_or_neg_one
  rw [goldenNorm_mul]
  rcases goldenNorm_eq_one_or_neg_one_of_unit hx with hx' | hx' <;>
    rcases goldenNorm_eq_one_or_neg_one_of_unit hy with hy' | hy' <;>
    simp [hx', hy']
```

0205 が符号反転に対する unit closure を示したのに対し、0206 は二つの unit の積も unit であることを norm `±1` の四通りの符号組合せへ還元する。さらに 0207 `goldenUnit_pow` が 0204 と 0206 を使って unit の自然数冪閉性を完成させる。