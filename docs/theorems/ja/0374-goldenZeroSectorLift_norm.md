# 0374 `goldenZeroSectorLift_norm`

## 宣言種別

`theorem`

## Lean コード

```lean
theorem goldenZeroSectorLift_norm (x : GoldenInt) :
    goldenNorm (goldenZeroSectorLift x) =
      goldenFifthSndFactor x.fst x.snd := by
  simp only [goldenZeroSectorLift, goldenNorm, goldenFifthSndFactor]
  ring
```

## Lean の型

```lean
goldenZeroSectorLift_norm :
  (x : GoldenInt) →
    goldenNorm (goldenZeroSectorLift x) =
      goldenFifthSndFactor x.fst x.snd
```

任意の黄金整数 `x : GoldenInt` に対して、0372 `goldenZeroSectorLift` の黄金ノルムが、第五冪の第二座標に現れる quartic factor `goldenFifthSndFactor` と一致することを述べる。

数学的に `x=(r,s)` とし、

$$
T(r,s)=\bigl(r^2+rs+s^2,\ s^2\bigr)
$$

と書けば、本定理は

$$
N\bigl(T(r,s)\bigr)=H(r,s)
$$

という恒等式である。

## 数学的主張の意味

この theorem は zero-sector descent の **代数的再入点** である。

第五冪 `gamma^5` の第二座標は、可視因子 `5s` と quartic factor `H(r,s)` に分解される。一方 0372 の quadratic lift `T` は、まさにその quartic factor が黄金整数の norm になるように設計されている。

黄金ノルムを

$$
N(a,b)=a^2+ab-b^2
$$

と書き、

$$
a=r^2+rs+s^2,
\qquad
b=s^2
$$

を代入すると、

$$
N(T(r,s))
=
(r^2+rs+s^2)^2
+(r^2+rs+s^2)s^2
-s^4.
$$

これを展開整理すると、`goldenFifthSndFactor r s` の quartic polynomial に一致する。

したがって、整数多項式として見えていた `H(r,s)` を黄金整数の norm に読み替えられる。これにより後続では、`H(r,s)=D^5` という fifth-power 情報を、黄金整数環での「積が第五冪」という因数分解問題へ運ぶことができる。

## 証明全体での役割

`SignedGoldenZeroSectorDescent.lean` では、zero sector で残った quartic 条件をそのまま整数論だけで処理せず、再び黄金整数環へ戻す。

流れは概念的に

$$
H(r,s)=D^5
\Longrightarrow
N(T(r,s))=D^5
\Longrightarrow
T(r,s)\overline{T(r,s)}=D^5
$$

となる。

本定理は第一の矢印、すなわち

$$
H(r,s)
\longleftrightarrow
N(T(r,s))
$$

を担う。

直後の 0375 `goldenZeroSectorLift_mul_conj` は `golden_mul_conj` と本定理を組み合わせ、

```lean
goldenMul (goldenZeroSectorLift x)
  (goldenConj (goldenZeroSectorLift x)) =
    goldenOfInt (goldenFifthSndFactor x.fst x.snd)
```

へ持ち上げる。そこで norm identity が黄金整数環の積 identity に変換される。

## 直接依存する定義・補題

### `goldenZeroSectorLift`

```lean
def goldenZeroSectorLift (x : GoldenInt) : GoldenInt :=
  ⟨x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2, x.snd ^ 2⟩
```

quartic factor を norm に戻すために設計された二次写像である。

### `goldenNorm`

`GoldenInt` の黄金ノルム。明示座標では二次形式として定義されている。本 theorem では `simp only` により定義展開される。

### `goldenFifthSndFactor`

黄金第五冪の第二座標から可視因子 `5*s` を除いた quartic polynomial。本 theorem の右辺そのものである。

### `ring`

定義展開後の整数係数多項式恒等式を正規化して閉じる Mathlib tactic である。

## 証明の流れ

証明は二段階である。

```lean
simp only [goldenZeroSectorLift, goldenNorm, goldenFifthSndFactor]
```

で三つの定義をすべて展開し、structure projection も簡約する。すると goal は `x.fst` と `x.snd` に関する純粋な整数多項式恒等式になる。

次に

```lean
ring
```

で両辺を同じ正規形へ変換して終了する。

したがってこの証明では、数論的補題や divisibility、coprimality はまだ使用しない。内容は「後段で使う algebraic bridge が正しい形に設計されている」ことの厳密な多項式検証である。

## Lean 固有の処理

### `simp only`

通常の `simp` ではなく `simp only` を使っているため、展開対象は明示された三定義に限定される。意図しない simp lemma に依存しにくく、standalone 化や Comparator challenge 化に向く。

### structure projection の簡約

`goldenZeroSectorLift x` を展開すると `GoldenInt` constructor が現れ、その `.fst` / `.snd` は kernel reduction により対応する座標式へ簡約される。

### `ring` による反射的多項式証明

手計算の展開を theorem 列として記述せず、可換環上の polynomial normalization に委ねている。ここでは `ℤ` 上なので `ring` の適用条件を満たす。

## 冗長・重複箇所

証明コードそのものは短く、明白な冗長性はない。

ただし `goldenZeroSectorLift` がこの norm identity を成立させるために設計されているため、定義と theorem は数学的には強く結び付いている。0373 `goldenZeroSectorLift_snd` と合わせて、lift の二つの重要な性質を named API として分離している形である。

これは重複というより、後続証明が lift の実装詳細を毎回展開せずに済むようにする抽象化である。

## 最適化候補

### 1. `[simp]` 属性の付与

本定理を `[simp]` にする案は慎重でよい。norm を自動的に quartic factor へ展開したい箇所では便利だが、逆向きに norm 形式を保持したい descent 証明では自動書き換えがかえって邪魔になる可能性がある。

現在の named rewrite theorem のままの方が、再入する瞬間を明示できる。

### 2. `simpa` / `ring_nf` への置換

現状の

```lean
simp only [...]
ring
```

は役割分担が明瞭である。`ring_nf` 一発へ寄せることは可能性としてあるが、定義展開を別途必要とするため、現在の二段構成の方が読みやすい。

### 3. quartic identity の独立 lemma 化

もし同じ polynomial identity を黄金整数環の外でも再利用するなら、

```lean
(r^2 + r*s + s^2)^2 + ... = goldenFifthSndFactor r s
```

という純粋な `ℤ` lemma を独立させ、本 theorem をその corollary にする設計も可能である。ただし現正本では、この identity の主目的は norm re-entry なので追加抽象化の実益は未確認である。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

本 theorem 単体で必要なのは概ね、

- `GoldenInt` とその座標 projection
- `goldenZeroSectorLift`
- `goldenNorm`
- `goldenFifthSndFactor`
- 整数環上の冪・加減乗算
- `simp only`
- `ring`

である。

従って `import Mathlib` はこの一宣言には広い。特に tactic 側では `ring` を提供する import が中心になる。

ただし `SignedGoldenZeroSectorDescent.lean` 全体では後続で divisibility、coprimality、`omega`、`norm_num`、`exact_mod_cast` なども使うため、モジュール単位の最小 import はより広くなる。Lean ビルドを行わない条件なので、厳密な最小 import は確定していない。

## Comparator challenge 化の可否

**非常に適している。**

例えば必要な三定義だけを与え、

```lean
example (x : GoldenInt) :
    goldenNorm (goldenZeroSectorLift x) =
      goldenFifthSndFactor x.fst x.snd := by
  ?_
```

を解かせれば、定義展開後に `ring` へ帰着できるかを評価できる。

0373 が definitional equality を認識する micro challenge だったのに対し、本 theorem は

1. 適切な定義を限定展開する
2. structure projection を簡約する
3. 非自明な quartic polynomial identity を `ring` で閉じる

という三段階を含むため、Comparator 用として一段価値が高い。

さらに 0375 と組み合わせれば、「座標多項式 identity → norm identity → conjugate product identity」という API 組み立て能力も測れる。

## 技術的意味

本定理の本質は、zero sector の quartic factor を黄金整数環の内部へ戻すことである。

整数多項式のままでは

$$
H(r,s)=D^5
$$

は単なる quartic=fifth-power 方程式に見える。しかし

$$
H(r,s)=N(T(r,s))
$$

と書き換えることで、

$$
T(r,s)\overline{T(r,s)}=D^5
$$

という因数分解構造が現れる。

ここから relative-prime factorization、unit-times-fifth-power extraction、five-sector classification を再利用できる。つまり FLT5 証明の前半で整備した黄金整数環の machinery を、zero-sector descent の内部で再帰的にもう一度起動するための橋がこの theorem である。

## 次に読むべき宣言

次は **`goldenZeroSectorLift_mul_conj`** である。

宣言種別は `theorem`。

```lean
theorem goldenZeroSectorLift_mul_conj (x : GoldenInt) :
    goldenMul (goldenZeroSectorLift x) (goldenConj (goldenZeroSectorLift x)) =
      goldenOfInt (goldenFifthSndFactor x.fst x.snd) := by
  rw [golden_mul_conj, goldenZeroSectorLift_norm]
```

0374 が quartic factor を norm に読み替えたのに対し、0375 は norm を `x * conjugate(x)` の積へ展開し、後続の coprime-factor theorem が直接受け取れる形へ変換する。
