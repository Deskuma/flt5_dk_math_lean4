# 0375 `goldenZeroSectorLift_mul_conj`

## 宣言種別

`theorem`

## Lean コード

```lean
theorem goldenZeroSectorLift_mul_conj (x : GoldenInt) :
    goldenMul (goldenZeroSectorLift x) (goldenConj (goldenZeroSectorLift x)) =
      goldenOfInt (goldenFifthSndFactor x.fst x.snd) := by
  rw [golden_mul_conj, goldenZeroSectorLift_norm]
```

## Lean の型

```lean
goldenZeroSectorLift_mul_conj :
  (x : GoldenInt) →
    goldenMul (goldenZeroSectorLift x)
      (goldenConj (goldenZeroSectorLift x)) =
        goldenOfInt (goldenFifthSndFactor x.fst x.snd)
```

任意の `x : GoldenInt` に対し、quadratic lift `goldenZeroSectorLift x` とその共役の積が、第五冪の第二座標に現れる quartic factor `goldenFifthSndFactor x.fst x.snd` を整数埋め込みした黄金整数に等しいことを述べる。

数学的に `x=(r,s)`、

$$
T(r,s)=\bigl(r^2+rs+s^2,\ s^2\bigr)
$$

と書けば、0374 `goldenZeroSectorLift_norm` は

$$
N(T(r,s))=H(r,s)
$$

を与えた。本 theorem はさらに黄金整数環の恒等式

$$
\alpha\overline{\alpha}=N(\alpha)
$$

を適用し、

$$
T(r,s)\overline{T(r,s)}=H(r,s)
$$

を黄金整数環内部の等式として実現する。ただし Lean の右辺では整数 `H(r,s)` を `goldenOfInt` で `GoldenInt` に埋め込んでいる。

## 数学的主張または宣言の意味

0374 では quartic factor を norm として認識したが、norm はまだ `ℤ` 値である。本 theorem はその整数値を `GoldenInt` に戻し、**積の等式** に変換する。

概念的には

$$
H(r,s)
\xleftarrow{\;0374\;}
N(T(r,s))
\xleftarrow{\;\alpha\bar\alpha=N(\alpha)\;}
T(r,s)\overline{T(r,s)}
$$

という再入が完成する。

この変換が重要なのは、後続の fifth-power factorization machinery が「norm が第五冪」という整数等式よりも、黄金整数環で

$$
A\overline A=B^5
$$

という積の形を直接扱うからである。0375 は quartic arithmetic と黄金整数環の relative-prime factorization の間の接続点である。

## 証明全体での役割

`SignedGoldenZeroSectorDescent.lean` の目的は、zero sector に残った候補からより小さい同型の候補を再構成し、無限降下で排除することである。

そのためにまず、zero-sector 座標から作った lift `T(r,s)` を黄金整数環の fifth-power factorization 問題へ戻す必要がある。

本 theorem はそのための bridge であり、後続 `GoldenZeroSectorDescentPacket.exists_lift_eq_fifthPower` では実際に

```lean
calc
  goldenMul (goldenZeroSectorLift p.base)
      (goldenConj (goldenZeroSectorLift p.base)) =
      goldenOfInt (goldenFifthSndFactor p.base.fst p.base.snd) :=
    goldenZeroSectorLift_mul_conj p.base
  _ = goldenOfInt ((p.D : ℤ) ^ 5) := by rw [p.H_eq]
  _ = goldenPow (goldenOfInt (p.D : ℤ)) 5 :=
    goldenOfInt_pow_five (p.D : ℤ)
```

という形で使用される。

したがって流れは

$$
H(r,s)=D^5
\Longrightarrow
T(r,s)\overline{T(r,s)}=D^5
\Longrightarrow
\text{coprime fifth-power factorization}
\Longrightarrow
T(r,s)=\varepsilon\gamma^5
$$

となる。本 theorem は第二段階への入口を与える。

## 直接依存する定義・補題

### `goldenZeroSectorLift`

```lean
def goldenZeroSectorLift (x : GoldenInt) : GoldenInt :=
  ⟨x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2, x.snd ^ 2⟩
```

quartic factor を黄金 norm として再表現する quadratic lift。

### `goldenConj`

黄金整数の共役を与える。`golden_mul_conj` の第二因子として使われる。

### `goldenMul`

`GoldenInt` 上の乗法。左辺の積を構成する。

### `goldenOfInt`

整数を `GoldenInt` に埋め込む。norm は `ℤ` 値なので、黄金整数環内の積等式にするにはこの埋め込みが必要になる。

### `golden_mul_conj`

```lean
theorem golden_mul_conj (x : GoldenInt) :
    goldenMul x (goldenConj x) = goldenOfInt (goldenNorm x) := by
  ext <;> simp [goldenMul, goldenConj, goldenOfInt, goldenNorm] <;> ring
```

黄金整数に対する

$$
\alpha\overline\alpha=N(\alpha)
$$

を Lean 上で表した一般定理。本 theorem の第一の rewrite である。

### `goldenZeroSectorLift_norm`

```lean
theorem goldenZeroSectorLift_norm (x : GoldenInt) :
    goldenNorm (goldenZeroSectorLift x) =
      goldenFifthSndFactor x.fst x.snd := by
  simp only [goldenZeroSectorLift, goldenNorm, goldenFifthSndFactor]
  ring
```

quadratic lift の norm を quartic factor に同定する 0374。本 theorem の第二の rewrite である。

## 証明または構築の流れ

証明は一行だけである。

```lean
rw [golden_mul_conj, goldenZeroSectorLift_norm]
```

最初の rewrite で左辺

```lean
goldenMul (goldenZeroSectorLift x)
  (goldenConj (goldenZeroSectorLift x))
```

を

```lean
goldenOfInt (goldenNorm (goldenZeroSectorLift x))
```

へ変換する。

次に 0374 を使って内部の norm を

```lean
goldenFifthSndFactor x.fst x.snd
```

へ書き換える。すると右辺と完全に一致して証明が終了する。

本 theorem 自体では `ring`、`omega`、divisibility、coprimality を新たに使わない。必要な代数計算は `golden_mul_conj` と 0374 の二つの既証明 theorem にすでに封じ込められている。

## Lean 固有の処理

### `rw` の合成

`rw [golden_mul_conj, goldenZeroSectorLift_norm]` は二つの抽象 API を順番に適用する。定義を直接展開せず、既存 theorem の rewrite interface だけで goal を閉じている。

### 内部部分式への rewrite

第二の `goldenZeroSectorLift_norm` は goal 全体ではなく、`goldenOfInt (...)` の内部に現れた

```lean
goldenNorm (goldenZeroSectorLift x)
```

へ適用される。Lean の `rw` が congruence の下で部分式を書き換える典型例である。

### definitional unfolding を避ける設計

この theorem では `goldenMul`、`goldenConj`、`goldenNorm`、`goldenZeroSectorLift` の具体座標を一切展開しない。前段の theorem を API として使うことで、証明が実装詳細から切り離されている。

## 冗長・重複箇所

コード上の冗長性はほぼない。二つの rewrite が数学的構造をそのまま表している。

一方、本 theorem は 0374 と `golden_mul_conj` の単純な合成なので、論理的には新しい数学を導入していない。しかし後続で同じ二段 rewrite を繰り返さずに済み、`goldenZeroSectorLift` の「積としての再入形」を named theorem として固定できるため、API 上の重複には実益がある。

## 最適化候補

### 1. `simpa` による短縮

例えば既存 theorem を組み合わせて `simpa` する書き方も考えられるが、現在の

```lean
rw [golden_mul_conj, goldenZeroSectorLift_norm]
```

は変換順序が明白であり、読みやすさの面で優れている。

### 2. `[simp]` 化

`golden_mul_conj` または `goldenZeroSectorLift_norm` を simp lemma とすれば `simp` で閉じる可能性がある。しかし norm 形式や conjugate-product 形式を意図的に保持したい証明もあり得るため、自動書き換え方向を広げる必要性は正本からは確認できない。現状の明示 rewrite の方が descent の段階を追いやすい。

### 3. bridge theorem としての現状維持

後続 `exists_lift_eq_fifthPower` が本 theorem を直接参照しているため、削除して rewrite を inline 化するより、named bridge として残す方が依存構造を可視化できる。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

本 theorem 単体の証明に必要なのは、主として

- `GoldenInt`
- `goldenMul`
- `goldenConj`
- `goldenOfInt`
- `goldenZeroSectorLift`
- `goldenFifthSndFactor`
- `golden_mul_conj`
- `goldenZeroSectorLift_norm`
- `rw` tactic

である。

0374 と異なり、この theorem 自体は `ring` を呼ばない。従って既存依存 theorem を同一モジュールまたは import 済みモジュールから利用できるなら、tactic requirement はかなり小さい。

ただし `SignedGoldenZeroSectorDescent.lean` 全体では後続に fifth-power factorization、coprimality、divisibility、`omega`、`norm_num` 等があるため、モジュール全体の最小 import は本 theorem 単独より広い。Lean ビルドを行わない条件なので、厳密な最小 import セットは未確認である。

## Comparator challenge 化の可否

**適している。** ただし難度は 0374 より低く、API 組み立て型の micro challenge になる。

例えば `golden_mul_conj` と `goldenZeroSectorLift_norm` を利用可能にしたうえで、

```lean
example (x : GoldenInt) :
    goldenMul (goldenZeroSectorLift x)
      (goldenConj (goldenZeroSectorLift x)) =
        goldenOfInt (goldenFifthSndFactor x.fst x.snd) := by
  ?_
```

を解かせる。

評価点は、

1. 左辺を一般 theorem `golden_mul_conj` で norm へ変換できるか
2. 0374 でその norm を quartic factor へ書き換えられるか
3. 座標定義を不必要に展開せず、既存 API を再利用できるか

である。

0374 とセットにすれば、「非自明な多項式恒等式を証明する段階」と「その結果を抽象 API で組み立てる段階」の二種類の能力を比較できる。

## 技術的意味

この theorem は zero-sector descent の再帰構造を成立させるための **環への再埋め込み bridge** である。

0374 までで

$$
H(r,s)=N(T(r,s))
$$

という整数値の同一視が得られた。本 theorem により

$$
T(r,s)\overline{T(r,s)}=\iota(H(r,s))
$$

となり、`H(r,s)=D^5` を代入すれば

$$
T(r,s)\overline{T(r,s)}=\iota(D^5)
$$

という黄金整数環内の積の fifth-power equation が得られる。

ここから前段で整備済みの `goldenCoprimeFactorOfFifthPower` などを再利用できる。すなわち zero-sector の特殊 quartic 方程式を新しい別問題として解くのではなく、証明前半で構築した「互いに素な積が第五冪なら各因子は unit × fifth power」という machinery へ戻す。その接続を一行で固定したのが本 theorem である。

## 次に読むべき宣言

次は **`GoldenZeroSectorDescentPacket`** である。

宣言種別は `structure`。

正本では本 theorem の直後に、次の説明とともに置かれている。

```lean
structure GoldenZeroSectorDescentPacket where
  base : GoldenInt
  t : ℕ
  D : ℕ
  t_pos : 0 < t
  D_pos : 0 < D
  ...
```

この structure は fifth-power re-entry で保存する不変量を packet 化する。正本の docstring では、可視座標が `5` 倍の第五冪であることと quartic factor 自体が第五冪であることの両方を保持することが、構成を真に再帰的にする、と説明されている。

0372–0375 で quadratic lift の再入 API が揃ったので、次はその再入を反復可能にする descent invariant の型そのものを読む段階に入る。
