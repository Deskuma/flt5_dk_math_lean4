# 0334 — `GoldenZeroSectorFactorData`

## 宣言種別

この宣言は theorem ではなく **dependent `inductive`** である。

`GoldenZeroSectorInversionPacket` を index に取り、零セクター反転後に得られる三つの二進 branch それぞれについて、第五冪因子化・互いに素性・奇偶性・所有関係・差分方程式を証明付きで保持するデータ型を定義する。

```lean
/-- Exact factor data in the three two-adic branches.  The enclosing packet
retains the complete inversion source and hence its norm and square reconstruction. -/
inductive GoldenZeroSectorFactorData
    (p : GoldenZeroSectorInversionPacket) : Type
  | odd
      (e f : ℕ)
      (e_pos : 0 < e) (f_pos : 0 < f)
      (coprime_e_f : Nat.Coprime e f)
      (coprime_ef_d : Nat.Coprime (e * f) p.source.d)
      (e_odd : Odd e) (f_odd : Odd f)
      (A_eq : p.source.A0 = 2 * e ^ 5)
      (B_eq : p.source.B0 = 2 * f ^ 5)
      (ownership : e * f = zeroSectorQ p.source.c)
      (difference : e ^ 5 + 4 * p.source.d ^ 5 = f ^ 5)
  | evenLeftLow
      (e f : ℕ)
      (e_pos : 0 < e) (f_pos : 0 < f)
      (coprime_e_f : Nat.Coprime e f)
      (coprime_ef_d : Nat.Coprime (e * f) p.source.d)
      (e_odd : Odd e) (f_even : Even f)
      (A_eq : p.source.A0 = 8 * e ^ 5)
      (B_eq : p.source.B0 = 16 * f ^ 5)
      (ownership : 2 * (e * f) = zeroSectorQ p.source.c)
      (difference : e ^ 5 + p.source.d ^ 5 = 2 * f ^ 5)
  | evenRightLow
      (e f : ℕ)
      (e_pos : 0 < e) (f_pos : 0 < f)
      (coprime_e_f : Nat.Coprime e f)
      (coprime_ef_d : Nat.Coprime (e * f) p.source.d)
      (e_even : Even e) (f_odd : Odd f)
      (A_eq : p.source.A0 = 16 * e ^ 5)
      (B_eq : p.source.B0 = 8 * f ^ 5)
      (ownership : 2 * (e * f) = zeroSectorQ p.source.c)
      (difference : 2 * e ^ 5 + p.source.d ^ 5 = f ^ 5)
```

## Lean の型

宣言全体の型は概念的に

```lean
GoldenZeroSectorFactorData :
  GoldenZeroSectorInversionPacket → Type
```

である。

したがって、固定した

```lean
p : GoldenZeroSectorInversionPacket
```

に対して

```lean
GoldenZeroSectorFactorData p : Type
```

が生成される。

ここが前回の `GoldenZeroSectorFactorBranch` との本質的な違いである。`GoldenZeroSectorFactorBranch` は三つの名前だけを持つ単純な列挙型だったが、今回の型は `p` に依存し、各 constructor の等式が

```lean
p.source.A0
p.source.B0
p.source.c
p.source.d
```

を直接参照する。

つまり factor data は任意の数論データではなく、**特定の inversion packet に対する certificate** である。

## 数学的意味

この宣言は、零セクター反転から得られた自然数因子 $A_0,B_0$ の二進構造を三種類に完全整理し、それぞれを第五冪 base $e,f$ で記述する。

### `odd` branch

この branch では

$$
A_0 = 2e^5,
\qquad
B_0 = 2f^5,
$$

かつ $e,f$ はともに奇数である。

さらに

$$
\gcd(e,f)=1,
\qquad
\gcd(ef,d)=1,
$$

および

$$
ef = Q,
\qquad
Q := \operatorname{zeroSectorQ}(c),
$$

が記録される。

差分方程式は

$$
e^5 + 4d^5 = f^5
$$

である。

この式は直前の `eleven_dvd_d_of_fifth_add_four_fifth` にそのまま入力できる形であり、odd branch の mod $11$ channel を明示している。

### `evenLeftLow` branch

この branch では左側因子の二進指数が低く、

$$
A_0 = 8e^5,
\qquad
B_0 = 16f^5
$$

となる。

奇偶性は

$$
e\text{ は奇数},
\qquad
f\text{ は偶数}
$$

であり、所有関係は

$$
2ef = Q
$$

となる。

差分方程式は

$$
e^5 + d^5 = 2f^5
$$

である。

### `evenRightLow` branch

左右を反転した branch で、

$$
A_0 = 16e^5,
\qquad
B_0 = 8f^5,
$$

$$
e\text{ は偶数},
\qquad
f\text{ は奇数},
$$

$$
2ef = Q
$$

を保持する。

差分方程式は

$$
2e^5 + d^5 = f^5
$$

である。

三 branch の違いは単なるラベルではなく、$2$ の冪の配置、$e,f$ の parity、`zeroSectorQ` の ownership、そして最終的に扱う第五冪方程式の形まで含む。

## 証明全体での役割

この宣言は零セクター factorization phase の中心的な **証明データ型** である。

前段では `GoldenZeroSectorInversionPacket` が

- $A_0,B_0$ の正性
- 積恒等式
- 差恒等式
- $c,d$ の互いに素性
- `zeroSectorQ`
- 平方再構成

などを保持していた。

しかし、そのままでは後続の descent や branch-specific obstruction に使いにくい。そこで二進付値を解析し、$A_0,B_0$ を第五冪の明示形に分解した結果を今回の型へ格納する。

特に、後続 theorem は生の $A_0,B_0$ から毎回 factorization を再構築する必要がなく、constructor pattern matching によって

```lean
.odd ...
.evenLeftLow ...
.evenRightLow ...
```

のいずれかを得れば、それぞれの exact equations を直接利用できる。

この意味で `GoldenZeroSectorFactorData p` は、反転 phase と descent phase の間に置かれた **certified normal form** と見ることができる。

## 直接依存する定義・補題

### `GoldenZeroSectorInversionPacket`

型 index `p` の型であり、今回の全 constructor が `p.source` を参照する。

特に

```lean
p.source.A0
p.source.B0
p.source.c
p.source.d
```

が factor equations と ownership equation に現れる。

### `zeroSectorQ`

ownership field に現れる。

odd branch では

```lean
ownership : e * f = zeroSectorQ p.source.c
```

であり、even branch では

```lean
ownership : 2 * (e * f) = zeroSectorQ p.source.c
```

となる。

### `Nat.Coprime`

各 constructor は

```lean
coprime_e_f : Nat.Coprime e f
coprime_ef_d : Nat.Coprime (e * f) p.source.d
```

を保持する。

### `Odd` / `Even`

branch ごとの二進配置を proposition として保持する。

今回の宣言自体は theorem を呼び出していない。前段 theorem への依存は、**この型の inhabitant を構築する際** に現れる。したがって declaration-level の直接依存と constructor-producing theorem の証明依存は区別する必要がある。

## 構築の流れ

この宣言自体に `by` proof はない。構築の意味は各 constructor の引数列に現れている。

### 1. inversion packet を index として固定する

```lean
(p : GoldenZeroSectorInversionPacket)
```

により、factor data の出所を型レベルで固定する。

### 2. 第五冪 base を導入する

全 branch で

```lean
(e f : ℕ)
```

を保持する。

### 3. 非退化性を正性で記録する

```lean
e_pos : 0 < e
f_pos : 0 < f
```

を全 branch が持つ。

### 4. prime ownership の分離を coprimality として記録する

```lean
coprime_e_f : Nat.Coprime e f
coprime_ef_d : Nat.Coprime (e * f) p.source.d
```

を共通 field として持つ。

### 5. branch 固有の parity を記録する

odd では `Odd e`, `Odd f`、evenLeftLow では `Odd e`, `Even f`、evenRightLow では `Even e`, `Odd f` となる。

### 6. $A_0,B_0$ の正確な二進係数付き第五冪形を記録する

係数は branch に応じて

$$
(2,2),\ (8,16),\ (16,8)
$$

の三通りである。

### 7. `zeroSectorQ` の ownership を記録する

odd branch は $ef=Q$、even branch は $2ef=Q$ を保持する。

### 8. branch 固有の第五冪差分方程式を記録する

これにより後続証明は factor equations を代入し直すことなく、すでに正規化された方程式を利用できる。

## Lean 固有の処理

### dependent inductive による source 固定

`p` を index に持つため、異なる inversion packet から作られた factor data を誤って混ぜることができない。

これは単なる `structure` に `source : GoldenZeroSectorInversionPacket` field を持たせる設計よりも、`GoldenZeroSectorFactorData p` という型そのものが source identity を表す点で強い。

### constructor が branch label と proof payload を同時に表す

各 constructor は branch の識別子であると同時に、その branch が成立するための全 certificate を運ぶ。

したがって pattern matching すると branch 判定と必要な証明 witness の取得が同時に行える。

### field projection ではなく constructor elimination が中心

通常の `structure` と異なり、共通 field を単純に `data.e` のように射影する API は自動では得られない。`e,f` は各 constructor の payload だからである。

その代わり後続では `cases data` や pattern matching を使い、branch ごとの exact equation を一度に取り出せる。

### proposition と computational data の混在

`e f : ℕ` は計算データ、`e_pos`, `coprime_e_f`, `A_eq` などは proof data である。Lean の dependent type により両者を同一 constructor 内に保持している。

## 冗長・重複箇所

三 constructor にはかなり多くの共通 payload がある。

共通部分は

```lean
(e f : ℕ)
(e_pos : 0 < e) (f_pos : 0 < f)
(coprime_e_f : Nat.Coprime e f)
(coprime_ef_d : Nat.Coprime (e * f) p.source.d)
```

である。

また `A_eq`, `B_eq`, `ownership`, `difference` も field の役割自体は共通し、式だけが branch ごとに異なる。

したがって syntactic duplication は存在する。

ただし、この重複により各 constructor の型を読むだけで branch invariant が完全に見える。特に factor coefficient と parity が constructor type に焼き付いているため、後続の `cases` で式が明示的に得られる利点が大きい。

## 最適化候補

### 1. 共通 payload を inner structure 化する案

例えば $e,f$、正性、coprimality を共通 `structure` に分離し、branch 固有データだけを constructor に残す設計は可能である。

これにより declaration の重複は減るが、利用側で一段 projection が増える。現在の規模では現行設計の明示性にも十分な価値がある。

### 2. `GoldenZeroSectorFactorBranch` を index にする案

概念的には

```lean
GoldenZeroSectorFactorData p b
```

のように branch label まで index に持つ設計も可能である。

そうすれば branch equality の扱いが型に移る一方、existential な「どれか一 branch の factor data」を扱う際に sigma type が必要になる。現行コードでは直後に `GoldenZeroSectorFactorData.branch` を定義しているため、軽い branch label と重い certificate を分離する方針が選ばれている。

### 3. parity と係数の対応を抽象化する案

$(2,2)$、$(8,16)$、$(16,8)$ と parity の対応を別定義にまとめることもできる。

しかし、この段階は証明の監査可能性が重要であり、係数を constructor type に露出させておく現行形は読みやすい。

### 4. `Prop` ではなく `Type` である点は維持すべき

この型は existential witness $e,f$ を実データとして保持し、後続で取り出して使う。したがって単なる branch proposition の disjunction に潰すより、現在の `Type`-valued certificate が適している。

## 必要 Mathlib import と import 最適化候補

standalone 正本全体は

```lean
import Mathlib
```

を使用している。

この宣言単体が直接必要とする主要要素は

- `Nat.Coprime`
- `Odd`
- `Even`
- 自然数の冪・乗算・順序
- 前段で定義された `GoldenZeroSectorInversionPacket`
- `zeroSectorQ`

である。

したがって、この宣言単独を切り出すなら `import Mathlib` より小さい import 集合へ縮められる可能性は高い。

ただし `GoldenZeroSectorInversionPacket` と `zeroSectorQ` 自体の import closure も必要であり、今回は Lean ビルドを行わないため、厳密な最小 Mathlib import 集合は確認していない。

ファイル全体では後続 proof が `omega`, `norm_num`, divisibility API などを大量に使うため、この宣言だけを理由に standalone 全体の `import Mathlib` を縮小できるとは限らない。

## Comparator challenge 化の可否

**高い。**

この宣言は theorem proving というより dependent API design の比較題材として良い。

比較候補としては、

1. 現行の三 constructor dependent `inductive`
2. 共通 field を持つ `structure` + branch-specific proposition
3. `GoldenZeroSectorFactorBranch` を index に加えた indexed family
4. branch ごとの三つの個別 `structure` を sum type で束ねる設計
5. existential/disjunction だけで factorization result を返す設計

が考えられる。

評価軸は、

- branch-specific invariant が型にどこまで現れるか
- pattern matching 後の proof state の簡潔さ
- 共通 field へのアクセス性
- `simp` の扱いやすさ
- source packet の取り違え防止
- downstream descent theorem の型の読みやすさ
- constructor 追加時の保守性

である。

特に現行設計は多少の field 重複と引き換えに、各 branch の完全な数学的 normal form を constructor signature だけで監査できる。このトレードオフは Comparator challenge に向いている。

## 次に読むべき宣言

正本上で次の宣言は

```lean
/-- Branch label of an exact factor datum. -/
def GoldenZeroSectorFactorData.branch
    {p : GoldenZeroSectorInversionPacket} :
    GoldenZeroSectorFactorData p → GoldenZeroSectorFactorBranch
  | .odd .. => .odd
  | .evenLeftLow .. => .evenLeftLow
  | .evenRightLow .. => .evenRightLow
```

である。

したがって次の連番は **0335 `GoldenZeroSectorFactorData.branch`** となる。

これは theorem ではなく **`def`** であり、今回の重い factor certificate を前回定義した軽い `GoldenZeroSectorFactorBranch` へ射影する。

0334 が branch-specific proof payload を保持する本体、0335 がそこから branch label だけを読み出す観測関数という関係である。