# 0337 — `GoldenZeroSectorFactorPacket`

## 宣言種別

この宣言は theorem ではなく **`structure`** である。

零セクター反転で得た `GoldenZeroSectorInversionPacket` と、その特定の反転 packet に依存する exact factor certificate `GoldenZeroSectorFactorData inversion` を一つの proof-carrying packet に束ねる。

```lean
/-- Complete zero-sector factor packet. -/
structure GoldenZeroSectorFactorPacket : Type where
  inversion : GoldenZeroSectorInversionPacket
  factors : GoldenZeroSectorFactorData inversion
```

## Lean の型

宣言自身の型は

```lean
GoldenZeroSectorFactorPacket : Type
```

である。

constructor が持つデータを明示すれば概念的には

```lean
GoldenZeroSectorFactorPacket.mk :
  (inversion : GoldenZeroSectorInversionPacket) →
  GoldenZeroSectorFactorData inversion →
  GoldenZeroSectorFactorPacket
```

となる。

重要なのは第2フィールド

```lean
factors : GoldenZeroSectorFactorData inversion
```

が第1フィールド `inversion` の値を型の中で参照している点である。したがって `factors` は任意の factor data ではなく、同じ packet に格納された `inversion` に対して構築された factor data でなければならない。

## 数学的意味

この structure 自体は新しい等式や可除性を証明しない。数学的役割は、零セクター解析の二段階の certificate

1. 反転・正規化された零セクター情報、
2. その情報に対する exact fifth-power factorization branch、

を「対応関係を壊せない一つの対象」として保存することである。

`inversion` が保持するデータを $p$ と書けば、`factors` は必ず

$$
\operatorname{GoldenZeroSectorFactorData}(p)
$$

である。

0334 で見た `GoldenZeroSectorFactorData p` は branch に応じて、例えば odd branch なら

$$
A_0=2e^5,
\qquad
B_0=2f^5,
$$

$$
e^5+4d^5=f^5,
$$

などの factorization certificate を運ぶ。今回の structure は、その certificate がどの inversion packet から来たものなのかを型依存によって固定する。

## FLT5 証明全体での役割

零セクターの証明は、単なる「因子分解が存在する」という命題ではなく、前段で得られた `GoldenZeroSectorInversionPacket` の具体的な `c,d,A0,B0,Q` 等に対して factorization を構築し、その後 descent へ渡す必要がある。

もし inversion と factor data を独立なフィールドとして

```lean
inversion : GoldenZeroSectorInversionPacket
factors : GoldenZeroSectorFactorData someOtherPacket
```

のように保持できてしまえば、異なる零セクター packet の証明データを誤って組み合わせる余地が生じる。

この structure は

```lean
factors : GoldenZeroSectorFactorData inversion
```

とすることで、その不整合を型検査段階で排除する。

したがってこれは、零セクター反転フェーズと exact factorization フェーズの間に置かれる **依存型による整合性境界** である。後続の descent machinery は一つの `GoldenZeroSectorFactorPacket` を受け取れば、反転情報と対応 factor certificate が同じ起源を持つことを改めて証明する必要がない。

## 直接依存する定義・宣言

### `GoldenZeroSectorInversionPacket`

第1フィールド

```lean
inversion : GoldenZeroSectorInversionPacket
```

の型である。

零セクターの source data と、その反転・正規化で得た恒等式、互いに素性、非可除性などを後段へ渡す certificate である。

### `GoldenZeroSectorFactorData`

0334 の dependent `inductive` 宣言である。

```lean
GoldenZeroSectorFactorData :
  GoldenZeroSectorInversionPacket → Type
```

という形で inversion packet を index に取り、`odd`、`evenLeftLow`、`evenRightLow` の各 constructor が branch 固有の exact factorization data を保持する。

今回の第2フィールドはこの index に第1フィールドそのものを渡す。

## 構築の流れ

この宣言には proof script は存在しない。structure 宣言そのものが constructor と projection を生成する。

### 1. inversion certificate を受け取る

```lean
inversion : GoldenZeroSectorInversionPacket
```

まず、どの零セクター反転 packet を扱うのかを固定する。

### 2. その inversion に対応する factor data を要求する

```lean
factors : GoldenZeroSectorFactorData inversion
```

第1フィールドが確定した後、その値を index とする factor certificate だけを受け入れる。

### 3. 一つの packet として後続へ渡す

constructor は概念的に

```lean
⟨p, data⟩
```

という形で使える。ただし Lean は `data` の型が厳密に

```lean
GoldenZeroSectorFactorData p
```

であることを検査する。

## Lean 固有の処理

### dependent field

通常の structure では各フィールドの型は互いに独立であることが多いが、ここでは後ろのフィールドの型が前のフィールドの値に依存する。

```lean
factors : GoldenZeroSectorFactorData inversion
```

は Lean の dependent structure の典型例である。

### 自動生成される projection

Lean は少なくとも概念的に

```lean
GoldenZeroSectorFactorPacket.inversion :
  GoldenZeroSectorFactorPacket → GoldenZeroSectorInversionPacket
```

と、それぞれの packet `p` に対して

```lean
p.factors : GoldenZeroSectorFactorData p.inversion
```

という projection を提供する。

後者の戻り型にも依存関係が保存される。

### proof-carrying data の束縛

`GoldenZeroSectorFactorData` 自体が多数の証明項を保持するため、今回の structure は証明を証明するのではなく、証明済みデータ同士の provenance を型で結び付ける役目を持つ。

これは命題間の論理的含意ではなく **データ設計による不変条件の強制** である。

## 冗長・重複箇所

宣言は2フィールドだけであり、コード上の実質的な冗長性はない。

`GoldenZeroSectorFactorData` がすでに `p : GoldenZeroSectorInversionPacket` を index としているため、「factor data から inversion を復元できるのではないか」という設計も考えられる。しかし index は通常 runtime field として保持される単純な record projection とは異なり、利用側で inversion と factor data を一つの値として持ち回るには今回の wrapper が便利である。

また、この wrapper を sigma type

```lean
Σ p : GoldenZeroSectorInversionPacket, GoldenZeroSectorFactorData p
```

で代用することも型理論上は可能である。しかし名前付きフィールド `inversion` / `factors` を持つ専用 structure の方が、後続 API の意味と projection の可読性が明確である。

## 最適化候補

### Sigma 型への縮約

純粋な型の最小化だけを目的とすれば

```lean
Σ p : GoldenZeroSectorInversionPacket, GoldenZeroSectorFactorData p
```

と同型の情報を持つため、専用 structure を省く設計は可能である。

ただし証明開発では名前付き projection と domain-specific な型名の価値が高く、現状の structure は API として妥当である。

### constructor helper

後続で packet 構築時の elaboration が繰り返し複雑になるなら、

```lean
def GoldenZeroSectorFactorPacket.mkFrom ...
```

のような helper を設ける余地はある。しかし今回の constructor は2引数しかなく、現時点で追加 abstraction の必要性は確認できない。

### `Prop` 化は適さない

この packet は後続で branch certificate を取り出して計算・場合分けするための data container であり、単なる存在命題へ潰すより `Type` に置く現在の設計の方が情報を保持できる。

## 必要 Mathlib import と import 最適化候補

リポジトリの standalone 正本はファイル全体で

```lean
import Mathlib
```

を使用している。

しかし今回の structure 宣言そのものは、既に

```lean
GoldenZeroSectorInversionPacket
GoldenZeroSectorFactorData
```

が利用可能なら、Mathlib の tactic や算術 theorem を直接呼び出していない。必要なのは Lean の structure / dependent type 機構と先行するローカル宣言である。

元のモジュール分割では `SignedGoldenZeroSectorFactorization.lean` に至る先行依存を import する必要があるが、この展示用 standalone からはそのモジュールの最小 import 集合までは確定できない。

したがって `import Mathlib` はこの1宣言だけを見る限り大幅に過剰であり得るが、Lean ビルドを行わない今回の作業では具体的な最小 import 列は検証済みとはしない。

## Comparator challenge 化の可否

**可能だが、単独では低難度。**

穴埋め対象を

```lean
structure GoldenZeroSectorFactorPacket : Type where
  inversion : GoldenZeroSectorInversionPacket
  factors : ?m
```

として、`?m` に

```lean
GoldenZeroSectorFactorData inversion
```

を入れさせる challenge なら dependent field の理解を検査できる。

ただし証明探索や arithmetic はなく、通常の theorem comparator としては簡単すぎる。より良い challenge は、0334 の dependent inductive と今回の structure をセットにし、「factor data が別の inversion packet と混在できない API を設計せよ」とする型設計問題である。

評価点は、単に2つの値を pair にするのではなく、第2成分の型が第1成分の値へ依存していることを表現できるかどうかに置ける。

## 次に読むべき宣言

次の宣言は

```lean
private theorem nonempty_odd_factorData
    (p : GoldenZeroSectorInversionPacket) (hc : Odd p.source.c) :
    Nonempty (GoldenZeroSectorFactorData p) := by
```

である。

種別は **`private theorem`**。

今回定義した packet の第2フィールドを実際に構築するための branch-specific existence theorem の最初であり、`c` が odd の場合に

```lean
Nonempty (GoldenZeroSectorFactorData p)
```

を作る。

ここから、0334 で定義した exact factor certificate が単なる型宣言ではなく、零セクター inversion packet から実際に inhabited であることを示す構築フェーズへ入る。