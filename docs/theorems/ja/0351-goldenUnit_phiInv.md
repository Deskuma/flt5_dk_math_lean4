# 0351 — `goldenUnit_phiInv`

## 宣言種別

この宣言は **`theorem`** である。

```lean
theorem goldenUnit_phiInv : GoldenUnit goldenPhiInv := by
  exact ⟨goldenPhi, golden_inv_mul_phi, golden_phi_mul_inv⟩
```

## Lean の型

```lean
goldenUnit_phiInv : GoldenUnit goldenPhiInv
```

ここで `goldenPhiInv : GoldenInt` は 0348 で定義された黄金整数

```lean
def goldenPhiInv : GoldenInt := ⟨-1, 1⟩
```

であり、数学的には $\varphi-1=\varphi^{-1}$ を表す。

`GoldenUnit epsilon` は、`epsilon : GoldenInt` に対して二側逆元となる黄金整数が存在することを表す命題である。既存コードで用いられている形は

```lean
def GoldenUnit (epsilon : GoldenInt) : Prop :=
  ∃ eta : GoldenInt,
    goldenMul epsilon eta = goldenOne ∧
    goldenMul eta epsilon = goldenOne
```

である。

したがって本 theorem の型は、`goldenPhiInv` に対してそのような逆元 witness が存在することを証明している。

## 数学的主張

0348–0350 までに

$$
goldenPhiInv=\varphi-1
$$

および

$$
\varphi(\varphi-1)=1,
\qquad
(\varphi-1)\varphi=1
$$

が具体的な `GoldenInt` の等式として得られている。

本 theorem では逆元 witness として

$$
\eta=\varphi
$$

を選ぶ。すると

$$
(\varphi-1)\eta=1
$$

と

$$
\eta(\varphi-1)=1
$$

の両方が成立するので、$\varphi-1$ は `GoldenUnit` である。

数学的には

$$
\varphi^{-1}\in \mathbb Z[\varphi]^\times
$$

を、このプロジェクト独自の `GoldenUnit` certificate として明示した宣言である。

## 証明全体での役割

`GoldenUnitClassification` の冒頭では、unit descent に必要な「$\varphi$ の逆元」をまず座標モデルの内部で構成している。

依存の流れは

```text
goldenPhiInv
  ├─ golden_phi_mul_inv
  └─ golden_inv_mul_phi
          ↓
     goldenUnit_phiInv
          ↓
     goldenUnit_descent
          ↓
 goldenUnitFifthClass_of_unit
          ↓
 goldenUnitClassesModFifth
```

となる。

0348 `goldenPhiInv` は単なる `GoldenInt` の値であり、それだけでは「unit である」という論理情報を持たない。0349 と 0350 が左右の逆元則を証明し、本 theorem がそれらを `GoldenUnit` の存在証明へ包装する。

後続の `goldenUnit_descent` では、unit `x` を短くするために

```lean
let y := goldenMul x goldenPhiInv
```

のような候補を構成し、

```lean
goldenUnit_mul hx goldenUnit_phiInv
```

によって `y` が再び unit であることを保証する。このため本 theorem は、下降写像が unit の集合から外へ飛び出さないことを保証する直接の certificate である。

## 直接依存する定義・補題

本 theorem が直接参照するプロジェクト宣言は次の通りである。

- `GoldenUnit` — 黄金整数が二側逆元を持つことを表す命題。
- `goldenPhiInv` — 0348。$\varphi-1$ を表す黄金整数 `⟨-1,1⟩`。
- `goldenPhi` — $\varphi$ を表す黄金整数。
- `golden_inv_mul_phi` — 0350。
  ```lean
  goldenMul goldenPhiInv goldenPhi = goldenOne
  ```
- `golden_phi_mul_inv` — 0349。
  ```lean
  goldenMul goldenPhi goldenPhiInv = goldenOne
  ```

`GoldenUnit` の witness は `goldenPhi` そのものであり、新たな算術計算は本 theorem では行わない。

## 証明または構築の流れ

証明は一行の constructor term である。

```lean
exact ⟨goldenPhi, golden_inv_mul_phi, golden_phi_mul_inv⟩
```

`GoldenUnit goldenPhiInv` を存在命題として展開すると、目標は概念的に

```lean
∃ eta : GoldenInt,
  goldenMul goldenPhiInv eta = goldenOne ∧
  goldenMul eta goldenPhiInv = goldenOne
```

となる。

そこで次の三要素を順に与えている。

1. `eta := goldenPhi`
2. `golden_inv_mul_phi`
3. `golden_phi_mul_inv`

すなわち

```text
witness          : goldenPhi
left inverse law : goldenPhiInv * goldenPhi = 1
right inverse law: goldenPhi * goldenPhiInv = 1
```

を一度に existential/conjunction structure へ詰めている。

## Lean 固有の処理

### 山括弧 `⟨...⟩` による存在証明と連言の同時構築

Lean では

```lean
⟨goldenPhi, golden_inv_mul_phi, golden_phi_mul_inv⟩
```

という記法が、入れ子になった `Exists.intro` と `And.intro` をまとめて構築する。

概念的には

```lean
Exists.intro goldenPhi
  (And.intro golden_inv_mul_phi golden_phi_mul_inv)
```

に相当する。

この theorem では tactic による探索はなく、既に得られた証明項を型の要求順に配置するだけである。

### 左右の向きの順序が重要

`GoldenUnit goldenPhiInv` の対象は `epsilon = goldenPhiInv` であり、witness は `eta = goldenPhi` である。そのため最初に必要なのは

```lean
goldenMul goldenPhiInv goldenPhi = goldenOne
```

すなわち 0350 `golden_inv_mul_phi` である。

次に必要なのが

```lean
goldenMul goldenPhi goldenPhiInv = goldenOne
```

すなわち 0349 `golden_phi_mul_inv` である。

数学的には可換なので同じ内容に見えるが、constructor の field/order に対して証明項の向きは正確に一致しなければならない。

### `exact` だけで閉じる proof-term 指向の証明

この宣言では `refine`、`constructor`、`use` などで目標を分解せず、完成済みの proof term を `exact` している。小さい interface theorem として非常に局所的で、後続コードからは内部の左右逆元証明を意識せず `goldenUnit_phiInv` 一つを渡せる。

## 冗長・重複箇所

本 theorem 自身には実質的な重複はほとんどない。0349 と 0350 の二つの closed computation を一つの `GoldenUnit` certificate に束ねることだけを行う。

数学的には黄金整数環の可換性により、片側逆元則から他側も得られるため、0349 と 0350 の両方を独立 theorem として保持する点には重複がある。しかし本 theorem の立場からは、`GoldenUnit` の定義が二つの向きを要求するため、既存の二 lemma をそのまま与える現在の形が最も直接的である。

もし `GoldenUnit` 自体を標準的な可換環の `IsUnit` / `Units` に寄せる設計へ変更するなら、この二側 certificate の明示性は減らせる可能性がある。ただし、それは局所最適化ではなく API 設計変更である。

## 最適化候補

現行証明

```lean
by
  exact ⟨goldenPhi, golden_inv_mul_phi, golden_phi_mul_inv⟩
```

はすでに極めて短い。

候補としては次が考えられる。

1. `by exact ...` を term style にして
   ```lean
   theorem goldenUnit_phiInv : GoldenUnit goldenPhiInv :=
     ⟨goldenPhi, golden_inv_mul_phi, golden_phi_mul_inv⟩
   ```
   とさらに一段縮める。
2. `GoldenUnit` と Mathlib の `IsUnit` / `Units` を接続する bridge が後続で有益なら、独自 unit certificate と標準 API の重複を整理する。
3. 0349・0350 の片方を乗法可換性から導出し、左右逆元の closed computation の重複を減らす。
4. `goldenUnit_phiInv` を `[simp]` ではなく unit closure API の基礎 lemma として現在どおり明示的に保持する。命題自体は rewrite lemma ではないため、simp 属性を付ける対象ではない。

1 は純粋な表記上の短縮であり、現行コードの可読性も十分高い。2 と 3 は依存関係や後続 API 全体を見て判断すべき設計候補である。

## 必要 Mathlib import と import 最適化候補

生成 standalone `Flt5DkMath/FLT5StandAlone.lean` は全体として

```lean
import Mathlib
```

を使用している。

本 theorem 自身の proof term は、Mathlib の算術 tactic を直接使用しない。必要なのは主として

- `Exists` と `And` の基礎論理構造
- `GoldenInt` と `GoldenUnit` など前段で定義されたプロジェクト API
- 0349・0350 の既証明 theorem

である。

したがって本 theorem 単体の証明は `Mathlib` 全体を必要とするほど重くない。一方、`GoldenUnit`、`GoldenInt`、`goldenMul`、各 ring instance の定義元が何を import しているかまで含めた厳密な最小 Mathlib import は、モジュール境界とビルドを確認しなければ確定できない。

今回は Lean ビルドを行わないため、細分化した最小 import は **未確認** とする。

## Comparator challenge 化の可否

**適している。難度は初級。**

例えば

```lean
example : GoldenUnit goldenPhiInv := by
  ?_
```

を与え、利用可能 lemma として

```lean
golden_inv_mul_phi
golden_phi_mul_inv
```

を提示すれば、solver が `GoldenUnit` の existential/conjunction shape を読み、正しい witness `goldenPhi` を選べるかを評価できる。

期待される最短解は

```lean
exact ⟨goldenPhi, golden_inv_mul_phi, golden_phi_mul_inv⟩
```

である。

challenge としての焦点は算術ではなく、

- proposition の constructor shape の理解
- existential witness の選択
- 左右逆元 lemma の向きの識別
- 既存 proof term の再利用

にある。

0350 までを隠して座標計算から全部構成させると別の challenge になるが、本 theorem 単体としては小さな proof-composition 問題として扱うのが自然である。

## 次に読むべき宣言

次は **0352 `golden_mul_phi_coords`** を読むべきである。宣言種別は **`theorem`**。

```lean
theorem golden_mul_phi_coords (x : GoldenInt) :
    goldenMul x goldenPhi = ⟨x.snd, x.fst + x.snd⟩ := by
  ext <;> simp [goldenMul, goldenPhi]
```

0351 までで `goldenPhiInv` が正式に unit であることが確定した。次の 0352 からは unit descent のための **座標変換則** に入る。

数学的には

$$
(a+b\varphi)\varphi
=b+(a+b)\varphi
$$

であり、座標写像として

$$
(a,b)\longmapsto(b,a+b)
$$

を与える。

続く `golden_mul_phiInv_coords` と対になり、後続の `goldenUnit_descent` が coordinate measure

$$
|a|+|b|
$$

を厳密に減少させる方向を場合分けで選ぶための計算基盤となる。
