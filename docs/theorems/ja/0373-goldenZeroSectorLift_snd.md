# 0373 `goldenZeroSectorLift_snd`

## 宣言種別

`theorem`

## Lean コード

```lean
theorem goldenZeroSectorLift_snd (x : GoldenInt) :
    (goldenZeroSectorLift x).snd = x.snd ^ 2 := rfl
```

## Lean の型

```lean
goldenZeroSectorLift_snd :
  (x : GoldenInt) → (goldenZeroSectorLift x).snd = x.snd ^ 2
```

任意の `x : GoldenInt` に対して、0372 `goldenZeroSectorLift` の第二座標が元の第二座標の平方に等しいことを述べる。

数学的に $x=(r,s)$、

$$
T(r,s)=\bigl(r^2+rs+s^2,\ s^2\bigr)
$$

と書けば、本定理は単に

$$
\operatorname{snd}(T(r,s))=s^2
$$

である。

## 数学的主張の意味

0372 で定義した quadratic re-entry map

$$
T(r,s)=\bigl(r^2+rs+s^2,s^2\bigr)
$$

の第二成分を named theorem として取り出した projection lemma である。

数学的内容だけを見れば定義の展開そのものであり、新しい算術事実を証明しているわけではない。しかし zero-sector descent では第二座標が平方になることが重要で、後段では元の座標 $s$ の 5 可除性から

$$
5\mid s^2
$$

を得るための安定した rewrite API として利用される。

## 証明全体での役割

`SignedGoldenZeroSectorDescent.lean` は、zero sector の quartic 条件を黄金整数の norm/fifth-power 問題へ再入させ、そこから strict descent を構成する部分である。

0372 `goldenZeroSectorLift` が再入写像そのものを定義し、本定理はその写像の「可視座標」を固定する。

後続 `GoldenZeroSectorDescentPacket.exists_lift_eq_fifthPower` では、

```lean
have hFiveAlpha : (5 : ℤ) ∣ (goldenZeroSectorLift p.base).snd := by
  rw [goldenZeroSectorLift_snd]
  ...
```

と実際に使用される。packet の `snd_eq` から

$$
p.base.snd=\pm 5t^5
$$

を得て平方し、lift の第二座標に 5 が割り切れることを示す。この 5 可除性は nonzero unit sector 排除へ渡される。

従って流れは

$$
p.base.snd=\pm5t^5
\Longrightarrow
5\mid p.base.snd^2
\Longrightarrow
5\mid \operatorname{snd}(T(p.base))
$$

であり、本定理は最後の同一視を担う。

## 直接依存する定義・補題

### `goldenZeroSectorLift`

直接の唯一の FLT5 固有依存である。

```lean
def goldenZeroSectorLift (x : GoldenInt) : GoldenInt :=
  ⟨x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2, x.snd ^ 2⟩
```

この定義の第二成分が literal に `x.snd ^ 2` なので、本定理は definitional equality で成立する。

### `GoldenInt.snd`

`GoldenInt` の第二座標 projection。定義を展開した後、constructor の第二成分へ projection する計算規則が働く。

### `rfl`

補題ではなく Lean の反射律 proof term である。左辺を定義展開・projection reduction すると右辺と定義的に同一になるため、追加の rewrite や algebra tactic は不要である。

## 証明の流れ

証明は一語だけである。

```lean
:= rfl
```

Lean が行う計算を明示すると、

```lean
(goldenZeroSectorLift x).snd
```

を `goldenZeroSectorLift` の定義で展開して

```lean
(⟨x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2,
   x.snd ^ 2⟩ : GoldenInt).snd
```

とし、structure projection の計算により

```lean
x.snd ^ 2
```

へ簡約する。

よって goal は

```lean
x.snd ^ 2 = x.snd ^ 2
```

となり、`rfl` で閉じる。

## Lean 固有の処理

### definitional equality

この theorem の中心は proposition-level の数学というより Lean の definitional equality である。

`rw [goldenZeroSectorLift_snd]` を後続コードで使える一方、証明側では定義を明示的に `unfold` する必要がない。kernel reduction が十分だからである。

### projection reduction

constructor で作った値に `.snd` を適用すると第二引数へ計算される。これは theorem を呼ぶ rewrite ではなく、Lean の計算規則である。

### named rewrite lemma としての API

理論上は後続で毎回

```lean
simp [goldenZeroSectorLift]
```

などと展開しても同じ結果を得られる。しかし named theorem を置くことで、後続証明は `goldenZeroSectorLift` の第一座標の実装詳細を展開せず、第二座標だけを書き換えられる。

これは proof maintenance 上の重要な抽象化境界である。

## 冗長・重複箇所

数学的には本 theorem は 0372 の定義から即座に得られるため、情報としては重複している。

ただしこの重複は意図的な API duplication と評価できる。後段で第二座標だけを使う箇所に対し、定義全体を展開させないためである。

現在の一行証明には除去すべき tactic-level の冗長性はない。

## 最適化候補

### 1. `[simp]` 属性

候補として

```lean
@[simp] theorem goldenZeroSectorLift_snd ... := rfl
```

とすれば、`simp` が lift の第二座標を自動的に `x.snd ^ 2` へ簡約できる。

ただし、現在の後続コードは意図を明示する `rw [goldenZeroSectorLift_snd]` を使っており、それ自体は読みやすい。グローバル simp set に追加する価値があるかは利用箇所全体を見て判断すべきで、ここでは候補に留める。

### 2. theorem を削除して定義展開する案

可能ではあるが推奨度は低い。後続 proof が `goldenZeroSectorLift` の座標実装に直接依存するため、抽象化が弱くなる。

### 3. 第一座標 projection lemma との対称 API

第一座標も頻繁に単独利用するなら `goldenZeroSectorLift_fst` を追加する余地がある。ただし現時点の正本では直後に norm identity が第一座標をまとめて処理しており、本 theorem と機械的に対称化する必要は確認できない。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

で全生成ソースをまとめている。

本 theorem 単体は、

- `GoldenInt`
- `goldenZeroSectorLift`
- structure projection
- 自然数指数による平方
- equality / `rfl`

しか必要とせず、追加 tactic は使用しない。

従ってこの一宣言だけを見ると `import Mathlib` は大幅に広い。ただし実際の `SignedGoldenZeroSectorDescent.lean` モジュール全体では `ring`, `norm_num`, `omega`, divisibility、coprimality など多数の機能を後続で使用する。

正確な最小 Mathlib import はモジュール全体の依存グラフを基準に Lean ビルドで検証する必要がある。本作業では Lean ビルドを行わないため、最小 import の確定はしていない。

## Comparator challenge 化の可否

**可能。ただし単体では極小 challenge である。**

例えば

```lean
def goldenZeroSectorLift (x : GoldenInt) : GoldenInt :=
  ⟨x.fst ^ 2 + x.fst * x.snd + x.snd ^ 2, x.snd ^ 2⟩

example (x : GoldenInt) :
    (goldenZeroSectorLift x).snd = x.snd ^ 2 := by
  ?_
```

とすれば、期待解は `rfl` である。

これは Comparator に対して、不要な tactic 探索をせず definitional equality を認識できるかを見る micro challenge になる。

より評価価値を高めるなら 0372〜0374 をまとめ、

1. lift の定義
2. `snd` projection を `rfl`
3. norm identity を `ring`

までを一つの小型 challenge にする方がよい。

## 技術的意味

本定理は「平方になっている」という 0372 の設計意図を、後続証明から直接参照できる論理 API に昇格させる。

zero-sector descent では、lift の norm 側だけでなく第二座標側にも算術条件が必要である。特に

$$
s=\pm5t^5
$$

という情報を lift へ運ぶと、

$$
\operatorname{snd}(T(r,s))=s^2
$$

なので 5 可除性が自動的に保存される。

この「可視座標の 5 可除性」と、次の 0374 が与える

$$
\operatorname{Norm}(T(r,s))=H(r,s)
$$

という norm 再入が組み合わさり、unit-sector classification を zero-sector descent へ再利用できる。

## 次に読むべき宣言

次は **`goldenZeroSectorLift_norm`** である。

宣言種別は `theorem`。

```lean
theorem goldenZeroSectorLift_norm (x : GoldenInt) :
    goldenNorm (goldenZeroSectorLift x) =
      goldenFifthSndFactor x.fst x.snd := by
  simp only [goldenZeroSectorLift, goldenNorm, goldenFifthSndFactor]
  ring
```

0373 が lift の第二座標を固定したのに対し、0374 は lift の norm を fifth-power 座標に現れる quartic factor と同一視する。これが zero-sector の algebraic re-entry を本格的に成立させる恒等式である。
