# 0379 `snd_natAbs_eq`

## 宣言種別

`theorem`

`GoldenZeroSectorDescentPacket` の namespace 内で、packet の第二座標の自然数絶対値を、保存されている fifth-power parameter `t` で正確に表す補題である。

## Lean コード

```lean
theorem snd_natAbs_eq (p : GoldenZeroSectorDescentPacket) :
    p.base.snd.natAbs = 5 * p.t ^ 5 := by
  rcases p.snd_eq with h | h <;> rw [h]
  · simp [Int.natAbs_mul, Int.natAbs_pow]
  · simp [Int.natAbs_mul, Int.natAbs_pow]
```

## Lean の型

namespace を展開すると、型は概念的に

```lean
GoldenZeroSectorDescentPacket.snd_natAbs_eq :
  (p : GoldenZeroSectorDescentPacket) →
    p.base.snd.natAbs = 5 * p.t ^ 5
```

である。

`p.base.snd : ℤ` に対し `Int.natAbs` を取るため、左辺は `ℕ` である。右辺も `p.t : ℕ` から作られた

$$
5t^5
$$

という自然数であり、両辺は同じ型 `ℕ` にある。

## 数学的主張

0376 `GoldenZeroSectorDescentPacket` は第二座標について

$$
s=5t^5
\quad\text{または}\quad
s=-5t^5
$$

を保存する。ここで

$$
s=p.base.snd.
$$

したがって符号に依存せず

$$
|s|=5t^5
$$

である。

Lean の `Int.natAbs` は整数絶対値を自然数として返すので、定理の主張は正確には

$$
\operatorname{natAbs}(p.base.snd)=5p.t^5
$$

である。

0378 `snd_ne_zero` が $s\ne0$ という qualitative な非退化性を与えたのに対し、今回の theorem はその大きさを完全に決める quantitative な等式を与える。

## 証明全体での役割

0377 で descent measure は

$$
\mu(p)=|p.base.snd|
$$

と定義されている。今回の theorem により、この measure は packet parameter `t` を使って

$$
\mu(p)=5t^5
$$

と読める。

この exact formula は後続 `fifthRoot_power_split` で直接使われる。そこでは fifth root `gamma` の第二座標と quartic factor の積から

$$
|s|^2
$$

が現れ、今回の等式によって

$$
|s|^2=(5t^5)^2
$$

へ変換される。さらに代数整理して

$$
|\gamma_2|\,|H(\gamma)|=5(t^2)^5
$$

という coprime fifth-power splitting の形を得る。

Lean 正本では実際に

```lean
_ = (5 * p.t ^ 5) ^ 2 := by rw [p.snd_natAbs_eq]
_ = 5 * (5 * (p.t ^ 2) ^ 5) := by ring
```

と使用される。

したがってこの補題は、packet の signed coordinate invariant を、再帰的 fifth-power factorization が消費できる unsigned natural-number invariant へ変換する bridge である。

## 直接依存する定義・補題

直接依存するプロジェクト内宣言は次である。

- `GoldenZeroSectorDescentPacket`
- `GoldenZeroSectorDescentPacket.snd_eq`

Mathlib / Lean 側で直接使う主要機能は次である。

- `Int.natAbs`
- `Int.natAbs_mul`
- `Int.natAbs_pow`
- `rcases`
- `rw`
- `simp`

0378 `snd_ne_zero` には依存しない。今回の theorem は `snd_eq` だけから独立に導かれている。

## 証明の流れ

1. packet の符号付き等式

   ```lean
   p.snd_eq :
     p.base.snd = 5 * (p.t : ℤ) ^ 5 ∨
       p.base.snd = -(5 * (p.t : ℤ) ^ 5)
   ```

   を

   ```lean
   rcases p.snd_eq with h | h
   ```

   で二分岐する。

2. `<;> rw [h]` により両方の枝で `p.base.snd` を具体的な signed fifth-power expression に置換する。

3. 正符号側では

   $$
   |5t^5|=5t^5
   $$

   を `simp` が `Int.natAbs_mul` と `Int.natAbs_pow` を使って処理する。

4. 負符号側でも

   $$
   |-5t^5|=5t^5
   $$

   となり、負号は `natAbs` により消える。

結果として両枝が同じ自然数式へ合流する。

## Lean 固有の処理

### `rcases ... with h | h`

`p.snd_eq` は符号を保持する disjunction なので、そのままでは単一の rewrite equation ではない。`rcases` で各符号を明示的に分解している。

### `<;> rw [h]`

セミコロン combinator `<;>` により、直前の case split で生成された両 goal に同じ `rw [h]` を適用している。

この書き方は

```lean
rcases p.snd_eq with h | h
· rw [h]
  ...
· rw [h]
  ...
```

の重複を縮める Lean 固有の tactic scripting である。

### `Int.natAbs_mul`

整数積の自然数絶対値を自然数積へ変換する。

概念的には

$$
|ab|=|a||b|.
$$

ここでは整数の係数 `5` と `(p.t : ℤ)^5` を自然数側の積へ移すために使われる。

### `Int.natAbs_pow`

整数冪の `natAbs` を自然数冪へ移す。

$$
|x^n|=|x|^n.
$$

`p.t` はもともと自然数なので、cast の絶対値が再び `p.t` に簡約される。

### `simp`

正枝と負枝の双方で、`natAbs` の乗法性・冪との交換・負号不変性・自然数 cast をまとめて正規化する。

証明の数学的内容は非常に小さいが、`ℤ` 上の signed invariant を `ℕ` 上の measure equality に落とす型変換を `simp` が担っている。

## 冗長・重複箇所

二つの枝はどちらも完全に同じ

```lean
simp [Int.natAbs_mul, Int.natAbs_pow]
```

で閉じている。

したがって tactic としては、より圧縮して

```lean
  rcases p.snd_eq with h | h <;>
    rw [h] <;>
    simp [Int.natAbs_mul, Int.natAbs_pow]
```

のように一列化できる可能性がある。

ただし現行コードは二枝を視覚的に残しており、`snd_eq` が正負二ケースであることを読み手に明示する利点がある。ここはコード量より説明性を優先した配置と解釈できる。

また `Int.natAbs_mul` と `Int.natAbs_pow` は現在の Mathlib の simp set の状況によっては明示しなくても閉じる可能性があるが、この点は Lean ビルドを行わない条件のため未確認である。

## 最適化候補

1. **両枝の `simp` を統合する**

   完全に同一の tactic なので、`<;>` によって一つへまとめられる。

2. **measure 用 API を追加する**

   0377 の定義と今回の theorem から

   ```lean
   theorem descentMeasure_eq (p : GoldenZeroSectorDescentPacket) :
       goldenZeroSectorDescentMeasure p = 5 * p.t ^ 5 := ...
   ```

   のような named lemma を用意すると、後続が `base.snd.natAbs` の実装詳細を知らずに済む。

3. **measure positivity の公開**

   `p.t_pos` と今回の theorem から

   $$
   0<\mu(p)
   $$

   を容易に導ける。`goldenZeroSectorDescentMeasure_pos` のような lemma は、well-founded descent の API として自然である。

4. **signed / unsigned invariant の分離**

   packet に `snd_eq` とともに `snd_natAbs_eq` 相当を field として持たせれば後続証明は短くなる。しかし同じ情報の二重保持となるため、現在のように theorem として導出する方が invariant の最小性は高い。

## 必要 Mathlib import と import 最適化候補

standalone 正本は `import Mathlib` を使用している。

この theorem 単体で必要なのは、整数・自然数、`Int.natAbs`、冪、基本 tactic `rcases` / `rw` / `simp` と、`Int.natAbs_mul`・`Int.natAbs_pow` を提供する Mathlib 部分である。

ただし実際の theorem はプロジェクト定義 `GoldenZeroSectorDescentPacket` に依存するため、modular file ではその packet 定義まで到達する DkMath / FLT5 側 import が必要である。

厳密な最小 Mathlib import は Lean ビルドを行わない条件のため確認していない。よって `import Mathlib` から特定 module への削減は候補に留める。

## Comparator challenge 化の可否

**可能。小規模な sign-elimination / `natAbs` normalization challenge に適する。**

challenge として残る本質は次である。

- disjunction による正負二ケースの処理
- `ℤ` から `ℕ` への `natAbs` 正規化
- multiplication と power に対する `natAbs` の伝播
- negative branch の符号消去

難度は低いが、Lean の integer/natural-number boundary を正しく扱えるかを見る micro challenge としては明確である。

より難しくする場合は `simp` の使用を制限し、`Int.natAbs_mul`、`Int.natAbs_pow`、`Int.natAbs_neg` などを明示的に組み立てさせる形式が適する。

## 次に読むべき宣言

次は同じ namespace の

```lean
theorem H_pos (p : GoldenZeroSectorDescentPacket) :
    0 < goldenFifthSndFactor p.base.fst p.base.snd := by
  rw [p.H_eq]
  exact pow_pos (by exact_mod_cast p.D_pos) 5
```

である。

packet は

$$
H(p.base.fst,p.base.snd)=D^5,
\qquad D>0
$$

を保存しているため、次の theorem は

$$
H(p.base.fst,p.base.snd)>0
$$

を抽出する。

今回が第二座標の signed equation を自然数絶対値へ変換したのに対し、次は quartic side の fifth-power invariant から正値性を取り出す。これにより、descent packet の二つの主要因子

$$
|s|
\quad\text{と}\quad
H(r,s)
$$

がともに非退化な正値量として扱えるようになる。