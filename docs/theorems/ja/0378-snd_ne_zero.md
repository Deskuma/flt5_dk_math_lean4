# 0378 `snd_ne_zero`

## 宣言種別

`theorem`

`GoldenZeroSectorDescentPacket` の namespace 内で、packet の第二座標が非零であることを証明する補題である。

## Lean コード

```lean
theorem snd_ne_zero (p : GoldenZeroSectorDescentPacket) :
    p.base.snd ≠ 0 := by
  have ht : (0 : ℤ) < p.t := by exact_mod_cast p.t_pos
  rcases p.snd_eq with h | h
  · rw [h]
    exact ne_of_gt (mul_pos (by norm_num) (pow_pos ht 5))
  · rw [h]
    exact neg_ne_zero.mpr (ne_of_gt (mul_pos (by norm_num) (pow_pos ht 5)))
```

## Lean の型

namespace を展開して見ると、型は概念的に

```lean
GoldenZeroSectorDescentPacket.snd_ne_zero :
  (p : GoldenZeroSectorDescentPacket) → p.base.snd ≠ 0
```

である。

`p.base.snd : ℤ` は packet の現在の黄金整数 `base` の第二座標であり、この theorem は

$$
p.base.snd \ne 0
$$

を返す。

## 数学的主張

0376 `GoldenZeroSectorDescentPacket` は

$$
t>0
$$

と

$$
s=5t^5 \quad\text{または}\quad s=-5t^5
$$

を field として保存している。ここで `s = p.base.snd` である。

したがって

$$
5t^5>0
$$

であり、正符号の場合は直ちに

$$
s>0 \Longrightarrow s\ne0,
$$

負符号の場合も

$$
s=-5t^5 \Longrightarrow s\ne0
$$

となる。

この theorem は、その elementary な事実を packet API として固定する。

## 証明全体での役割

この補題は zero-sector infinite descent の positivity chain の入口である。

直後の補題群では `p.base.snd` の絶対値・平方・fifth-root re-entry を扱う。特に後続 `fifthRoot_H_pos` と `fifthRoot_snd_pos` では

```lean
have hsSq : 0 < p.base.snd ^ 2 := sq_pos_of_ne_zero p.snd_ne_zero
```

という形で今回の theorem が使われる。

したがって流れは

$$
p.t>0
\Longrightarrow p.base.snd\ne0
\Longrightarrow p.base.snd^2>0
$$

となり、この正値性が fifth root の第二座標や quartic factor の正値性へ伝播する。

また 0377 で定義した measure

$$
\mu(p)=|p.base.snd|
$$

が実際に正の量を測っていることの基礎事実でもある。

## 直接依存する定義・補題

直接使っているのは次である。

- `GoldenZeroSectorDescentPacket`
- `GoldenZeroSectorDescentPacket.t_pos`
- `GoldenZeroSectorDescentPacket.snd_eq`
- `exact_mod_cast`
- `pow_pos`
- `mul_pos`
- `ne_of_gt`
- `neg_ne_zero.mpr`
- `norm_num`

数学的依存の中心は `t_pos` と `snd_eq` の二つだけである。

## 証明の流れ

1. `p.t_pos : 0 < p.t` を整数へ移し、

   ```lean
   have ht : (0 : ℤ) < p.t := by exact_mod_cast p.t_pos
   ```

   とする。

2. `p.snd_eq` を場合分けして

   ```lean
   rcases p.snd_eq with h | h
   ```

   により

   $$
   s=5t^5
   $$

   または

   $$
   s=-5t^5
   $$

   を得る。

3. 正符号側では `rw [h]` 後、`pow_pos ht 5` と `mul_pos` から $5t^5>0$ を示し、`ne_of_gt` で非零性を得る。

4. 負符号側では同じ正値性から $5t^5\ne0$ を得て、`neg_ne_zero.mpr` によりその負号付き値も非零とする。

## Lean 固有の処理

### `exact_mod_cast`

`p.t_pos` は自然数上の

```lean
0 < p.t
```

だが、`p.base.snd` の式は整数である。そのため証明開始時に

```lean
have ht : (0 : ℤ) < p.t := by exact_mod_cast p.t_pos
```

として整数側の positivity lemma へ橋渡ししている。

### `rcases ... with h | h`

`p.snd_eq` は disjunction なので、符号を二分岐で処理する。これは packet が第二座標の符号を固定せず、絶対値として同一の fifth-power mass を保持する設計に対応する。

### `rw [h]`

抽象座標 `p.base.snd` を具体的な $\pm5t^5$ へ置き換えることで、以後は純粋な整数 positivity 問題になる。

### `ne_of_gt` と `neg_ne_zero.mpr`

正値性から非零性を作る部分は constructive に明示されている。負符号側では `-x ≠ 0 ↔ x ≠ 0` を使うため `neg_ne_zero.mpr` が現れる。

## 冗長・重複箇所

二分岐の内部で

```lean
ne_of_gt (mul_pos (by norm_num) (pow_pos ht 5))
```

が実質的に重複している。

先に

```lean
have hpos : (0 : ℤ) < 5 * (p.t : ℤ) ^ 5 :=
  mul_pos (by norm_num) (pow_pos ht 5)
have hne : (5 : ℤ) * (p.t : ℤ) ^ 5 ≠ 0 := ne_of_gt hpos
```

と置けば、両分岐は `hne` を共有できる。

ただし現在の証明は短く、各枝の数学的意味も直接見えるため、この重複は可読性との交換条件である。

## 最適化候補

1. `snd_natAbs_eq` を先に使える配置なら、絶対値が $5t^5$ かつ `t_pos` であることから非零性を導く方法もある。ただし現行順序では `snd_ne_zero` が先に置かれているため、依存方向を増やさない現在の証明が自然である。

2. 共通する $5t^5>0$ を局所補題へ切り出すと二分岐の重複を減らせる。

3. packet API として `measure_pos` を追加する場合、今回の `snd_ne_zero` と 0377 `goldenZeroSectorDescentMeasure` から簡潔に証明できる可能性がある。

4. `snd_eq` 自体を absolute-value equation と符号情報へ分離する設計も考えられるが、後続で符号付き等式を直接使うため、現在の disjunction を保持する合理性がある。

## 必要 Mathlib import と import 最適化候補

standalone 正本は `import Mathlib` を使用している。

今回の theorem が直接必要とする機能は、整数・自然数 cast、順序、整数の冪、`exact_mod_cast`、`norm_num`、および基本的な非零補題である。

ただし `GoldenZeroSectorDescentPacket` 自体がプロジェクト内の先行定義に依存するため、実際の modular file ではその定義を含むプロジェクト側 import が必要である。

厳密な最小 Mathlib import は Lean ビルドを行わない条件のため確認していない。よって `import Mathlib` からの具体的な削減先は候補に留める。

## Comparator challenge 化の可否

**可能。小規模だが良い cast / sign-split challenge になる。**

核心は次の三点である。

- `Nat` の正値性を `ℤ` へ移す。
- disjunction で正負を分ける。
- positivity から非零性を構成する。

Comparator 用には theorem 本体をそのまま穴埋めにしてもよい。さらに `exact_mod_cast` を禁止し、明示的 cast lemma で再構成させれば、より Lean 固有の型変換能力を測れる。

## 次に読むべき宣言

次は同じ namespace の

```lean
theorem snd_natAbs_eq (p : GoldenZeroSectorDescentPacket) :
    p.base.snd.natAbs = 5 * p.t ^ 5 := by
  rcases p.snd_eq with h | h <;> rw [h]
  · simp [Int.natAbs_mul, Int.natAbs_pow]
  · simp [Int.natAbs_mul, Int.natAbs_pow]
```

である。

今回が

$$
s\ne0
$$

という qualitative な非退化性を取り出したのに対し、次は

$$
|s|=5t^5
$$

という exact quantitative formula を得る。0377 の measure と直結するため、zero-sector descent の大小比較へ向けて一段具体化する宣言である。