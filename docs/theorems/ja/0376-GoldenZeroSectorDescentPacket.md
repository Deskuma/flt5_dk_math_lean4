# 0376 `GoldenZeroSectorDescentPacket`

## 宣言種別

`structure`

これは theorem ではなく、zero-sector の無限降下で各段階に保存される条件を一つの型へ束ねる構造体宣言である。

## Lean コード

```lean
/--
The invariant preserved by the fifth-power re-entry.  The visible coordinate
is five times a fifth power, and the quartic is itself a fifth power.  Keeping
both statements is what makes the construction genuinely recursive.
-/
structure GoldenZeroSectorDescentPacket where
  base : GoldenInt
  t : ℕ
  D : ℕ
  t_pos : 0 < t
  D_pos : 0 < D
  coprime_coords : Nat.Coprime base.fst.natAbs base.snd.natAbs
  snd_eq :
    base.snd = 5 * (t : ℤ) ^ 5 ∨
      base.snd = -(5 * (t : ℤ) ^ 5)
  H_eq :
    goldenFifthSndFactor base.fst base.snd = (D : ℤ) ^ 5
  five_not_dvd_norm : ¬ (5 : ℤ) ∣ goldenNorm base
```

## Lean の型

構造体 constructor の型を展開すると、概念的には次のデータを受け取って `GoldenZeroSectorDescentPacket` を構成する。

```lean
GoldenZeroSectorDescentPacket.mk :
  (base : GoldenInt) →
  (t D : ℕ) →
  0 < t →
  0 < D →
  Nat.Coprime base.fst.natAbs base.snd.natAbs →
  (base.snd = 5 * (t : ℤ) ^ 5 ∨
    base.snd = -(5 * (t : ℤ) ^ 5)) →
  goldenFifthSndFactor base.fst base.snd = (D : ℤ) ^ 5 →
  (¬ (5 : ℤ) ∣ goldenNorm base) →
  GoldenZeroSectorDescentPacket
```

各 field は projection としても利用できる。たとえば `p : GoldenZeroSectorDescentPacket` に対し、`p.base`, `p.t`, `p.D`, `p.snd_eq`, `p.H_eq` などが得られる。

## 数学的意味

`base = (r,s)` と書く。この packet は、zero-sector 降下のある段階で次を同時に保持する。

$$
(r,s)\in\mathbb Z^2,
$$

$$
t>0,\qquad D>0,
$$

$$
\gcd(|r|,|s|)=1,
$$

$$
s=5t^5\quad\text{または}\quad s=-5t^5,
$$

$$
H(r,s)=D^5,
$$

および

$$
5\nmid N(r,s).
$$

ここで `H` は `goldenFifthSndFactor`、`N` は `goldenNorm` に対応する。

重要なのは、単に「現在の `base` が fifth-power equation を満たす」と記録しているのではなく、 **次の降下段階をもう一度構成するために必要な条件を丸ごと保存している** 点である。

0372--0375 で構成した quadratic lift

$$
T(r,s)=\bigl(r^2+rs+s^2,\ s^2\bigr)
$$

は、quartic factor を黄金整数 norm とその共役積へ戻した。この structure は、その re-entry を一回限りの変形で終わらせず、同じ形の問題をより小さいデータへ反復するための再帰状態である。

## 証明全体での役割

FLT5 の zero-sector 排除では、「第五冪が存在する」と仮定してただ一度矛盾を出すのではなく、同じ性質を持ちながら measure が真に小さい packet を再構成し続ける。

したがって必要なのは次の形である。

$$
P\longmapsto P',
$$

$$
P'\text{ は }P\text{ と同じ不変条件を満たす},
$$

$$
\mu(P')<\mu(P).
$$

`GoldenZeroSectorDescentPacket` はこのうち「同じ不変条件」を型として固定する役目を持つ。後続では `GoldenZeroSectorStrictDescent` が `next : GoldenZeroSectorDescentPacket` を保持し、さらに strict measure decrease を加える。

つまり、この structure は zero-sector infinite descent の **状態空間** である。

## 各 field の役割

### `base : GoldenInt`

現在の黄金整数。座標を

$$
base=(r,s)
$$

と読む。

### `t : ℕ`, `t_pos : 0 < t`

第二座標が `±5 t^5` であることを記述するための正の fifth-root parameter。

### `D : ℕ`, `D_pos : 0 < D`

quartic factor `goldenFifthSndFactor r s` の fifth root。

### `coprime_coords`

```lean
Nat.Coprime base.fst.natAbs base.snd.natAbs
```

符号付き整数座標を `natAbs` で自然数へ移し、primitive condition を保持する。

数学的には

$$
\gcd(|r|,|s|)=1.
$$

### `snd_eq`

```lean
base.snd = 5 * (t : ℤ) ^ 5 ∨
  base.snd = -(5 * (t : ℤ) ^ 5)
```

第二座標の符号を固定せず、positive/negative の双方を一つの packet で扱う。指数 5 が奇数であることと整合する signed fifth-power shape である。

### `H_eq`

```lean
goldenFifthSndFactor base.fst base.snd = (D : ℤ) ^ 5
```

0374--0375 の re-entry で norm / conjugate product に移した quartic factor 自体が第五冪であることを保存する。

これがあるため、次段階でも「fifth root を取り、同型の packet を作る」という操作を再実行できる。

### `five_not_dvd_norm`

```lean
¬ (5 : ℤ) ∣ goldenNorm base
```

例外素数 5 が norm に混入しないことを保存する side condition。黄金整数の factor/coprime 処理で fifth-power root を抽出するときの clean condition として働く。

## 直接依存する定義・補題

この宣言自身は証明を持たないため、直接依存は主として型・定義である。

- `GoldenInt`: `base` の型。
- `goldenFifthSndFactor`: `H_eq` の左辺。
- `goldenNorm`: `five_not_dvd_norm` の対象。
- `Nat.Coprime`: primitive 座標条件。
- `Int.natAbs`: 符号付き座標を自然数の gcd 条件へ送る。
- 自然数・整数の冪、整数への coercion、整数の可除性。

0372 `goldenZeroSectorLift`、0374 `goldenZeroSectorLift_norm`、0375 `goldenZeroSectorLift_mul_conj` は、この structure の field そのものの定義依存ではない。しかし証明全体の依存関係では、この packet を生成・更新するための algebraic re-entry を準備する直前段階である。

## 構築の流れ

`structure` なので、この宣言自体には tactic proof はない。構築時には、各 field を順に与える。

典型的には次のような形になる。

```lean
{
  base := ...
  t := ...
  D := ...
  t_pos := ...
  D_pos := ...
  coprime_coords := ...
  snd_eq := ...
  H_eq := ...
  five_not_dvd_norm := ...
}
```

後続コードでは candidate や fifth root からこの record を再構成し、その record 全体を strong descent の入力として使う。

## Lean 固有の処理

### `structure ... where`

複数の数学的仮定を bundled object にする。以降の theorem が 8 個前後の引数を毎回受け取る代わりに、`p : GoldenZeroSectorDescentPacket` 一つを受け取ればよい。

### coercion `(t : ℤ)` と `(D : ℤ)`

`t`, `D` は positivity と measure 管理のため自然数で保持される一方、`base.snd` と `goldenFifthSndFactor` は整数値なので、等式では明示的に `ℤ` へ cast している。

### `base.fst.natAbs`, `base.snd.natAbs`

`Nat.Coprime` は自然数上の述語なので、整数座標に対して `natAbs` を使う。この選択により符号を無視した primitive condition を直接表現できる。

### `∨` による符号保持

`snd_eq` を `|s| = 5 t^5` のような絶対値等式に潰さず、正負二分岐を明示したまま保持している。後続で符号別の rewrite を行いやすい設計である。

## 冗長・重複箇所

構造体としては意図的な冗長性がある。

`t_pos`, `D_pos` は `snd_eq` や `H_eq` と他の非零条件から場合によっては導ける可能性があるが、現在の API では正値を field として直接保持することで後続証明を単純化している。

また、`snd_eq` は絶対値を使えば一つの等式へ圧縮できる。しかしその場合、後続で符号を復元する補題が必要になり、必ずしも簡潔にならない。

`coprime_coords` も primitive candidate から最初は導出されるが、降下ごとに再証明して packet へ保存することで recursive invariant を自己完結させている。したがって、これらはコード重複というより **再帰閉包のための証明キャッシュ** と見るのが適切である。

## 最適化候補

1. `snd_eq` を表す専用 predicate、たとえば `IsSignedFiveTimesFifthPower base.snd t` を導入すれば、同種の signed equation を他箇所でも共有できる可能性がある。

2. `coprime_coords` を黄金整数向け primitive predicate にまとめれば、`base.fst.natAbs` / `base.snd.natAbs` の反復を隠蔽できる。

3. `t_pos`, `D_pos` を `PNat` 的 subtype に埋め込む設計も可能だが、cast や既存 theorem との接続が増えるため、現状の plain `ℕ` + positivity field の方が Lean では扱いやすい可能性が高い。

4. `H_eq` と `five_not_dvd_norm` は descent の核心なので、これらを別 packet に分割するより現状の一体化の方が strong induction の入力として明快である。

いずれも設計候補であり、現在の正本が冗長で誤っていることを意味しない。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

この structure 単体が Mathlib 側で必要とする機能は、概ね次の範囲である。

- `Nat.Coprime`
- `Int.natAbs`
- `Pow`
- 整数の可除性
- `Nat` / `Int` coercion

ただし `GoldenInt`, `goldenFifthSndFactor`, `goldenNorm` はプロジェクト内の先行定義であり、実際の modular source に必要な最小 import はそれらの定義所在との依存関係で決まる。

この repository の standalone artifact だけから厳密な最小 Mathlib import 集合を断定することはできない。また今回は Lean ビルドを行っていないため、import 削減の機械検証も行っていない。

## Comparator challenge 化の可否

**可能。特に structure reconstruction challenge に向く。**

この宣言自体を再定義させるだけでは challenge として弱いが、packet の projection と constructor を使い、与えられた field から同値な packet を再構成する課題にできる。

たとえば、

```lean
example (p : GoldenZeroSectorDescentPacket) :
    GoldenZeroSectorDescentPacket := by
  exact {
    base := p.base
    t := p.t
    D := p.D
    t_pos := p.t_pos
    D_pos := p.D_pos
    coprime_coords := p.coprime_coords
    snd_eq := p.snd_eq
    H_eq := p.H_eq
    five_not_dvd_norm := p.five_not_dvd_norm }
```

のような最小課題から、candidate data を packet 化する challenge へ発展できる。

Comparator では theorem proving よりも、 **dependent field を含む bundled invariant の正確な再構築** を評価する題材として適している。

## 次に読むべき宣言

次は

```lean
def goldenZeroSectorDescentMeasure (p : GoldenZeroSectorDescentPacket) : ℕ :=
  p.base.snd.natAbs
```

である。

0376 が descent の状態空間を定義したのに対し、次宣言はその packet に自然数値 measure

$$
\mu(P)=|P.base.snd|
$$

を与える。後続の `GoldenZeroSectorStrictDescent` は、この measure が次 packet で真に減少することを field として保持し、最終的に `Nat.strong_induction_on` で zero-sector packet の存在そのものを否定する。
