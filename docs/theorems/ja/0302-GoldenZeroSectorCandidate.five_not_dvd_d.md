# 0302 — `GoldenZeroSectorCandidate.five_not_dvd_d`

## 宣言種別

これは **`theorem`** である。

zero-sector candidate の quartic factor が 5 で割れないことと、その quartic factor が tenth power `d^10` に一致することから、base `d` 自身も 5 で割れないこと

$$
5\nmid d
$$

を証明する。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- The quartic tenth-power base is not divisible by five. -/
theorem five_not_dvd_d (p : GoldenZeroSectorCandidate) : ¬ 5 ∣ p.d := by
  intro h5d
  apply p.five_not_dvd_H
  rw [p.H_eq_tenth]
  exact dvd_pow (Int.natCast_dvd.mpr h5d) (by decide : 10 ≠ 0)
```

結論は自然数上の非可除性

```lean
¬ 5 ∣ p.d
```

である。一方、途中で利用する `five_not_dvd_H` は整数上の非可除性

```lean
¬ (5 : ℤ) ∣ goldenFifthSndFactor p.r p.s
```

なので、証明内部では `ℕ` から `ℤ` への divisibility cast が入る。

## 数学的意味

直前の 0301 `GoldenZeroSectorCandidate.five_not_dvd_H` により

$$
5\nmid H(r,s)
$$

が得られている。また 0297 `GoldenZeroSectorCandidate.H_eq_tenth` により

$$
H(r,s)=d^{10}
$$

が得られている。

ここで仮に

$$
5\mid d
$$

とすると、当然

$$
5\mid d^{10}
$$

である。したがって

$$
5\mid H(r,s),
$$

となり 0301 と矛盾する。ゆえに

$$
5\nmid d.
$$

本 theorem は、quartic factor 全体に対する prime-five exclusion を、その tenth-power base へ降ろす単純だが重要な descent である。

## 証明全体での役割

0290 以降の zero-sector inversion では、quartic factor の absolute-value split

$$
|H(r,s)|=d^{10}
$$

から 0297 で符号を除去し、

$$
H(r,s)=d^{10}
$$

まで戻している。0301 では norm channel を利用して

$$
5\nmid H(r,s)
$$

を確定した。

0302 はこの二つを合成し、後続で実際に使いやすい base-level の条件

$$
5\nmid d
$$

へ変換する。

この情報は直後の parity 系だけでなく、その後に構築される `GoldenZeroSectorInversionPacket` の field

```lean
five_not_dvd_d : ¬ 5 ∣ source.d
```

として保存される。さらに後続の factorization 層では `zeroSectorQ c` と `d` の coprimality を証明する際、5 の成分が `d` に侵入していないことを直接利用する。

したがって本 theorem は、 **five-adic ownership を quartic factor から split base `d` へ確定的に降ろす境界補題** と位置づけられる。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate`

本 theorem の引数 `p`。特に `p.d : ℕ` と座標 `p.r`, `p.s` を利用する。

### `GoldenZeroSectorCandidate.five_not_dvd_H`

直前の 0301。

```lean
theorem five_not_dvd_H (p : GoldenZeroSectorCandidate) :
    ¬ (5 : ℤ) ∣ goldenFifthSndFactor p.r p.s
```

本 theorem の矛盾先そのものである。

### `GoldenZeroSectorCandidate.H_eq_tenth`

0297。

```lean
theorem H_eq_tenth (p : GoldenZeroSectorCandidate) :
    goldenFifthSndFactor p.r p.s = (p.d : ℤ) ^ 10
```

これにより quartic factor の問題を integer-cast された `d^10` の問題へ置き換える。

### `Int.natCast_dvd`

```lean
Int.natCast_dvd.mpr h5d
```

により

```lean
h5d : 5 ∣ p.d
```

を

```lean
(5 : ℤ) ∣ (p.d : ℤ)
```

へ持ち上げる。

### `dvd_pow`

base が割れるなら正の冪も割れることを使う。

```lean
dvd_pow (Int.natCast_dvd.mpr h5d) (by decide : 10 ≠ 0)
```

ここでは指数 10 が 0 ではないことを明示して

$$
5\mid (d:\mathbb Z)^{10}
$$

を得る。

### `decide`

```lean
(by decide : 10 ≠ 0)
```

という閉じた decidable proposition を計算で解決する。

## 証明または構築の流れ

1. 結論 `¬ 5 ∣ p.d` を証明するため、
   ```lean
   intro h5d
   ```
   として $5\mid d$ を仮定する。
2. 
   ```lean
   apply p.five_not_dvd_H
   ```
   により、0301 の否定命題へ矛盾を渡す形にする。新しい目標は
   ```lean
   (5 : ℤ) ∣ goldenFifthSndFactor p.r p.s
   ```
   となる。
3. 
   ```lean
   rw [p.H_eq_tenth]
   ```
   で quartic factor を `(p.d : ℤ)^10` に書き換える。
4. `Int.natCast_dvd.mpr h5d` により自然数上の $5\mid d$ を整数上へ持ち上げる。
5. `dvd_pow` に指数の非零性 `(by decide : 10 ≠ 0)` を与えて
   $$
   5\mid(d:\mathbb Z)^{10}
   $$
   を得る。
6. これは `p.five_not_dvd_H` と矛盾し、仮定 $5\mid d$ が排除される。

## Lean 固有の処理

数学的には証明は

$$
5\mid d
\Rightarrow
5\mid d^{10}=H
$$

の一行である。Lean で主要になるのは **型の境界** である。

`p.d` は `ℕ` だが `H_eq_tenth` の右辺は

```lean
(p.d : ℤ) ^ 10
```

であるため、`h5d : 5 ∣ p.d` をそのまま `dvd_pow` に与えることはできない。そこで

```lean
Int.natCast_dvd.mpr h5d
```

を用い、divisibility を `ℤ` へ運んでから冪へ上げる。

また `dvd_pow` は指数が非零であることを要求するため、具体的指数 10 に対して

```lean
(by decide : 10 ≠ 0)
```

を渡している。

## 冗長・重複箇所

本 theorem 自体は非常に短く、局所的な冗長性はほぼない。

数学的には一般形

```lean
¬ p ∣ x ^ n → n ≠ 0 → ¬ p ∣ x
```

あるいは prime を仮定するなら `Prime.dvd_of_dvd_pow` の否定形で処理することも考えられる。しかし現行実装は「`d` が割れると `d^10` も割れる」という順方向の含意だけを使っており、prime 性すら不要である。

そのため 0301 のような five-specific arithmetic を終えた後、0302 では余計な素数論を再導入せず、単なる divisibility transport に徹している。この分離は監査上むしろ良い。

重複候補としては、今後 `x^n` の非可除性から base の非可除性を降ろす theorem が多数現れるなら helper 化できる。しかし現時点では 4 行の証明を抽象化する利益は小さい。

## 最適化候補

1. `dvd_pow` を明示する現在形は十分に簡潔である。
2. `Int.natCast_dvd.mpr` と `dvd_pow` の組み合わせが頻出するなら cast-aware helper theorem を用意する余地はある。
3. `H_eq_tenth` の右辺が自然数 divisibility と直接連携できる API を別途持つなら cast を減らせるが、quartic factor 本体は `ℤ` 値なので現行設計の方が自然である。
4. `by decide : 10 ≠ 0` は `by norm_num` に置換可能と思われるが、閉じた proposition に対する `decide` の方が軽量で意図も明瞭である。

これらは Lean build を行っていないため、代替案の成立性は **未検証** である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

manifest 上では本 theorem は

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

の領域に属する。

本 theorem 自体が直接必要とする Mathlib 機能は主として

- divisibility `∣`
- `Int.natCast_dvd`
- `dvd_pow`
- `decide`
- `rw`, `intro`, `apply`

である。

`ring`, `ring_nf`, `omega`, `linarith`, `nlinarith`, `norm_num`, `exact_mod_cast` は本 theorem 本体では使用しない。

したがって standalone 全体の `import Mathlib` に比べれば、本 theorem 単独の import は大幅に縮小可能と思われる。ただし `GoldenZeroSectorCandidate`, `goldenFifthSndFactor`, `H_eq_tenth`, `five_not_dvd_H` の定義・証明を含む upstream module の import closure が必要であるため、厳密な最小 import 集合は Lean build 禁止条件のもとでは **未確認** である。

## Comparator challenge 化の可否

**適している。** 難度は初級から中級の境界程度である。

challenge としては次を与えられる。

```lean
hH : ¬ (5 : ℤ) ∣ H
heq : H = (d : ℤ) ^ 10
```

目標を

```lean
¬ 5 ∣ d
```

とする。

評価点は、

- contradiction の向きを適切に選べるか
- `ℕ` 上の divisibility を `ℤ` へ cast できるか
- `dvd_pow` の指数非零条件を処理できるか
- `heq` を rewrite して既存の非可除性へ接続できるか

である。

0301 に比べると数論そのものは軽いが、Lean の coercion と theorem application の基本技能をきれいに測れるので Comparator challenge として有用である。

## PDF との対応

対象 branch の repository tree には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

ただし GitHub コネクタの通常のテキスト取得は binary PDF 本文を返さないため、この実行では PDF 内の具体的ページ・節番号を直接照合できていない。したがって、PDF における本 theorem の正確な節番号や表現との一対一対応は **未確認** とする。

Lean コードについては対象 branch の `Flt5DkMath/FLT5StandAlone.lean` にある宣言本体と、その直前の 0301、直後の `H_odd` まで確認した。

## 次に読むべき宣言

次は

```lean
GoldenZeroSectorCandidate.H_odd
```

である。種別は **`theorem`**。

Lean 正本では直後に

```lean
/-- The primitive-coordinate quartic is odd. -/
theorem H_odd (p : GoldenZeroSectorCandidate) :
    Odd (goldenFifthSndFactor p.r p.s) := by
  ...
```

と続く。

0302 までで five-adic exclusion

$$
5\nmid d
$$

が base level に降りた後、次は primitive coordinate の parity を場合分けして quartic factor 自身が odd であることを示す。その直後には `d_odd` があり、

$$
H=d^{10},\qquad H\text{ odd}
$$

から

$$
d\text{ odd}
$$

を復元する。

従って次の二段は、0301→0302 の five-adic descent と平行して、`H` の parity を `d` へ降ろす parity descent になっている。
