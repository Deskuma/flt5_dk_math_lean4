# 0303 — `GoldenZeroSectorCandidate.H_odd`

## 宣言種別

これは **`theorem`** である。

primitive な zero-sector 座標 `r`,`s` の互いに素性から、quartic second-coordinate factor

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s)
$$

が奇数であることを証明する。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- The primitive-coordinate quartic is odd. -/
theorem H_odd (p : GoldenZeroSectorCandidate) :
    Odd (goldenFifthSndFactor p.r p.s) := by
  have hterm2 : Even (2 * p.r ^ 3 * p.s) :=
    (even_two.mul_right (p.r ^ 3)).mul_right p.s
  have hfour : Even (4 : ℤ) := ⟨2, by norm_num⟩
  have hterm3 : Even (4 * p.r ^ 2 * p.s ^ 2) :=
    (hfour.mul_right (p.r ^ 2)).mul_right (p.s ^ 2)
  rcases Int.even_or_odd p.r with hr | hr <;>
    rcases Int.even_or_odd p.s with hs | hs
  · exfalso
    have hrNat : Even p.r.natAbs := hr.natAbs
    have hsNat : Even p.s.natAbs := hs.natAbs
    exact (Nat.not_coprime_of_dvd_of_dvd (by omega)
      hrNat.two_dvd hsNat.two_dvd) p.coprime_coords
  · unfold goldenFifthSndFactor
    have hterm1 : Even (p.r ^ 4) :=
      hr.pow_of_ne_zero (by decide : 4 ≠ 0)
    have hterm4 : Even (3 * p.r * p.s ^ 3) :=
      (hr.mul_left 3).mul_right (p.s ^ 3)
    have hterm5 : Odd (p.s ^ 4) := hs.pow
    exact (((hterm1.add hterm2).add hterm3).add hterm4).add_odd hterm5
  · unfold goldenFifthSndFactor
    have hterm1 : Odd (p.r ^ 4) := hr.pow
    have hterm4 : Even (3 * p.r * p.s ^ 3) :=
      (hs.pow_of_ne_zero (by decide : 3 ≠ 0)).mul_left (3 * p.r)
    have hterm5 : Even (p.s ^ 4) :=
      hs.pow_of_ne_zero (by decide : 4 ≠ 0)
    exact (((hterm1.add_even hterm2).add_even hterm3).add_even hterm4).add_even hterm5
  · unfold goldenFifthSndFactor
    have hterm1 : Odd (p.r ^ 4) := hr.pow
    have hthree : Odd (3 : ℤ) := ⟨1, by norm_num⟩
    have hterm4 : Odd (3 * p.r * p.s ^ 3) :=
      (hthree.mul hr).mul hs.pow
    have hterm5 : Odd (p.s ^ 4) := hs.pow
    exact (((hterm1.add_even hterm2).add_even hterm3).add_odd hterm4).add_odd hterm5
```

結論の型は整数上の parity proposition

```lean
Odd (goldenFifthSndFactor p.r p.s)
```

である。

## 数学的意味

Lean コードで展開される quartic factor は

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4.
$$

中央の二項

$$
2r^3s,\qquad 4r^2s^2
$$

は `r`,`s` の偶奇に関係なく常に偶数である。したがって parity を決めるのは主として

$$
r^4,\qquad 3rs^3,\qquad s^4
$$

である。

candidate は

$$
\gcd(|r|,|s|)=1
$$

を `p.coprime_coords` として保持しているので、`r`,`s` が同時に偶数になることはない。残る三場合を調べる。

1. `r` 偶、`s` 奇なら、`r^4` と `3rs^3` は偶数、`s^4` は奇数なので $H$ は奇数。
2. `r` 奇、`s` 偶なら、`r^4` は奇数、`3rs^3` と `s^4` は偶数なので $H$ は奇数。
3. `r` 奇、`s` 奇なら、`r^4`,`3rs^3`,`s^4` はすべて奇数で、奇数三個の和は奇数。常に偶数の二項を加えても parity は変わらない。

従って全ての primitive coordinate case で

$$
H(r,s)\equiv1\pmod2
$$

である。

## 証明全体での役割

0301→0302 では quartic factor に対する prime-five exclusion

$$
5\nmid H(r,s)
$$

を tenth-power base `d` へ降ろし、

$$
5\nmid d
$$

を得た。

0303 からはこれと平行な parity channel に入る。本 theorem はまず factor 側で

$$
H(r,s)\text{ is odd}
$$

を確定する。直後の 0304 `GoldenZeroSectorCandidate.d_odd` は 0297 の

$$
H(r,s)=d^{10}
$$

を使い、この oddness を base 側へ降ろして

$$
d\text{ is odd}
$$

を得る。

後続の inversion では `W=4d^5` や二つの factor `A`,`B` の 2-adic 構造を追跡するため、`d` の奇性は重要な入力となる。特に even-`c` branch で factor の 2-adic valuation を区別する際、`d^5` が奇数であることが factor difference の parity を固定する。

したがって 0303 は、 **primitive coordinate の coprimality を quartic factor の 2-adic unit 性へ変換する入口** である。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate`

本 theorem の引数 `p`。特に

```lean
p.r : ℤ
p.s : ℤ
p.coprime_coords : Nat.Coprime p.r.natAbs p.s.natAbs
```

を利用する。

### `goldenFifthSndFactor`

parity を判定する quartic polynomial。本 proof では各有効 branch で `unfold goldenFifthSndFactor` し、各項の偶奇を個別に合成する。

### `Int.even_or_odd`

各整数について even / odd の完全場合分けを与える。`r`,`s` の二重場合分けにより四 branch を作る。

### `Even.natAbs` と `Nat.not_coprime_of_dvd_of_dvd`

`r`,`s` が両方 even の branch で、整数上の偶性を natural absolute value の偶性へ移す。

そこから

```lean
hrNat.two_dvd : 2 ∣ p.r.natAbs
hsNat.two_dvd : 2 ∣ p.s.natAbs
```

を得て `p.coprime_coords` と矛盾させる。

### `Even` / `Odd` の積・和・冪 API

`mul_left`, `mul_right`, `pow`, `pow_of_ne_zero`, `add_even`, `add_odd` などを用い、polynomial の各 monomial の parity を型として合成する。

### `norm_num`, `omega`, `decide`

`4` が even、`3` が odd という閉じた算術事実、共通因子 `2` が非自明であること、指数 `3`,`4` の非零性を処理する。

## 証明または構築の流れ

1. `2 * r^3 * s` が常に even であることを `hterm2` として先に固定する。
2. `4` 自身の evenness `hfour` を作り、`4 * r^2 * s^2` が常に even であることを `hterm3` として固定する。
3. `Int.even_or_odd p.r` と `Int.even_or_odd p.s` を組み合わせ、四つの parity branch に分ける。
4. even-even branch では `natAbs` に移した両座標がとも 2 で割れるため、`p.coprime_coords` と矛盾する。
5. even-odd branch では quartic を展開し、最終項 `s^4` だけが odd であることから全体を odd とする。
6. odd-even branch では先頭項 `r^4` だけが odd であることから全体を odd とする。
7. odd-odd branch では `r^4`, `3*r*s^3`, `s^4` が odd、残り二項が even であることを合成し、全体を odd とする。

## Lean 固有の処理

数学的には mod 2 で一行に圧縮できる議論だが、Lean 実装は `Even` / `Odd` proposition の algebraic API を明示的に使っている。

特に同時偶数を排除するとき、candidate の primitive 条件は `ℕ` 上の

```lean
Nat.Coprime p.r.natAbs p.s.natAbs
```

なので、整数の `Even p.r`, `Even p.s` から `.natAbs` を経由して自然数 divisibility へ落とす必要がある。

また even power の証明では

```lean
hr.pow_of_ne_zero (by decide : 4 ≠ 0)
```

のように指数非零条件が現れる一方、odd power は `hs.pow` のように指数条件なしで扱える。この非対称性は Mathlib の parity API に由来する Lean 固有の形である。

最後の parity 合成も通常の算術 simplifier に丸投げせず、`add_even` / `add_odd` を順に適用して証明項を構築しているため、どの項が parity を反転させるかが明示されている。

## 冗長・重複箇所

`hterm2` と `hterm3` を case split の外で共有している点は既に良い最適化である。両項は全 branch で必ず even なので、各 branch で再証明する重複を避けている。

一方、三つの有効 branch では毎回

```lean
unfold goldenFifthSndFactor
```

して `hterm1`, `hterm4`, `hterm5` を組み立てるため、構文上の反復はある。しかし parity pattern 自体が branch ごとに異なるので、helper 化するとかえって証明の読みやすさを落とす可能性が高い。

数学的には primitive 条件から「少なくとも片方が odd」を先に補題化し、mod-2 polynomial identity

$$
H(r,s)\equiv r+s+rs\pmod2
$$

あるいは同値な Boolean parity 計算へ落とす方法も考えられる。これは短くなる可能性があるが、現行 proof の方が各 monomial の由来を監査しやすい。

## 最適化候補

1. primitive coprime integers に対する「not both even」を再利用補題として抽出すれば、最初の contradiction branch を短縮できる。
2. `goldenFifthSndFactor` の mod-2 正規形を独立 lemma として持てば、今後同じ quartic の parity を再利用する箇所で大幅に短くできる。
3. `simp` / `norm_num` と parity normalization を組み合わせて三 branch を圧縮できる可能性はあるが、成立性と proof robustness は Lean build 禁止条件のため **未検証** である。
4. 現行の明示的 proof は Comparator や監査用途では利点が大きいため、単なる行数削減だけを目的に置換する必要性は低い。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

同ファイルの generated-source manifest では本 theorem は

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

の領域に属する。

本 theorem 本体が直接使う機能は主として、整数・自然数の `Even` / `Odd`、`natAbs`、`Nat.Coprime`、divisibility、冪に対する parity API、および `norm_num`, `omega`, `decide` である。

したがって theorem 単独では `import Mathlib` より狭い import closure にできる可能性が高い。ただし `GoldenZeroSectorCandidate`, `goldenFifthSndFactor` とその upstream 定義を含む project module が必要であり、Mathlib の正確な最小 module 集合は Lean build を行っていないため **未確認** である。

## Comparator challenge 化の可否

**適している。** 0302 より一段高い中級程度の challenge にできる。

入力として

```lean
hrs : Nat.Coprime r.natAbs s.natAbs
```

と quartic `goldenFifthSndFactor r s` の定義を与え、

```lean
Odd (goldenFifthSndFactor r s)
```

を目標とする。

評価点は、

- `Int.even_or_odd` による完全場合分けを構成できるか
- even-even branch を `Nat.Coprime` から排除できるか
- `Even` / `Odd` の積・和・冪 API を正しく接続できるか
- 共通の even monomial を branch 外へ持ち上げて重複を減らせるか
- `ℤ` の parity と `ℕ` の `natAbs` coprimality の型境界を処理できるか

である。

単なる自動算術ではなく、proof decomposition と API 選択の質を比較できるので Comparator 向けの題材として良い。

## PDF との対応

対象 branch の repository tree には

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

GitHub コネクタの通常のテキスト取得は binary PDF 本文を返さないため、この実行では PDF 内の具体的ページ・節番号を直接照合できていない。したがって、本 theorem と PDF の正確な節番号・記述との一対一対応は **未確認** であり、推測によるページ対応は行わない。

Lean コードについては対象 branch の `Flt5DkMath/FLT5StandAlone.lean` にある宣言本体、直前の `five_not_dvd_d`、直後の `d_odd` まで確認した。

## 次に読むべき宣言

次は

```lean
GoldenZeroSectorCandidate.d_odd
```

である。種別は **`theorem`**。

Lean 正本では直後に

```lean
/-- Consequently the tenth-power base `d` is odd. -/
theorem d_odd (p : GoldenZeroSectorCandidate) : Odd p.d := by
  have hH := p.H_odd
  rw [p.H_eq_tenth] at hH
  have hdZ : Odd (p.d : ℤ) :=
    (Int.odd_pow' (by decide : 10 ≠ 0)).mp hH
  exact_mod_cast hdZ
```

と続く。

0303 が factor level で

$$
H(r,s)\text{ odd}
$$

を確定し、0304 は

$$
H(r,s)=d^{10}
$$

を介して

$$
d\text{ odd}
$$

へ降ろす。これは 0301→0302 の five-adic descent と完全に平行な parity descent の後半である。