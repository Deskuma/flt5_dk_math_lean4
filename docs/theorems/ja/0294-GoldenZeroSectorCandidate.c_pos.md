# 0294 — `GoldenZeroSectorCandidate.c_pos`

## 宣言種別

これは **`theorem`** である。

0293 `GoldenZeroSectorCandidate.s_neg` で visible coordinate `s` が厳密に負であることを確定した後、0290 `GoldenZeroSectorCandidate` が保持する

$$
|s|=5^6c^{10}
$$

に対応する `s_natAbs_eq` から、tenth-power base `c` が 0 ではありえないことを示す。

## Lean の型

```lean
namespace GoldenZeroSectorCandidate

/-- The tenth-power base in the visible coordinate is nonzero. -/
theorem c_pos (p : GoldenZeroSectorCandidate) : 0 < p.c := by
  by_contra hc
  have hc0 : p.c = 0 := Nat.eq_zero_of_not_pos hc
  have hsAbsZero : p.s.natAbs = 0 := by
    simpa [hc0] using p.s_natAbs_eq
  have hs0 : p.s = 0 := Int.natAbs_eq_zero.mp hsAbsZero
  have hsneg := p.s_neg
  omega
```

結論は

$$
0<p.c
$$

である。

`p.c : ℕ` なので、これは単に `p.c ≠ 0` より一段強い自然数上の正性の形である。

## 数学的意味

候補 `p` は

$$
|p.s|=5^6p.c^{10}
$$

を保持している。一方 0293 により

$$
p.s<0
$$

なので、とりわけ

$$
p.s\neq0.
$$

もし $p.c=0$ なら

$$
|p.s|=5^6\cdot0^{10}=0
$$

となり、絶対値が 0 なので $p.s=0$ である。これは $p.s<0$ と矛盾する。

したがって

$$
p.c\neq0.
$$

自然数では非零性と正性が一致するため

$$
0<p.c
$$

が従う。

## 証明全体での役割

zero-sector arithmetic で得られた tenth-power split は

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}
$$

という自然数側の形で保存されている。inversion 層では、これらの base `c`, `d` を単なる自然数パラメータではなく **正の tenth-power scale** として扱う必要がある。

0293 は `s` の符号を回復し、本 theorem 0294 はそこから `c` の退化ケースを除く。直後の 0295 `GoldenZeroSectorCandidate.d_pos` は全く対称的に quartic factor 側の base `d` の正性を示す。

したがって 0294–0295 は、absolute-value split に現れた二つの tenth-power base が zero-sector inversion の実際の非退化量であることを保証する小さな gateway theorem の対である。

## 直接依存する定義・補題

### `GoldenZeroSectorCandidate`

0290 の `structure`。本 theorem で直接使う field は

```lean
p.c : ℕ
p.s : ℤ
p.s_natAbs_eq : p.s.natAbs = 5 ^ 6 * p.c ^ 10
```

である。

### `GoldenZeroSectorCandidate.s_neg`

0293 の theorem。

```lean
theorem s_neg (p : GoldenZeroSectorCandidate) : p.s < 0
```

最後に `p.s = 0` を排除するための主要な符号入力である。

### `Nat.eq_zero_of_not_pos`

`by_contra hc` 後の仮定は `¬ 0 < p.c` である。自然数についてこれを

```lean
p.c = 0
```

へ変換する。

### `Int.natAbs_eq_zero`

```lean
p.s.natAbs = 0
```

から

```lean
p.s = 0
```

へ戻す整数絶対値 API である。

### `simpa`

`p.c = 0` を `p.s_natAbs_eq` に代入し、右辺

```lean
5 ^ 6 * 0 ^ 10
```

を 0 に簡約して `p.s.natAbs = 0` を得る。

### `omega`

最後の

```lean
p.s = 0
p.s < 0
```

という線形整数算術上の矛盾を閉じる。

## 証明の流れ

### 1. 正性を否定する

```lean
by_contra hc
```

目標 `0 < p.c` を否定し、`hc : ¬ 0 < p.c` を仮定する。

### 2. 自然数 `c` を 0 に固定する

```lean
have hc0 : p.c = 0 := Nat.eq_zero_of_not_pos hc
```

自然数では正でない値は 0 なので、退化ケースへ落ちる。

### 3. tenth-power split から `|s|=0` を得る

```lean
have hsAbsZero : p.s.natAbs = 0 := by
  simpa [hc0] using p.s_natAbs_eq
```

0290 が保存する

$$
|s|=5^6c^{10}
$$

に $c=0$ を代入するだけである。

### 4. 絶対値 0 から `s=0` を得る

```lean
have hs0 : p.s = 0 := Int.natAbs_eq_zero.mp hsAbsZero
```

ここで自然数絶対値から元の整数へ戻る。

### 5. 0293 の厳密な負性と矛盾させる

```lean
have hsneg := p.s_neg
omega
```

`hs0 : p.s = 0` と `hsneg : p.s < 0` は両立しないので contradiction が閉じる。

## Lean 固有の処理

本証明で重要なのは、`c : ℕ` と `s : ℤ` の二つの数体系を跨ぐことではなく、`natAbs` がその橋になっている点である。

`p.s_natAbs_eq` は既に自然数等式なので `exact_mod_cast` は不要である。`c=0` の rewrite と自然数冪の簡約は `simpa` に任せられる。

また `Int.natAbs_eq_zero.mp` により、絶対値 0 の情報を明示的に整数等式へ戻してから `omega` を使う。このため証明は `ring`, `nlinarith`, `positivity`, `norm_num`, `exact_mod_cast` を必要としない。

## 冗長・重複箇所

### 0295 `d_pos` との構造的重複

直後の 0295 は

- `p.d = 0` を仮定
- `p.H_natAbs_eq` から quartic factor の `natAbs = 0`
- 元の quartic factor を 0 に戻す
- `p.H_pos` と矛盾

というほぼ同型の証明になる。

これは冗長というより、二つの tenth-power base に対して同じ非退化パターンを明示したものと見るべきである。共通補題化は可能だが、この程度の短さでは個別 theorem の方が proof graph を読みやすい。

### `hs0` の明示

`Int.natAbs_eq_zero` と `p.s_neg` を直接組み合わせる短縮形も考えられるが、`hs0 : p.s = 0` を名前付きで保持する現行コードは数学的な矛盾点が明瞭である。

## 最適化候補

1. 自然数の `p.c ≠ 0` を先に示してから `Nat.pos_of_ne_zero` 型の API で正性へ変換する別形が考えられる。ただし現在の `by_contra` + `Nat.eq_zero_of_not_pos` は十分短い。
2. 0294 と 0295 の共通パターンを「`natAbs x = K * n^k` かつ `x ≠ 0` なら `0<n`」という補題へ一般化できる可能性はある。ただし抽象化コストの方が大きい可能性が高い。
3. 最後の `omega` は単純な `p.s = 0` と `p.s < 0` の矛盾だけなので、基本 order lemma で閉じることも可能と思われる。具体的な最短 API は Lean build/API 探索を行っていないため断定しない。

現行証明は意図が明快であり、実用上は十分最適化されている。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。manifest 上、本宣言を含む generated source は

```text
DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean
```

である。

本 theorem 自体が直接利用する機能は主に

- `Nat.eq_zero_of_not_pos`
- `Int.natAbs_eq_zero`
- `simpa`
- `omega`
- `GoldenZeroSectorCandidate.s_neg`

である。

`ring`, `nlinarith`, `positivity`, `norm_num`, `exact_mod_cast` は本 theorem 自体では使わない。

ただし指定に従い Lean build は行っていないため、`import Mathlib` からどの個別 import まで削減できるかは **未検証** である。特に `omega` の import と、前段の candidate 定義群に必要な import を含めた module 全体の最小集合は断定しない。

## Comparator challenge 化の可否

**適している。**

短い theorem だが、次の要素を評価できる。

1. 自然数の非正性から 0 を得る API を見つけられるか。
2. structure field `s_natAbs_eq` を適切に rewrite できるか。
3. `Int.natAbs_eq_zero` で整数へ戻せるか。
4. 既存 theorem `p.s_neg` を依存として発見できるか。
5. 最後の矛盾を Lean の算術 tactic または order API で閉じられるか。

例えば

```lean
theorem challenge (p : GoldenZeroSectorCandidate) : 0 < p.c := by
  ...
```

とし、`s_natAbs_eq` と `s_neg` の利用を許可する形式がよい。

難度は低めだが、`Nat` と `Int.natAbs` の境界処理を含むため教材として価値がある。

## PDF との対応

対象 branch には既存の

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

ただし今回の GitHub コネクタでは PDF binary 本文をテキストとして取得できず、raw PDF の外部取得も成功しなかった。そのため PDF 内の具体的なページ番号、節番号、あるいは本 theorem と完全一致する記述位置は **確認できていない**。ここでは Lean 正本 `Flt5DkMath/FLT5StandAlone.lean` の現行コードを最優先の根拠とし、PDF の具体的内容について推測は行わない。

## 次に読むべき宣言

次は **0295 `GoldenZeroSectorCandidate.d_pos`** である。種別は `theorem`。

```lean
/-- The tenth-power base in the quartic factor is nonzero. -/
theorem d_pos (p : GoldenZeroSectorCandidate) : 0 < p.d := by
  by_contra hd
  have hd0 : p.d = 0 := Nat.eq_zero_of_not_pos hd
  have hHAbsZero : (goldenFifthSndFactor p.r p.s).natAbs = 0 := by
    simpa [hd0] using p.H_natAbs_eq
  have hH0 : goldenFifthSndFactor p.r p.s = 0 :=
    Int.natAbs_eq_zero.mp hHAbsZero
  have hHpos := p.H_pos
  omega
```

0294 が visible coordinate 側の tenth-power base `c` の正性を保証したのに対し、0295 は quartic factor 側の base `d` を同じ方法で非退化にする。これで inversion に必要な二つの tenth-power scale の正性が揃う。