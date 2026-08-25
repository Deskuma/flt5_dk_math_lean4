# 0222 — `goldenQuotient_zero`

## Lean の型

```lean
theorem goldenQuotient_zero (x : GoldenInt) :
    goldenQuotient x 0 = 0 := by
  ext <;> simp [goldenQuotient, goldenQuotientCoords,
    goldenQuotientNumerator, goldenConj, goldenMul, goldenNorm]
```

これは `theorem` であり、0220 `goldenQuotient` で定義した全域 quotient が、divisor を `0` とした場合には黄金整数 `0` を返すことを保証する。

## 数学的主張・宣言の意味

通常の Euclidean division では除数 `0` に数学的な商は存在しない。しかし Lean / Mathlib の `EuclideanDomain` が要求する quotient operation は全域関数なので、`goldenQuotient x 0` にも何らかの値を与える必要がある。

本実装では、その特殊値を

$$
goldenQuotient(x,0)=0
$$

とする。

これは 0219 `goldenQuotientCoords` と 0220 `goldenQuotient` の定義から自然に出る。`y=0` なら、

$$
\overline{0}=0,
$$

したがって

$$
x\overline{0}=0,
$$

さらに

$$
N(0)=0.
$$

`goldenQuotientCoords x 0` の各座標は Lean の有理数除算では `0 / 0` となるが、`ℚ` の除算は全域化されており `0⁻¹=0` なので `0 / 0 = 0` へ簡約される。最後に `round 0 = 0` だから、丸めた黄金整数 quotient も `0` になる。

重要なのは、これは「数学的に 0 で割った商が 0 である」と主張しているのではなく、**全域な Euclidean-domain API の zero-divisor branch を 0 に固定する仕様 theorem** だという点である。

## 証明全体での役割

`GoldenEuclidean.lean` は、黄金整数環を norm-Euclidean domain として構築するため、具体的な quotient / remainder algorithm を Mathlib の `EuclideanDomain` structure に登録する。

0220–0222 の流れは次の通りである。

1. 0219 `goldenQuotientCoords` で rational quotient coordinates を構成する。
2. 0220 `goldenQuotient` で各座標を最近接整数へ丸め、離散 quotient を得る。
3. 0221 `goldenRemainder` で

$$
r=x-qy
$$

を定義する。
4. **0222 `goldenQuotient_zero` で divisor `0` の quotient 仕様を確定する。**
5. 後続の division identity と strict remainder decrease を証明する。
6. 最終 `goldenEuclideanDomain` instance の

```lean
quotient_zero := goldenQuotient_zero
```

に本 theorem をそのまま登録する。

したがって 0222 は、Euclidean norm の収縮を証明する theorem ではなく、**全域 quotient operation が Mathlib の structure law を満たすための境界条件** を担う。

## 直接依存する定義・補題

直接依存する主な定義は次の通りである。

- `GoldenInt`
- 0220 `goldenQuotient`
- 0219 `goldenQuotientCoords`
- 0216 `goldenQuotientNumerator`
- 0163 `goldenConj`
- 0124 `goldenMul`
- 0164 `goldenNorm`
- `GoldenInt.ext` および projection simp API
- `round` の `0` に対する simp rule
- `ℚ` の全域除算に関する simp rule

本 theorem は、非零 divisor に対する 0215 `goldenNorm_ne_zero_of_ne_zero` を必要としない。むしろ `y=0` の branch を扱うため、分母非零性を仮定せず定義をそのまま展開する。

概念的には

$$
y=0
\Longrightarrow
x\overline y=0
\Longrightarrow
goldenQuotientCoords(x,y)=(0,0)
\Longrightarrow
round(0,0)=(0,0)
\Longrightarrow
goldenQuotient(x,0)=0
$$

という流れである。

## 証明の流れ

proof は一行の tactic pipeline である。

```lean
by
  ext <;> simp [goldenQuotient, goldenQuotientCoords,
    goldenQuotientNumerator, goldenConj, goldenMul, goldenNorm]
```

### 1. `ext` で黄金整数の二座標へ分解する

目標

```lean
goldenQuotient x 0 = 0
```

を `GoldenInt.ext` により第一座標と第二座標の二つの等式へ落とす。

### 2. quotient stack を一括展開する

`simp` の展開集合に、

- `goldenQuotient`
- `goldenQuotientCoords`
- `goldenQuotientNumerator`
- `goldenConj`
- `goldenMul`
- `goldenNorm`

を与えることで、`y=0` の計算を最下層まで押し下げる。

### 3. `0 / 0` と `round 0` を simp に処理させる

Lean の `ℚ` は field の全域 inverse を持つので `0⁻¹=0`、従って `0/0=0` になる。さらに `round 0=0` が適用され、両座標が整数 `0` に閉じる。

座標展開後に `ring` や `field_simp` は不要である。zero branch は純粋な simplification だけで完了する。

## Lean 固有の処理

### 1. division by zero は proposition-level error ではない

Lean の field division は total function である。したがって

```lean
(goldenQuotientNumerator x 0).fst / goldenNorm 0
```

のような式も型付き項として普通に存在する。

ここで `0 / 0 = 0` になるのは、数学的な partial division の意味付けではなく、`Inv.inv 0 = 0` を採用する algebraic API の結果である。

### 2. `ext` が quotient 実装の透明性を利用する

`goldenQuotient` は `GoldenInt` の structure literal として二つの `round` 値を格納する。したがって全体の等式を直接扱うより、`ext` で座標ごとに見る方が simp が働きやすい。

### 3. zero branch では nonzero certificate が不要

非零 divisor の quotient identities では 0215

```lean
goldenNorm_ne_zero_of_ne_zero
```

が `field_simp` 等の分母非零条件に使われる。しかし 0222 は正反対の branch を扱い、total division の仕様をそのまま利用するので、その theorem は依存しない。

### 4. theorem は implementation-sensitive である

もし `goldenQuotient` を

```lean
if y = 0 then 0 else ...
```

と明示的に定義すれば、本 theorem は `simp [goldenQuotient]` に近い形になる。一方、現行実装は rational quotient の totality から zero law を結果として得ている。

## 冗長・重複箇所

現行 proof は quotient stack をかなり深く展開する。

```lean
simp [goldenQuotient, goldenQuotientCoords,
  goldenQuotientNumerator, goldenConj, goldenMul, goldenNorm]
```

これは local proof としては短いが、0222 が `goldenQuotientCoords x 0 = (0,0)` という中間事実を直接必要としていることを隠している。

もし今後 zero-divisor branch の補題が増えるなら、例えば

```lean
theorem goldenQuotientCoords_zero (x : GoldenInt) :
    goldenQuotientCoords x 0 = (0, 0) := ...
```

を置き、0222 をその consequence とする方が API layering は明瞭になる可能性がある。

一方、この中間 theorem が 0222 以外で使われないなら、現行の一括 `simp` は十分合理的である。

## 最適化候補

1. **zero branch を `goldenQuotient` 定義に明示する**

```lean
def goldenQuotient (x y : GoldenInt) : GoldenInt :=
  if y = 0 then 0 else
    ⟨round ..., round ...⟩
```

とすれば zero law は直接的になる。ただし非零 branch の downstream proof に `if` 展開が増える可能性がある。

2. **`goldenQuotientCoords_zero` を補助 theorem として切り出す**

zero-coordinate calculation と rounding calculation を分離できる。

3. **現在の deep `simp` proof を維持する**

局所的には最短で、追加 API も不要。zero branch が一箇所だけなら最も軽量である。

4. **quotient implementation の標準 algebra notation 化**

raw `goldenMul` / `goldenConj` 展開を減らし、より bundle 化された ring API へ寄せることで simp surface を縮められる可能性がある。

5. **Euclidean division の zero policy を一般 helper として抽象化する**

quadratic-order 一般化を行う場合、total rational quotient + rounding から quotient-zero law を得る pattern は再利用できる。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem が直接利用する Mathlib surface は主に、

- extensionality tactic `ext`
- simplifier `simp`
- rational division / inverse の simp rules
- integer/rational rounding `round`
- product / structure projection

である。

`ring`、`field_simp`、`nlinarith` は本 theorem 自体では不要である。

ただし `GoldenEuclidean.lean` 全体では最近接整数、非線形 inequality、分母 clearing、Euclidean-domain hierarchy まで広く利用するため、module 全体の最小 import はかなり広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 deep `ext <;> simp [...]`
- B: `goldenQuotientCoords_zero` を経由する layered proof
- C: `goldenQuotient` 自体に `if y = 0 then 0` を持たせる実装
- D: quotient / remainder を bundle し zero specification も certificate として保持する設計
- E: 一般 quadratic-order Euclidean quotient framework の zero law を再利用する設計

比較軸は、

- proof term / source 行数
- simp 展開の深さ
- implementation change への頑健性
- zero branch と nonzero branch の proof burden
- EuclideanDomain instance への接続の自然さ
- 一般化可能性

である。

特に A と C は、「total field division の既定値を利用する設計」と「domain-level で zero policy を明示する設計」の違いを測る小さく明瞭な Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenEuclidean.lean` generated section である。

今回 GitHub code search は一時的に upstream 502 を返したため、0222 の Lean 型と proof は、同じ branch の直前正本文書 0221 `goldenRemainder` に記録された source 順・完全な theorem 抜粋でも照合した。0221 日英文書は一致しており、0222 日英ファイルが双方とも未作成であることも GitHub で確認済みである。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。今回も本 theorem に対応する具体的 PDF ページ・節番号は特定していないため推測しない。

## 次に読むべき宣言

依存順の次は、quotient と remainder の Euclidean identity を与える **0223 `golden_quotient_mul_add_remainder`** である。

0221 の正本文書では、後続 source が

$$
yq+r=x
$$

という identity を証明し、その theorem を最終 `EuclideanDomain` instance の `quotient_mul_add_remainder_eq` field に登録することが確認できる。

0222 が divisor `0` の境界仕様を閉じたので、0223 では一般の `x,y` に対して、0221 の定義

$$
r=x-qy
$$

を標準的な Euclidean division equation へ組み直す段階に進む。
