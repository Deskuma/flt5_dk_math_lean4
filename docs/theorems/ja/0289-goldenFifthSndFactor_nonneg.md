# 0289 — `goldenFifthSndFactor_nonneg`

## 宣言種別

これは **`theorem`** である。

黄金整数の 5 乗の第二座標に現れる四次因子 `goldenFifthSndFactor r s` が、任意の整数 `r,s` に対して常に非負であることを示す。

## Lean の型

```lean
/-- The quartic second-coordinate factor is nonnegative for all integer inputs. -/
theorem goldenFifthSndFactor_nonneg (r s : ℤ) :
    0 ≤ goldenFifthSndFactor r s := by
  have hdiag : 0 ≤
      zeroSectorX r s ^ 4 +
        10 * zeroSectorX r s ^ 2 * s ^ 2 +
        5 * s ^ 4 := by
    positivity
  have hident := sixteen_mul_goldenFifthSndFactor_eq r s
  nlinarith
```

数学的には、

$$
H(r,s)=\texttt{goldenFifthSndFactor}(r,s)
$$

と置いたとき、すべての $r,s\in\mathbb Z$ について

$$
H(r,s)\ge 0
$$

を主張する。

正本での定義は

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4.
$$

この形だけを見ると交差項 $2r^3s$ と $3rs^3$ の符号が変わり得るため、非負性は項ごとには明らかではない。そこで直前の 0288 `sixteen_mul_goldenFifthSndFactor_eq` が導いた

$$
16H(r,s)=X^4+10X^2s^2+5s^4,
\qquad X=2r+s
$$

を使う。

右辺はすべて非負項なので、左辺も非負となり、$16>0$ から $H(r,s)\ge 0$ が従う。

## 数学的意味

本 theorem の本質は、符号が見えにくい四次式を 0288 の対角化恒等式を通して **明示的な非負表示** に変換することである。

$$
X^4\ge 0,
\qquad
10X^2s^2\ge 0,
\qquad
5s^4\ge 0
$$

なので、

$$
X^4+10X^2s^2+5s^4\ge 0.
$$

したがって

$$
16H(r,s)\ge 0,
$$

さらに $16>0$ より

$$
H(r,s)\ge 0.
$$

これは単なる計算補題ではなく、後続の zero-sector inversion で `goldenFifthSndFactor` の絶対値や符号を扱う際に、符号の不定性を消す役割を持つ。

## 証明全体での役割

zero-sector arithmetic では先に tenth-power split が得られており、inversion 層では

$$
X=2r+s,
\qquad
U=X^2+5s^2,
\qquad
W=4d^5,
$$

$$
A=U-W,
\qquad
B=U+W,
\qquad
Q=5^5c^8
$$

という量が導入されている。

0288 は元の quartic factor $H(r,s)$ を新座標 $X$ で

$$
16H=X^4+10X^2s^2+5s^4
$$

と書き直した。本 theorem 0289 は、その代数的恒等式を初めて **順序情報** に変換する。

つまり流れは

$$
\text{quartic identity}
\longrightarrow
\text{sum of nonnegative terms}
\longrightarrow
H(r,s)\ge 0
$$

である。

この非負性により、後続で `|H(r,s)| = d^10` のような情報を使う場合にも、必要に応じて絶対値を外して `H(r,s) = d^10` へ進むための基礎が整う。ただし、本 theorem 単独ではその絶対値除去の具体的な後続 lemma までは主張していない。

## 直接依存する定義・補題

### `goldenFifthSndFactor`

対象となる四次式である。

```lean
def goldenFifthSndFactor (r s : ℤ) : ℤ :=
  r ^ 4 + 2 * r ^ 3 * s + 4 * r ^ 2 * s ^ 2 +
    3 * r * s ^ 3 + s ^ 4
```

元の意味は、黄金整数 $(r+s\varphi)^5$ の第二座標に現れる因子 $H(r,s)$ である。

### `zeroSectorX`

0282 で導入された対角座標

```lean
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s
```

である。

### `sixteen_mul_goldenFifthSndFactor_eq`

直前の 0288。

```lean
theorem sixteen_mul_goldenFifthSndFactor_eq (r s : ℤ) :
    16 * goldenFifthSndFactor r s =
      zeroSectorX r s ^ 4 +
        10 * zeroSectorX r s ^ 2 * s ^ 2 +
        5 * s ^ 4 := by
  unfold goldenFifthSndFactor zeroSectorX
  ring
```

本 theorem の数学的核心をすでに代数恒等式として提供している。

### `positivity`

右辺が非負であることを自動判定する Mathlib tactic である。偶数冪の非負性と、非負係数との積・和を処理する。

### `nlinarith`

`hdiag` と `hident` から最終目標 `0 ≤ goldenFifthSndFactor r s` を非線形算術として閉じる Mathlib tactic である。

## 証明の流れ

証明は三段階である。

### 1. 対角化後の右辺の非負性

```lean
have hdiag : 0 ≤
    zeroSectorX r s ^ 4 +
      10 * zeroSectorX r s ^ 2 * s ^ 2 +
      5 * s ^ 4 := by
  positivity
```

`positivity` により、偶数冪と非負係数から右辺全体が非負と分かる。

### 2. 0288 の恒等式を取得

```lean
have hident := sixteen_mul_goldenFifthSndFactor_eq r s
```

これにより

$$
16H(r,s)=X^4+10X^2s^2+5s^4
$$

を局所仮定として得る。

### 3. 非線形算術で結論

```lean
nlinarith
```

`hdiag` と `hident` を合わせると

$$
16H(r,s)\ge 0.
$$

係数 $16$ が正なので `nlinarith` が

$$
H(r,s)\ge 0
$$

を導く。

## Lean 固有の処理

本 theorem の特徴は、直接 `goldenFifthSndFactor` を展開しないことである。

0288 では

```lean
unfold goldenFifthSndFactor zeroSectorX
ring
```

と純粋な環恒等式を証明したが、0289 ではその結果を再利用し、符号判定だけを `positivity` と `nlinarith` に任せる。

この分離により、

- 代数正規化は 0288
- 順序推論は 0289

という責務分担になっている。

`ℤ` 上の theorem なので `Nat`/`Int` coercion、`natAbs`、divisibility、coprimality の処理は現れない。

また `have hident := ...` では型注釈を明示せず、Lean の elaborator が 0288 の具体化された等式型を推論している。

## 冗長・重複箇所

証明本体は短く、実質的な冗長性はほとんどない。

ただし理論上は 0288 を `rw` で使ってから `positivity` だけで閉じる別 proof style も考えられる。例えば「左辺の 16 倍が非負」という中間命題を明示してから、正の定数による割り戻しを行う形である。

現行証明は

```lean
positivity
have hident := ...
nlinarith
```

と役割が明確であり、可読性も高い。

`nlinarith` は本件にはやや強力な tactic だが、恒等式と不等式を一度に組み合わせて処理できるため、コード量との釣り合いは良い。

## 最適化候補

### 1. `nlinarith` の縮小

より限定的な順序 lemma を使って、`16 * H ≥ 0` から `H ≥ 0` を明示的に導くことは可能である。その方が kernel-level の数学的流れは読みやすくなる可能性がある。

一方、現行の `nlinarith` は短く堅牢で、変更する強い理由はない。

### 2. 非負表示を API 化するか

0288 がすでに exact identity を API として提供しているため、本 theorem のためだけに別の「sum-of-squares」補題を置く必要は薄い。

もし今後、右辺の各項の消滅条件から $r=s=0$ のような等号条件を解析するなら、非負性だけでなく

$$
H(r,s)=0 \iff r=0\land s=0
$$

のような positive-definite 性質を別 lemma として追加する余地はある。ただしこれは現行 source から確認できる将来実装ではなく、数学的な最適化候補である。

### 3. `have hident` の型明示

教育用には

```lean
have hident :
    16 * goldenFifthSndFactor r s = ... :=
  sixteen_mul_goldenFifthSndFactor_eq r s
```

と書く方が追いやすいが、実装としては現行の型推論の方が簡潔である。

## 必要 Mathlib import と import 最適化候補

standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem が直接必要とする主な機能は、

- 整数の順序付き可換環構造
- 自然数指数の冪
- `positivity` tactic
- `nlinarith` tactic
- 依存定義 `goldenFifthSndFactor`, `zeroSectorX`
- 0288 `sixteen_mul_goldenFifthSndFactor_eq`

である。

したがって `import Mathlib` は theorem 単独には広い可能性が高い。ただしこの作業では Lean build を行わないため、元 module `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` の実際の最小 import 集合は **未検証** である。具体的な import 削減先は推測で断定しない。

## Comparator challenge 化の可否

**適している。**

0288 より一段だけ推論要素が増え、

1. 偶数冪から右辺の非負性を認識する。
2. 既存の exact identity を利用する。
3. 正の定数倍から元の因子の非負性へ戻す。

という小さく明確な challenge になる。

例えば 0288 を既知 lemma として与え、

```lean
theorem challenge (r s : ℤ) :
    0 ≤ goldenFifthSndFactor r s := by
  ...
```

を完成させる形式が良い。

`positivity` + `nlinarith` の現行解だけでなく、明示的な order lemma を用いた proof と比較できるため Comparator 向け教材として価値がある。

判定は **適する** である。

## PDF との対応

対象 branch の repository tree に

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することは確認した。

ただし GitHub コネクタの通常のテキスト取得では PDF binary 本文を解析可能な形で取得できず、今回の PDF 直接取得も成功しなかった。そのため、本 theorem と PDF の具体的ページ・節番号・文言との対応は **未確認** である。

確認できない位置情報を推測せず、ここでは branch 上の Lean 正本と既存 theorem museum を根拠とする。

## 次に読むべき宣言

次は 0290 `GoldenZeroSectorCandidate` である。種別は **`structure`**。

正本では 0289 の直後に、zero-sector arithmetic receiver から供給される raw hypotheses と chosen tenth-power split をまとめて保持する構造体として導入される。

冒頭は次の通りである。

```lean
structure GoldenZeroSectorCandidate where
  r : ℤ
  s : ℤ
  ...
```

0282–0289 が inversion に必要な座標・恒等式・非負性という汎用部品を用意したのに対し、0290 からは実際の zero-sector candidate のデータを一つの構造体へ束ね、そのフィールドを用いた factorization 証明へ進む。

したがって依存順では、0289 で quartic factor の符号制御を確立した後、0290 で inversion の入力データ構造を確定する流れになる。