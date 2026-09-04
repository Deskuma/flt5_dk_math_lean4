# 0256 — `goldenFifthSndPoly`

## Lean の型

```lean
/-- Second-coordinate polynomial of `(p + q*phi)^5`. -/
def goldenFifthSndPoly (p q : ℤ) : ℤ :=
  5 * q * (p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 +
    3 * p * q ^ 3 + q ^ 4)
```

これは `theorem` ではなく `def` であり、黄金整数

$$
\gamma=p+q\varphi
$$

の第五冪を `1,φ` 基底へ展開したときの第二座標を与える整数係数多項式を名前付き API として定義する。

## 数学的主張・宣言の意味

黄金整数では

$$
\varphi^2=\varphi+1
$$

なので、第五冪は

$$
(p+q\varphi)^5=A(p,q)+B(p,q)\varphi
$$

と一意に書ける。0255 `goldenFifthFstPoly` が第一座標 $A(p,q)$ を定義したのに対し、本定義は第二座標

$$
B(p,q)
=5q\left(p^4+2p^3q+4p^2q^2+3pq^3+q^4\right)
$$

を定義する。

最も重要なのは、第二座標が定義の段階で明示的に

$$
5q
$$

を因子として持つ点である。したがって任意の黄金整数の第五冪では、第二座標は必ず `5` で割れる。

これは単なる展開式ではなく、後続の five-adic sector arithmetic で使う可視な 5-進構造を、そのまま構文上に露出した定義である。

## 証明全体での役割

0255–以降の `GoldenFifthPowerCoordinates.lean` は、unit × fifth-power 形

$$
\beta=\varepsilon\gamma^5
$$

を具体的な座標合同へ落とすための module である。

本定義はその中で第二座標側の中心量を担う。正本 source では直後に

```lean
theorem goldenPow_five_snd (gamma : GoldenInt) :
    (goldenPow gamma 5).snd =
      goldenFifthSndPoly gamma.fst gamma.snd := by
  simp [goldenPow, goldenMul, goldenOne, goldenFifthSndPoly]
  ring
```

が置かれ、実際の `goldenPow gamma 5` の第二座標と本多項式が接続される。

さらに後続では

```lean
theorem five_dvd_goldenFifthSndPoly (r s : ℤ) :
    (5 : ℤ) ∣ goldenFifthSndPoly r s := by
  ...
```

が証明され、unit sector ごとの第二座標式と組み合わせて、非零 sector が要求する 5-進条件を排除する材料になる。

また後続では quartic factor

$$
H(r,s)=r^4+2r^3s+4r^2s^2+3rs^3+s^4
$$

を `goldenFifthSndFactor` として切り出し、

$$
goldenFifthSndPoly(r,s)=5s\,H(r,s)
$$

という形へ再整理する。この factorization は最終的な zero-sector descent にも使われる。

## 直接依存する定義・補題

本宣言は `def` なので proof script はなく、直接依存は基本的な整数演算だけである。

- `ℤ`
- 加法・乗法
- 自然数冪 `^`

概念的には 0255 `goldenFifthFstPoly` と対になる座標定義であり、数学的背景としては次を利用する。

- `GoldenInt`
- `goldenPow`
- `goldenMul`
- 0165 `golden_phi_sq`
- `φ² = φ + 1`

ただしこれらは本 `def` の Lean 定義本文には直接現れない。実際の第五冪座標との一致は次の `goldenPow_five_snd` が証明する。

## 構築の流れ

この定義は、第五冪展開後に `φ²=φ+1` を反復して `1,φ` 基底へ還元した第二座標を、さらに 5 と `q` を括り出した形で固定する。

展開前のイメージは

$$
(p+q\varphi)^5
$$

であり、還元後の第二座標は

$$
5p^4q+10p^3q^2+20p^2q^3+15pq^4+5q^5.
$$

これを因数分解すると

$$
5q\left(p^4+2p^3q+4p^2q^2+3pq^3+q^4\right)
$$

となる。現行定義は最初から後者を採用することで、five-adic 情報を可視化している。

## Lean 固有の処理

本宣言自体には tactic はない。

```lean
def goldenFifthSndPoly (p q : ℤ) : ℤ := ...
```

という純粋な整数多項式定義なので、評価は通常の `ring` / `norm_num` / `simp` によって扱える。

後続の `goldenPow_five_snd` では、`goldenPow` と `goldenMul` を展開してから `ring` により多項式同一性を閉じる。したがって本定義は、複雑な raw coordinate 展開を一つの名前へ畳み込み、downstream の rewrite surface を小さくする役割を持つ。

また `5 * q * (...)` という構文上の因子化により、後続の整除証明では大規模な `ring_nf` を行わずに `5 ∣ ...` の witness を構成しやすい。

## 冗長・重複箇所

0255 `goldenFifthFstPoly` と本定義は、同じ第五冪座標展開の二成分を別々の scalar function として保持している。

理論上は、例えば

```lean
def goldenFifthCoords (p q : ℤ) : ℤ × ℤ :=
  (goldenFifthFstPoly p q, goldenFifthSndPoly p q)
```

のように pair として束ねる設計も可能である。

一方、現行の分離には利点がある。

- 第一座標と第二座標では five-adic 性質が大きく異なる。
- 第二座標では `5*q` 因子を直接参照したい。
- unit sector ごとの式では `A` と `B` を異なる係数で組み合わせる。
- scalar theorem の方が rewrite しやすい。

したがって API-level の重複はあるが、downstream arithmetic の用途を考えると合理的な分離である。

## 最適化候補

1. **第一・第二座標を pair 定義へ束ねる**
   - 0255/0256 の共通 derivation を一つの theorem にまとめられる可能性がある。

2. **`goldenFifthSndFactor` を先に定義する**
   - 現行 source では後段で quartic factor を再度切り出して

$$
goldenFifthSndPoly(r,s)=5s\,goldenFifthSndFactor(r,s)
$$

を証明する。
   - 先に quartic を定義して、本宣言を `5 * q * goldenFifthSndFactor p q` と定義すれば重複を減らせる。

3. **一般指数の座標 recurrence を導入する**
   - `φ²=φ+1` から `(p+qφ)^n` の二座標を recurrence で生成し、`n=5` を特殊化する設計も可能。
   - ただし FLT5 専用実装としては現行の明示多項式の方が監査しやすい。

4. **標準 polynomial API へ持ち上げる**
   - `MvPolynomial` 等で第五冪展開を表現する案もあるが、現行 downstream は整数算術中心なので過剰抽象化になりうる。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本定義単独が必要とする表面は非常に小さく、実質的には整数型と基本 ring / power notation のみである。したがって `Mathlib` 全体よりかなり狭い import で足りる可能性が高い。

ただし同一 module の直後では `ring`、整除、有限 unit sector の case split 等が使われるため、module 全体の最小 import は本 `def` 単独より広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。特に次の比較が有効である。

- A: 現行の明示 factorized polynomial
- B: 展開形 `5p^4q + 10p^3q² + ...`
- C: `goldenFifthSndFactor` を先に定義して `5*q*H` とする設計
- D: 第一・第二座標を pair で一括定義
- E: `goldenPow` を直接展開し、named polynomial を置かない設計

比較軸は、proof 長、`5 ∣ snd` 証明の容易さ、rewrite usability、式の監査性、重複量、下流 sector arithmetic の読みやすさである。

特に A と B の比較は、数学的には同値でも「5-adic 因子を構文上で可視化すること」が formal proof にどれだけ効くかを測るよい課題になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenFifthPowerCoordinates.lean` generated section である。

source では 0255 `goldenFifthFstPoly` の直後に本定義があり、続いて `goldenPow_five_fst`、`goldenPow_five_snd` が置かれている。

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし本 `def` に対応する具体的な PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0257 `goldenPow_five_fst`** である。

```lean
theorem goldenPow_five_fst (gamma : GoldenInt) :
    (goldenPow gamma 5).fst =
      goldenFifthFstPoly gamma.fst gamma.snd := by
  simp [goldenPow, goldenMul, goldenOne, goldenFifthFstPoly]
  ring
```

0255・0256 で第五冪の二つの座標多項式を定義したので、0257 からはそれらが実際の `goldenPow gamma 5` の座標と一致することを証明する段階へ進む。