# 0264 — `golden_unit_zero_mul_fifth_snd`

## 宣言種別

これは `theorem` である。

## Lean の型

```lean
theorem golden_unit_zero_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 0) (goldenPow gamma 5)).snd =
      goldenFifthSndPoly gamma.fst gamma.snd := by
  rw [goldenPhi_pow_zero]
  simp only [goldenMul]
  rw [goldenPow_five_snd]
  ring
```

## 数学的主張

`GoldenInt` の元を

$$
\gamma=p+q\varphi
$$

と書く。零 sector の代表 unit は

$$
\varphi^0=1
$$

であるから、

$$
\varphi^0\gamma^5=\gamma^5.
$$

0256 `goldenFifthSndPoly` と 0258 `goldenPow_five_snd` により、第五冪の第二座標は

$$
B(p,q)
=5q\left(p^4+2p^3q+4p^2q^2+3pq^3+q^4\right)
$$

である。したがって本 theorem は

$$
\operatorname{snd}(\varphi^0\gamma^5)=B(p,q)
$$

を Lean の具体的な座標演算として確立している。

ここでいう「sector」は幾何学的な角領域ではなく、unit を fifth power で割った剰余類を表す代数的 sector である。零 sector は代表元 $1=\varphi^0$ に対応する。

## 証明全体での役割

0259–0263 では

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

の五つの unit representative を具体座標へ落とした。本 theorem からは、それらを実際に `gamma^5` に掛けたときの第二座標を明示する段階へ移る。

零 sector はその最初であり、代表が $1$ なので混合は起こらない。そのため、第二座標はそのまま `goldenFifthSndPoly` になる。後続の sector 1–4 では第一座標 `goldenFifthFstPoly` と第二座標 `goldenFifthSndPoly` の線形結合が現れる。

したがって本 theorem は、

1. unit-class representative の具体座標化
2. fifth-power coordinate polynomial
3. finite sector arithmetic

を接続する最初の bridge である。

## 直接依存する定義・補題

直接の証明スクリプトで使われるものは次である。

- `goldenPhi_pow_zero`
  - `goldenPow goldenPhi 0 = ⟨1, 0⟩`。
  - 零 sector の representative を具体座標へ rewrite する。
- `goldenMul`
  - `GoldenInt` の座標乗法。
  - `simp only [goldenMul]` により積の第二座標を展開する。
- `goldenPow_five_snd`
  - `(goldenPow gamma 5).snd = goldenFifthSndPoly gamma.fst gamma.snd`。
  - raw fifth power の第二座標を named polynomial へ置換する。
- `goldenFifthSndPoly`
  - 第五冪の第二座標多項式。

間接的には `GoldenInt`, `goldenPhi`, `goldenPow` の各定義に依存する。

## 証明の流れ

証明は四段階である。

```lean
rw [goldenPhi_pow_zero]
```

により

```lean
goldenPow goldenPhi 0
```

を `⟨1, 0⟩` に置き換える。

次に

```lean
simp only [goldenMul]
```

で黄金整数の乗法を座標へ展開する。左因子が `⟨1,0⟩` なので、第二座標は右因子 `goldenPow gamma 5` の第二座標へ簡約される。

続いて

```lean
rw [goldenPow_five_snd]
```

でその第二座標を `goldenFifthSndPoly gamma.fst gamma.snd` に rewrite する。

最後の

```lean
ring
```

は展開後に残った整数環上の自明な多項式等式を正規化して閉じる。

## Lean 固有の処理

数学的には $1\cdot\gamma^5=\gamma^5$ だけであるが、Lean では `GoldenInt` が直接座標モデルとして実装されているため、ring multiplication の抽象 API ではなく `goldenMul` の座標式を明示的に展開している。

`rw [goldenPhi_pow_zero]` は definitional reduction に任せず、0259 で用意した named theorem を API として利用している。これにより downstream proof が `goldenPow` の再帰定義に直接依存しない。

また `simp only [goldenMul]` として simplifier の使用範囲を限定しており、無関係な simp lemma に proof が依存することを避けている。

## 冗長・重複箇所

数学的には `ring` はかなり強い。`goldenPhi_pow_zero` を rewrite して `goldenMul` を展開した後、第二座標は本質的に恒等写像なので、より局所的な simplification だけで閉じられる可能性がある。

また後続の

- `golden_unit_one_mul_fifth_snd`
- `golden_unit_two_mul_fifth_snd`
- `golden_unit_three_mul_fifth_snd`
- `golden_unit_four_mul_fifth_snd`

も同じ「representative を rewrite → `goldenMul` 展開 → fifth-power coordinates を rewrite → `ring`」という形を共有する。五本を個別 theorem として持つことは downstream の可読性には有利だが、証明実装としては一定の重複がある。

## 最適化候補

最も自然な最適化候補は、unit representative `⟨a,b⟩` と fifth-power coordinates `A,B` に対して

$$
\operatorname{snd}((a+b\varphi)(A+B\varphi))=bA+(a+b)B
$$

という一般 lemma を一つ用意することである。

すると sector 0–4 は representative の座標を代入するだけになり、現在の五本の proof の重複を減らせる。

ただし、現行の個別 theorem は「各 sector の最終形がその場で見える」という長所がある。したがって、一般 lemma を内部 helper とし、公開 API として五本を残す構成が最も読みやすい可能性が高い。

零 sector だけなら、`ring` をより弱い `simp` / `rfl` 系で置き換えられる可能性もある。ただし本作業では Lean build を行っていないため、実際に成立する最小 proof は未確認である。

## 必要 Mathlib import と import 最適化候補

確認できた standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

したがって、この環境で本 theorem に必要な tactic・整数環 machinery が利用可能であることはリポジトリ上で確認できる。

一方、この theorem 単体についての最小 Mathlib import 集合は確認できていない。少なくとも `ring` tactic、整数演算、構造体・rewrite/simp が必要になるが、どの細分化 import まで削減できるかは build を伴う検証が必要である。本タスクでは Lean build を行わないため、特定の最小 import を断定しない。

import 最適化を行うなら、元 module `GoldenFifthPowerCoordinates.lean` の直接 import と、`ring` を供給する Mathlib module を基準に縮小テストするのが妥当である。

## Comparator challenge 化の可否

可能である。難度は低い。

challenge としては、0255–0259 および `goldenMul` を与え、次を証明させる形が適している。

```lean
theorem golden_unit_zero_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 0) (goldenPow gamma 5)).snd =
      goldenFifthSndPoly gamma.fst gamma.snd := by
  ...
```

評価点は、

- `goldenPhi_pow_zero` を使って representative を具体化できるか
- `goldenPow_five_snd` を再利用し raw expansion を避けられるか
- unnecessary unfolding をせず既存 API を使えるか

である。

ただし数学的発見を要求する challenge というより、Lean API の利用と proof refactoring を評価する小問に向いている。

## PDF との対応

対象ブランチには

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

ただし今回の実行環境では PDF 本文を直接取得して 0264 に対応する具体的ページ・節番号を確定できなかった。そのため PDF 内の対応ページについては推測しない。

## 次に読むべき宣言

次は `golden_unit_one_mul_fifth_snd` である。

```lean
theorem golden_unit_one_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 1) (goldenPow gamma 5)).snd =
      goldenFifthFstPoly gamma.fst gamma.snd +
        goldenFifthSndPoly gamma.fst gamma.snd := by
  rw [goldenPhi_pow_one]
  simp only [goldenMul]
  rw [goldenPow_five_fst, goldenPow_five_snd]
  ring
```

零 sector では第二座標 $B$ がそのまま残ったが、sector 1 では代表 $\varphi$ を掛けるため第一座標 $A$ と第二座標 $B$ が混ざり、

$$
\operatorname{snd}(\varphi\gamma^5)=A+B
$$

となる。ここから五つの sector に固有の線形結合が順番に現れる。