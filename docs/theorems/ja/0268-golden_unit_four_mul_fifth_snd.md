# 0268 — `golden_unit_four_mul_fifth_snd`

## 宣言種別

これは `theorem` である。

## Lean の型

```lean
theorem golden_unit_four_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 4) (goldenPow gamma 5)).snd =
      3 * goldenFifthFstPoly gamma.fst gamma.snd +
        5 * goldenFifthSndPoly gamma.fst gamma.snd := by
  rw [goldenPhi_pow_four]
  simp only [goldenMul]
  rw [goldenPow_five_fst, goldenPow_five_snd]
  ring
```

型としては、任意の `gamma : GoldenInt` に対して、sector 4 の代表 `goldenPow goldenPhi 4` を `gamma` の第五冪に掛けたとき、その積の第二座標が二つの第五冪座標多項式の特定の線形結合に等しいことを主張している。

## 数学的主張

`GoldenInt` の元を

$$
\gamma=p+q\varphi
$$

と書き、その第五冪を

$$
\gamma^5=A(p,q)+B(p,q)\varphi
$$

とする。ここで

$$
A(p,q)=p^5+10p^3q^2+10p^2q^3+10pq^4+3q^5
$$

および

$$
B(p,q)=5q\left(p^4+2p^3q+4p^2q^2+3pq^3+q^4\right)
$$

である。

0263 `goldenPhi_pow_four` により sector 4 の代表 unit は

$$
\varphi^4=2+3\varphi,
$$

すなわち `GoldenInt` 座標では `⟨2,3⟩` である。したがって

$$
\varphi^4\gamma^5=(2+3\varphi)(A+B\varphi).
$$

黄金比の関係 $\varphi^2=\varphi+1$ を用いると、

$$
(2+3\varphi)(A+B\varphi)
=(2A+3B)+(3A+5B)\varphi.
$$

よって第二座標は

$$
\operatorname{snd}(\varphi^4\gamma^5)=3A(p,q)+5B(p,q)
$$

となる。本 theorem はこの sector 4 の座標変換を Lean の `GoldenInt` 乗法として固定する。

## 証明全体での役割

0264–0268 は unit representatives

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

を第五冪に掛けたときの第二座標を明示する一連の sector arithmetic であり、本 theorem が最後の sector 4 を担当する。これにより第二座標表

$$
B,\quad A+B,\quad A+2B,\quad 2A+3B,\quad 3A+5B
$$

が完成する。

後続の `signedGolden_nonzero_unitSector_false` では本 theorem が直接 rewrite に用いられる。packet 側から積の第二座標が $5$ で割り切れるため、sector 4 では

$$
5\mid 3A+5B
$$

が得られる。$5B$ は明らかに $5$ の倍数なので、差を取れば

$$
5\mid 3A
$$

となる。$5$ は素数で $5\nmid3$ だから

$$
5\mid A
$$

を得る。これを `five_dvd_goldenNorm_of_five_dvd_fifthFst` に渡すと

$$
5\mid\operatorname{Norm}(\gamma)
$$

となり、packet invariant `five_not_dvd_gamma_norm` と矛盾する。

したがって本 theorem は五 sector の座標表を完成させるだけでなく、sector 4 を modulo-five argument によって排除するための直接入力である。

## 直接依存する定義・補題

証明スクリプトで直接使われるものは次である。

- `goldenPhi_pow_four`
  - `goldenPow goldenPhi 4 = ⟨2, 3⟩`。
  - sector 4 の代表 $\varphi^4$ を具体座標へ rewrite する。
- `goldenMul`
  - `GoldenInt` の座標乗法。
  - `simp only [goldenMul]` により積の第二座標を整数式へ展開する。
- `goldenPow_five_fst`
  - `(goldenPow gamma 5).fst = goldenFifthFstPoly gamma.fst gamma.snd`。
  - 第五冪の第一座標を $A$ に置き換える。
- `goldenPow_five_snd`
  - `(goldenPow gamma 5).snd = goldenFifthSndPoly gamma.fst gamma.snd`。
  - 第五冪の第二座標を $B$ に置き換える。
- `goldenFifthFstPoly`, `goldenFifthSndPoly`
  - 第五冪の二座標を与える named polynomial。

間接的には `GoldenInt`, `goldenPhi`, `goldenPow` と、黄金整数乗法に組み込まれた $\varphi^2=\varphi+1$ の関係に依存する。

## 証明または構築の流れ

最初に

```lean
rw [goldenPhi_pow_four]
```

で `goldenPow goldenPhi 4` を `⟨2,3⟩` に置き換える。

次に

```lean
simp only [goldenMul]
```

で黄金整数の積を座標演算へ展開する。右因子を `⟨A,B⟩` と見れば、左因子 `⟨2,3⟩` による第二座標は $3A+5B$ となる。

続いて

```lean
rw [goldenPow_five_fst, goldenPow_five_snd]
```

で `gamma^5` の生の二座標を `goldenFifthFstPoly` と `goldenFifthSndPoly` に置換する。

最後に

```lean
ring
```

で整数環上の残った多項式恒等式を正規化して証明を閉じる。

## Lean 固有の処理

数学的な核は $(2+3\varphi)(A+B\varphi)$ の展開だけである。しかし Lean では unit representative、黄金整数の乗法、第五冪の座標がそれぞれ named API になっているため、proof はそれらを順に concrete arithmetic へ落とす構成になっている。

`simp only [goldenMul]` は simplifier を `goldenMul` の展開だけに限定しており、グローバルな simp set に偶然依存しない。`ring` は最後の可換環恒等式だけを担当する。

sector 4 では結果の第二座標が $3A+5B$ なので、第一座標と第二座標の両方を参照するため `goldenPow_five_fst` と `goldenPow_five_snd` の双方が必要である。

## 冗長・重複箇所

0264–0268 はほぼ同一の proof skeleton を繰り返している。

1. `goldenPhi_pow_*` で unit representative を具体化する。
2. `goldenMul` を展開する。
3. `goldenPow_five_fst` / `goldenPow_five_snd` で第五冪座標を named polynomial にする。
4. `ring` で閉じる。

これはコード上の重複である。ただし各 sector の右辺を独立 theorem として持つことで、後続の divisibility proof が `rw [golden_unit_four_mul_fifth_snd]` のように直接読める利点がある。

さらに downstream の sector 4 分岐では `hS : 5 ∣ B` を使って $5\mid5B$ を示しているが、$5B$ は係数そのものが 5 なので、数学的には `hS` を使わなくても $5\mid5B$ は自明である。これは本 theorem の冗長性ではなく、後続 proof に残る小さな最適化余地である。

本 theorem 自体の最後の `ring` も、展開後の式が単純であるためより弱い正規化で閉じる可能性がある。ただし本作業では Lean build を行わないため、その置換可能性は確認していない。

## 最適化候補

最も自然なのは、任意の黄金整数 `x=⟨a,b⟩`, `y=⟨A,B⟩` に対して積の第二座標を

$$
bA+(a+b)B
$$

と与える一般 lemma を用意することである。概念的には

```lean
lemma goldenMul_snd_formula (x y : GoldenInt) :
    (goldenMul x y).snd =
      x.snd * y.fst + (x.fst + x.snd) * y.snd := by
  ...
```

のような helper があれば、五つの sector theorem は representative の座標を代入するだけで導ける。

また `goldenPow_five_fst` と `goldenPow_five_snd` を pair equality としてまとめる helper があれば、第五冪座標を一度に rewrite できる。一方、現行の座標別 theorem は downstream で片方だけを使いたい場合に便利なので、一般 helper を追加しても公開 API として現在の theorem 群を残す価値はある。

sector 4 の downstream proof では $5B$ の可除性に `hS : 5 ∣ B` を要求しない形へ簡略化する候補もある。ただし具体的にどの Mathlib lemma が最も簡潔かは未検証である。

## 必要 Mathlib import と import 最適化候補

確認できた正本 standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem の proof には整数環上の演算、`rw` / `simp only`、および `ring` tactic が必要である。`GoldenInt`, `goldenMul`, `goldenPow`, `goldenPhi` と各 coordinate theorem はプロジェクト側の定義・補題であり、Mathlib 単体の import だけでは本 theorem は独立しない。

最小 Mathlib import 集合は確認していない。import 最適化の候補は、整数代数を供給する module と `ring` tactic を供給する tactic module まで縮小することであるが、正確な最小 import path は Lean build で検証する必要がある。本タスクでは Lean build を行わないため断定しない。

## Comparator challenge 化の可否

可能である。難度は低〜中程度である。

```lean
theorem golden_unit_four_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 4) (goldenPow gamma 5)).snd =
      3 * goldenFifthFstPoly gamma.fst gamma.snd +
        5 * goldenFifthSndPoly gamma.fst gamma.snd := by
  ...
```

という goal を与え、既存 API をどれだけ再利用して短く安定した proof を構成できるかを比較できる。評価点は `goldenPhi_pow_four` による representative の具体化、`goldenMul` の第二座標の正しい読取り、第五冪を定義から再計算せず `goldenPow_five_fst` / `goldenPow_five_snd` を利用できるか、である。

より良い発展 challenge は、五 sector を個別に証明するのではなく一般 `goldenMul_snd_formula` を先に証明し、そこから 0264–0268 を系として導出する構成である。これなら単なる `ring` の競争ではなく API 設計と証明再利用も比較できる。

## PDF との対応

対象ブランチには

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

この実行では GitHub 上の PDF バイナリ本文を解析可能な形で取得できなかったため、0268 に対応する具体的ページ・節番号、PDF 内の表現との一対一対応は確認できていない。したがって PDF 内容については推測せず、本稿の技術的説明はリポジトリ上の Lean 正本と、PDF ファイルの存在確認を根拠としている。

## 次に読むべき宣言

次は `golden_neg_unit_mul_fifth_snd` である。

```lean
theorem golden_neg_unit_mul_fifth_snd (epsilon gamma : GoldenInt) :
    (goldenMul (-epsilon) (goldenPow gamma 5)).snd =
      -(goldenMul epsilon (goldenPow gamma 5)).snd := by
  change ((-epsilon) * gamma ^ 5).snd = -(epsilon * gamma ^ 5).snd
  rw [neg_mul]
  rfl
```

0268 までで正の representatives $1,\varphi,\ldots,\varphi^4$ の第二座標表が完成した。次の theorem は representative の符号反転が積の第二座標を単に符号反転させることを示し、unit class の符号を第五冪側へ吸収・整理するための座標 API を与える。