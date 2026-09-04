# 0267 — `golden_unit_three_mul_fifth_snd`

## 宣言種別

これは `theorem` である。

## Lean の型

```lean
theorem golden_unit_three_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 3) (goldenPow gamma 5)).snd =
      2 * goldenFifthFstPoly gamma.fst gamma.snd +
        3 * goldenFifthSndPoly gamma.fst gamma.snd := by
  rw [goldenPhi_pow_three]
  simp only [goldenMul]
  rw [goldenPow_five_fst, goldenPow_five_snd]
  ring
```

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

sector 3 の代表 unit は

$$
\varphi^3=1+2\varphi,
$$

すなわち `GoldenInt` 座標で `⟨1,2⟩` である。したがって

$$
\varphi^3\gamma^5=(1+2\varphi)(A+B\varphi).
$$

黄金比の関係 $\varphi^2=\varphi+1$ を使うと、

$$
(1+2\varphi)(A+B\varphi)
=(A+2B)+(2A+3B)\varphi.
$$

ゆえに第二座標は

$$
\operatorname{snd}(\varphi^3\gamma^5)=2A(p,q)+3B(p,q)
$$

となる。本 theorem はこの sector 3 の座標変換を Lean 上の `GoldenInt` 乗法として確立する。

## 証明全体での役割

0264–0268 は unit representatives $1,\varphi,\varphi^2,\varphi^3,\varphi^4$ を第五冪に掛けたときの第二座標を明示する sector arithmetic の表である。本 theorem はその sector 3 を担当し、

$$
B \longmapsto 2A+3B
$$

という線形結合を与える。

この公式は後続の `signedGolden_nonzero_unitSector_false` で直接使われる。packet 側から積の第二座標が $5$ で割り切れることが既知であり、さらに `goldenFifthSndPoly` 自体も常に $5$ で割り切れる。したがって sector 3 では

$$
5\mid 2A+3B,
\qquad
5\mid B
$$

から

$$
5\mid 2A
$$

を得る。$5$ は素数で $5\nmid2$ なので最終的に

$$
5\mid A
$$

を抽出し、`five_dvd_goldenNorm_of_five_dvd_fifthFst` を通じて $5\mid\operatorname{Norm}(\gamma)$ を導く。これは packet invariant の $5\nmid\operatorname{Norm}(\gamma)$ と矛盾する。

したがって本 theorem は単なる座標計算ではなく、sector 3 を排除する modulo-five argument への入力である。

## 直接依存する定義・補題

証明スクリプトで直接使われるものは次である。

- `goldenPhi_pow_three`
  - `goldenPow goldenPhi 3 = ⟨1, 2⟩`。
  - sector 3 の representative $\varphi^3$ を concrete coordinate に rewrite する。
- `goldenMul`
  - `GoldenInt` の座標乗法。
  - `simp only [goldenMul]` により積の第二座標を展開する。
- `goldenPow_five_fst`
  - `(goldenPow gamma 5).fst = goldenFifthFstPoly gamma.fst gamma.snd`。
  - 第五冪の第一座標を named polynomial $A$ に置き換える。
- `goldenPow_five_snd`
  - `(goldenPow gamma 5).snd = goldenFifthSndPoly gamma.fst gamma.snd`。
  - 第五冪の第二座標を named polynomial $B$ に置き換える。
- `goldenFifthFstPoly`, `goldenFifthSndPoly`
  - 第五冪の二座標を与える多項式。

間接的には `GoldenInt`, `goldenPhi`, `goldenPow` と、$\varphi^2=\varphi+1$ を組み込んだ黄金整数の乗法実装に依存する。

## 証明または構築の流れ

最初に

```lean
rw [goldenPhi_pow_three]
```

で `goldenPow goldenPhi 3` を `⟨1,2⟩` に置き換える。

次に

```lean
simp only [goldenMul]
```

で黄金整数の積を座標演算へ展開する。右因子を `⟨A,B⟩` と見れば、左因子 `⟨1,2⟩` による第二座標は $2A+3B$ になる。

続いて

```lean
rw [goldenPow_five_fst, goldenPow_five_snd]
```

により raw fifth power の二座標を `goldenFifthFstPoly` と `goldenFifthSndPoly` に置換する。

最後に

```lean
ring
```

で整数環上の残余多項式恒等式を正規化して閉じる。

## Lean 固有の処理

数学的には $(1+2\varphi)(A+B\varphi)$ の展開だけである。しかし Lean では `GoldenInt` が具体座標で実装されているため、まず representative を named theorem で concrete pair に落とし、`goldenMul` を展開してから第五冪の二座標 theorem を適用する。

sector 3 では結果の第二座標に第一座標 $A$ が係数 2 で流入するため、`goldenPow_five_fst` と `goldenPow_five_snd` の双方が必要になる。

`simp only [goldenMul]` は simplifier を局所化しており、広い simp set に偶然依存しない証明にしている。`ring` は最後の環正規化だけを担当する。

## 冗長・重複箇所

0264–0268 の sector theorem 群は同じ proof pattern を反復している。

1. `goldenPhi_pow_*` で representative を具体化する。
2. `goldenMul` を展開する。
3. `goldenPow_five_fst` / `goldenPow_five_snd` で第五冪座標を named polynomial にする。
4. `ring` で閉じる。

これは実装上の重複である。一方、右辺を

$$
B,\quad A+B,\quad A+2B,\quad 2A+3B,\quad 3A+5B
$$

と個別 theorem にしておくことは、後続の `rw` と divisibility proof の可読性に大きな利点がある。

本 theorem 単独では `ring` がやや強い可能性がある。展開後は実質的に線形結合なので、より限定的な簡約でも閉じる可能性があるが、本作業では Lean build を行わないため確認していない。

## 最適化候補

最も自然なのは、任意の `GoldenInt` の座標 `x=⟨a,b⟩`, `y=⟨A,B⟩` に対して積の第二座標を

$$
bA+(a+b)B
$$

と与える一般 lemma を用意することである。

概念的には

```lean
lemma goldenMul_snd_formula (x y : GoldenInt) :
    (goldenMul x y).snd =
      x.snd * y.fst + (x.fst + x.snd) * y.snd := by
  ...
```

のような helper があれば、sector 0–4 は representative の座標を代入するだけで導出できる。

さらに `goldenPow_five_fst` と `goldenPow_five_snd` を pair equality としてまとめた theorem があれば二本の rewrite を一度に扱える。ただし現行の座標別 API は downstream で片方だけ必要な場合には扱いやすい。

したがって内部 helper を一般化しつつ、現在の sector theorem 群は公開 rewrite API として残すのがよい。

## 必要 Mathlib import と import 最適化候補

確認できた standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem の proof には整数環上の演算、rewrite/simplification、`ring` tactic が必要である。一方 `GoldenInt`, `goldenMul`, `goldenPow` などはプロジェクト側の定義なので、Mathlib import だけでは独立しない。

この theorem 単体の最小 Mathlib import 集合は確認していない。standalone artifact は複数の生成 source module を統合しており、個別 module の最小 import graph はこの確認だけでは断定できない。import 最適化を行うなら、整数代数と `ring` を供給する module まで段階的に縮小して Lean build で検証する必要がある。本タスクでは Lean build を行わないため最小 import を断定しない。

## Comparator challenge 化の可否

可能である。難度は低〜中程度である。

```lean
theorem golden_unit_three_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 3) (goldenPow gamma 5)).snd =
      2 * goldenFifthFstPoly gamma.fst gamma.snd +
        3 * goldenFifthSndPoly gamma.fst gamma.snd := by
  ...
```

評価点は、sector 3 representative を `goldenPhi_pow_three` で `⟨1,2⟩` に落とせるか、第五冪を定義から再展開せず既存の二座標 theorem を再利用できるか、そして `goldenMul` の第二座標から $2A+3B$ を正しく抽出できるかである。

発展 challenge として、本 theorem の後続で実際に使われる

$$
5\mid2A+3B,\quad 5\mid B \Longrightarrow 5\mid A
$$

まで含めると、座標算術と素数 divisibility の接続を問う、より良い問題になる。

## PDF との対応

対象ブランチには

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

GitHub コネクタでは PDF ファイルの存在とメタデータは確認できたが、この実行では本文を解析していない。そのため 0267 に対応する具体的ページ・節番号、または PDF 内の文言との一対一対応は確認できていない。推測は行わない。

## 次に読むべき宣言

次は `golden_unit_four_mul_fifth_snd` である。

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

sector 4 の representative は $\varphi^4=2+3\varphi$、すなわち `⟨2,3⟩` であるため、第二座標は

$$
3A+5B
$$

となる。これで unit representatives 0–4 の第二座標表が完成する。