# 0266 — `golden_unit_two_mul_fifth_snd`

## 宣言種別

これは `theorem` である。

## Lean の型

```lean
theorem golden_unit_two_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 2) (goldenPow gamma 5)).snd =
      goldenFifthFstPoly gamma.fst gamma.snd +
        2 * goldenFifthSndPoly gamma.fst gamma.snd := by
  rw [goldenPhi_pow_two]
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

sector 2 の代表 unit は

$$
\varphi^2=1+\varphi,
$$

すなわち `GoldenInt` 座標で `⟨1,1⟩` である。したがって

$$
\varphi^2\gamma^5=(1+\varphi)(A+B\varphi).
$$

黄金比の関係 $\varphi^2=\varphi+1$ を使って整理すると、

$$
(1+\varphi)(A+B\varphi)
=(A+B)+(A+2B)\varphi.
$$

ゆえに第二座標は

$$
\operatorname{snd}(\varphi^2\gamma^5)=A(p,q)+2B(p,q)
$$

となる。本 theorem はこの sector 2 の座標変換を Lean 上の `GoldenInt` 乗法として確立する。

## 証明全体での役割

0264–0268 は unit representatives $1,\varphi,\varphi^2,\varphi^3,\varphi^4$ を第五冪に掛けたときの第二座標を明示する sector arithmetic の表である。本 theorem はその sector 2 を担当し、

$$
B \longmapsto A+2B
$$

という線形結合を与える。

`goldenFifthSndPoly` は定義上 $5$ を因子に持つため、後続の unit-sector 排除では packet 側から $5\mid A+2B$ が得られると、既知の $5\mid B$ と組み合わせて $5\mid A$ を抽出できる。したがって本 theorem は unit class の情報を modulo five の算術条件へ変換する bridge の一つである。

0265 の sector 1 では $A+B$ であったのに対し、本 theorem では係数が $A+2B$ となる。これは representative の座標 `⟨1,1⟩` が `goldenMul` の第二座標公式に作用した結果である。

## 直接依存する定義・補題

証明スクリプトで直接使われるものは次である。

- `goldenPhi_pow_two`
  - `goldenPow goldenPhi 2 = ⟨1, 1⟩`。
  - sector 2 の representative $\varphi^2$ を具体座標へ rewrite する。
- `goldenMul`
  - `GoldenInt` の座標乗法。
  - `simp only [goldenMul]` により積の第二座標を展開する。
- `goldenPow_five_fst`
  - `(goldenPow gamma 5).fst = goldenFifthFstPoly gamma.fst gamma.snd`。
  - 第五冪の第一座標を named polynomial $A$ へ置換する。
- `goldenPow_five_snd`
  - `(goldenPow gamma 5).snd = goldenFifthSndPoly gamma.fst gamma.snd`。
  - 第五冪の第二座標を named polynomial $B$ へ置換する。
- `goldenFifthFstPoly`, `goldenFifthSndPoly`
  - 第五冪の二座標多項式。

間接的には `GoldenInt`, `goldenPhi`, `goldenPow` と、関係 $\varphi^2=\varphi+1$ を組み込んだ黄金整数の乗法実装に依存する。

## 証明または構築の流れ

まず

```lean
rw [goldenPhi_pow_two]
```

により `goldenPow goldenPhi 2` を `⟨1,1⟩` に置き換える。

次に

```lean
simp only [goldenMul]
```

で黄金整数の積を座標へ展開する。右因子を `⟨A,B⟩` と見れば、左因子 `⟨1,1⟩` による第二座標は $A+2B$ の形になる。

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

数学的内容は $(1+\varphi)(A+B\varphi)$ の一回の展開だが、Lean では `GoldenInt` が具体座標で実装されているため、representative を named theorem で concrete pair にし、`goldenMul` を展開してから第五冪の座標 theorem を適用する。

`rw [goldenPow_five_fst, goldenPow_five_snd]` と第一・第二座標の両方を使うのは、unit multiplication によって第一座標が結果の第二座標へ流入するためである。

`simp only [goldenMul]` は simplifier の使用範囲を限定しており、proof が広い simp set に偶然依存するのを避けている。`ring` は最後の環正規化だけを担当する。

## 冗長・重複箇所

0264–0268 の sector theorem 群はほぼ同じ proof pattern を持つ。

1. `goldenPhi_pow_*` で representative を具体化する。
2. `goldenMul` を展開する。
3. `goldenPow_five_fst` / `goldenPow_five_snd` で第五冪座標を named polynomial にする。
4. `ring` で閉じる。

この反復は実装上の重複である。ただし右辺を

$$
B,\quad A+B,\quad A+2B,\quad 2A+3B,\quad 3A+5B
$$

と明示することは downstream proof の可読性と rewrite 性に有利であり、公開 API として個別 theorem を残す価値は高い。

本 theorem 単独では `ring` がやや強い可能性がある。展開後は線形結合なので `ring_nf` や追加の `simp` で閉じられる可能性もあるが、本作業では Lean build を行っていないため確認していない。

## 最適化候補

最も自然なのは、任意の `GoldenInt` の座標 `x=⟨a,b⟩`, `y=⟨A,B⟩` に対し積の第二座標を

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

のような helper があれば、sector 0–4 は representative の座標を代入するだけで導ける。

さらに第五冪の二座標を pair equality としてまとめる theorem があれば二本の rewrite を一度にまとめられる。ただし各座標 theorem を個別に保持する現行 API は、片方だけ必要な proof には扱いやすい。

したがって内部 helper を一般化しつつ、現在の個別 sector theorem 群を公開 rewrite API として残す構成が有力である。

## 必要 Mathlib import と import 最適化候補

確認できた standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem の proof では整数環上の演算、rewrite/simplification、`ring` tactic が必要である。一方 `GoldenInt`, `goldenMul`, `goldenPow` などはプロジェクト側で定義されたものなので、Mathlib の import だけでは本 theorem は独立しない。

この theorem 単体の最小 Mathlib import 集合は確認していない。元の生成 source が standalone に統合されているため、個別 module の import graph もこのリポジトリ上では直接確認できなかった。import 最適化を行うなら、`ring` と整数代数を供給する module まで段階的に縮小し、Lean build で検証する必要がある。本タスクでは Lean build を行わないため最小 import を断定しない。

## Comparator challenge 化の可否

可能である。難度は低〜中程度で、0265 とほぼ同型だが係数 2 の由来を理解できるかを見るには良い challenge になる。

```lean
theorem golden_unit_two_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 2) (goldenPow gamma 5)).snd =
      goldenFifthFstPoly gamma.fst gamma.snd +
        2 * goldenFifthSndPoly gamma.fst gamma.snd := by
  ...
```

評価点は、sector 2 representative を `goldenPhi_pow_two` で `⟨1,1⟩` に落とせるか、第一・第二座標の両方を既存 API から再利用できるか、そして $A+2B$ の係数を `goldenMul` の定義から正しく取り出せるかである。

発展 challenge として、一般の第二座標公式 $bA+(a+b)B$ を先に証明し、本 theorem をその corollary として導かせるのも有用である。

## PDF との対応

対象ブランチには

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

GitHub コネクタでは PDF 本文をバイナリとして直接取得できず、外部取得も成功しなかったため、0266 に対応する具体的ページ・節番号は確認できていない。したがって PDF 内の対応位置や文言については推測しない。

## 次に読むべき宣言

次は `golden_unit_three_mul_fifth_snd` である。

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

sector 3 の representative は $\varphi^3=1+2\varphi$、すなわち `⟨1,2⟩` であるため、第二座標は

$$
2A+3B
$$

となる。sector 2 の $A+2B$ からさらに Fibonacci 型の係数列が進む。