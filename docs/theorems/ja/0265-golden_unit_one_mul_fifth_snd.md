# 0265 — `golden_unit_one_mul_fifth_snd`

## 宣言種別

これは `theorem` である。

## Lean の型

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

sector 1 の代表 unit は

$$
\varphi^1=\varphi.
$$

黄金比の関係

$$
\varphi^2=\varphi+1
$$

を使うと、

$$
\varphi(A+B\varphi)
=A\varphi+B\varphi^2
=B+(A+B)\varphi.
$$

したがって第二座標は

$$
\operatorname{snd}(\varphi\gamma^5)=A(p,q)+B(p,q)
$$

となる。本 theorem はこの恒等式を `GoldenInt` の具体的な座標乗法として Lean 上で確立している。

ここでいう「sector」は幾何学的な領域ではなく、unit を fifth power で割った剰余類を表す代数的 sector である。sector 1 は代表元 $\varphi$ に対応する。

## 証明全体での役割

0264 `golden_unit_zero_mul_fifth_snd` では、代表 unit が $1$ なので第五冪の第二座標 $B$ がそのまま残った。本 theorem では初めて第一座標 $A$ と第二座標 $B$ が混合し、

$$
B \longmapsto A+B
$$

という sector 固有の線形結合が現れる。

この形は後続の非零 unit-sector 排除で重要である。`goldenFifthSndPoly` は常に $5$ で割れるため、もし packet 側から sector 1 の第二座標 $A+B$ も $5$ で割れるなら、その差を取って

$$
5\mid A
$$

を得られる。さらに第一座標の $5$ 可除性から `goldenNorm gamma` の $5$ 可除性を導き、packet invariant と矛盾させるのが後段の流れである。

実際、正本 source の `signedGolden_nonzero_unitSector_false` では sector 1 の場合に

```lean
rw [hbeta, golden_unit_one_mul_fifth_snd] at hb
have h := dvd_sub hb hS
ring_nf at h
exact h
```

という形で本 theorem が直接使われる。

したがって本 theorem は単なる座標計算ではなく、unit class を modulo five の算術条件へ変換する bridge である。

## 直接依存する定義・補題

直接の証明スクリプトで使われるものは次である。

- `goldenPhi_pow_one`
  - `goldenPow goldenPhi 1 = ⟨0, 1⟩`。
  - sector 1 の representative $\varphi$ を具体座標へ rewrite する。
- `goldenMul`
  - `GoldenInt` の座標乗法。
  - `simp only [goldenMul]` により積の第二座標を展開する。
- `goldenPow_five_fst`
  - `(goldenPow gamma 5).fst = goldenFifthFstPoly gamma.fst gamma.snd`。
  - raw fifth power の第一座標を named polynomial $A$ へ置換する。
- `goldenPow_five_snd`
  - `(goldenPow gamma 5).snd = goldenFifthSndPoly gamma.fst gamma.snd`。
  - raw fifth power の第二座標を named polynomial $B$ へ置換する。
- `goldenFifthFstPoly`, `goldenFifthSndPoly`
  - 第五冪の二つの座標多項式。

間接的には `GoldenInt`, `goldenPhi`, `goldenPow` の各定義と、黄金整数の関係 $\varphi^2=\varphi+1$ を組み込んだ `goldenMul` の実装に依存する。

## 証明の流れ

証明は四段階である。

まず

```lean
rw [goldenPhi_pow_one]
```

により

```lean
goldenPow goldenPhi 1
```

を具体座標 `⟨0, 1⟩` に置き換える。

次に

```lean
simp only [goldenMul]
```

で黄金整数の乗法を座標へ展開する。左因子が `⟨0,1⟩` なので、右因子を `⟨A,B⟩` と見れば第二座標は $A+B$ の形になる。

続いて

```lean
rw [goldenPow_five_fst, goldenPow_five_snd]
```

で raw fifth power の二座標をそれぞれ `goldenFifthFstPoly` と `goldenFifthSndPoly` に rewrite する。

最後に

```lean
ring
```

で残った整数環上の多項式等式を正規化して閉じる。

## Lean 固有の処理

数学的には $\varphi(A+B\varphi)=B+(A+B)\varphi$ という一行の計算である。しかし Lean では `GoldenInt` の座標モデルを使っているため、まず `goldenPhi_pow_one` により representative を concrete pair にし、`goldenMul` を展開してから named fifth-power coordinate theorem を適用している。

`rw [goldenPow_five_fst, goldenPow_five_snd]` と二本を明示する点が 0264 との違いである。0264 では第二座標だけで足りたが、sector 1 では unit multiplication により第一座標が第二座標へ流入するため、両方の coordinate theorem が必要になる。

また `simp only [goldenMul]` と simplifier の対象を制限しているため、proof が広い simp set に偶然依存しにくい。最後の `ring` は整数係数多項式としての正規化を担当する。

## 冗長・重複箇所

0264–0268 の sector theorem はすべて、

1. `goldenPhi_pow_*` で representative を具体化する
2. `goldenMul` を展開する
3. `goldenPow_five_fst` / `goldenPow_five_snd` で第五冪座標を named polynomial にする
4. `ring` で閉じる

という同型の proof pattern を共有する。

したがって実装上は重複がある。一方で、各 theorem の右辺が

$$
B,\quad A+B,\quad A+2B,\quad 2A+3B,\quad 3A+5B
$$

と明示されることは downstream の可読性に大きな利点があるため、公開 theorem 自体を統合する必要性は低い。

本 theorem 単独では `ring` がやや強い可能性がある。`goldenMul` の展開後はほぼ線形等式なので、より弱い `simp` または `ring_nf` で閉じられる可能性がある。ただし本作業では Lean build を行っていないため、最小 tactic 構成は未確認である。

## 最適化候補

最も自然な最適化は、任意の `GoldenInt` 座標 `⟨a,b⟩` と `⟨A,B⟩` に対して第二座標を

$$
bA+(a+b)B
$$

として与える一般 lemma を用意することである。

たとえば概念的には

```lean
lemma goldenMul_snd_formula (x y : GoldenInt) :
    (goldenMul x y).snd =
      x.snd * y.fst + (x.fst + x.snd) * y.snd := by
  ...
```

のような API があれば、sector 0–4 は代表座標を代入するだけになる。

さらに `goldenPow_five_fst` と `goldenPow_five_snd` を pair equality としてまとめる theorem を用意すれば、第五冪の二座標 rewrite を一度の API 呼び出しにできる。ただし現在の二本立ては個々の座標だけ欲しい downstream proof には扱いやすい。

したがって、一般 lemma を内部 helper として追加し、現在の明示的 sector theorem 群を公開 API として残す構成がよい候補である。

## 必要 Mathlib import と import 最適化候補

確認できた standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem の proof では少なくとも rewrite/simplification と `ring` tactic、整数環上の演算が必要である。ただし `GoldenInt`, `goldenMul`, `goldenPow` などはプロジェクト側の定義なので、Mathlib の最小 import だけでは theorem は成立せず、元 module の依存関係も必要になる。

この theorem 単体の最小 Mathlib import 集合は確認していない。import 最適化をする場合は、元 module `GoldenFifthPowerCoordinates.lean` の直接 import を維持しつつ、`ring` と整数演算を供給する Mathlib module まで段階的に縮小して build 検証するのが妥当である。本タスクでは Lean build を行わないため、特定の最小 import を断定しない。

## Comparator challenge 化の可否

可能である。難度は低〜中程度で、0264 より少し良い challenge になる。

challenge としては `goldenPhi_pow_one`, `goldenPow_five_fst`, `goldenPow_five_snd`, `goldenMul` を利用可能にした上で、次を証明させる形が適している。

```lean
theorem golden_unit_one_mul_fifth_snd (gamma : GoldenInt) :
    (goldenMul (goldenPow goldenPhi 1) (goldenPow gamma 5)).snd =
      goldenFifthFstPoly gamma.fst gamma.snd +
        goldenFifthSndPoly gamma.fst gamma.snd := by
  ...
```

評価点は、

- sector representative を既存 theorem で具体化できるか
- 第一・第二座標の両方が必要になることを見抜けるか
- raw `goldenPow` を無駄に全面展開せず named coordinate API を再利用できるか
- 最後を環正規化で簡潔に閉じられるか

である。

さらに発展 challenge として、一般の `⟨a,b⟩` による第二座標変換 $bA+(a+b)B$ を先に証明し、本 theorem を corollary として導かせる形も有用である。

## PDF との対応

対象ブランチには

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

ただし今回の GitHub コネクタでは PDF はバイナリとして本文取得できず、0265 に対応する具体的ページ・節番号を確定できなかった。そのため PDF 内の対応位置については推測しない。

## 次に読むべき宣言

次は `golden_unit_two_mul_fifth_snd` である。

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

sector 2 の代表は $\varphi^2=1+\varphi$、すなわち座標 `⟨1,1⟩` である。そのため第五冪 `⟨A,B⟩` に掛けると第二座標は

$$
A+2B
$$

となる。sector 1 の $A+B$ に続き、unit representative の Fibonacci 型座標が第二座標の係数列として表面化していく。