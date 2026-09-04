# 0169 — `goldenNorm_ofInt`

## Lean の型

```lean
/-- The norm of an embedded integer is its square. -/
@[simp] theorem goldenNorm_ofInt (a : ℤ) :
    goldenNorm (goldenOfInt a) = a ^ 2 := by
  simp [goldenNorm, goldenOfInt]
```

これは `theorem` であり、整数 `a : ℤ` を黄金整数環へ `goldenOfInt` で埋め込んだとき、その黄金ノルムが通常の整数平方 `a ^ 2` に一致することを示す `@[simp]` 補題である。

## 数学的主張または宣言の意味

0162 の整数埋め込みは

```lean
def goldenOfInt (a : ℤ) : GoldenInt := ⟨a, 0⟩
```

であり、0164 の黄金ノルムは

```lean
def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

である。

`GoldenInt` の元を $x=a+b\varphi$ と読むと、ノルムは

$$
N(a+b\varphi)=a^2+ab-b^2
$$

である。整数埋め込み `goldenOfInt a` では第二座標が $b=0$ なので、

$$
N(a)=a^2+a\cdot0-0^2=a^2.
$$

したがって本 theorem は、黄金整数環の二次ノルムが基礎整数軸上では通常の平方へ退化することを明示している。

## 証明全体での役割

0168 `goldenConj_ofInt` は共役が整数埋め込みを固定すること、すなわち

$$
\overline{a}=a
$$

を示した。本 theorem はその直後で、同じ整数軸に対するノルムが

$$
N(a)=a^2
$$

になることを API として公開する。

二次環の標準的な関係

$$
N(x)=x\overline{x}
$$

を念頭に置けば、整数軸では共役が恒等写像なので $N(a)=a\cdot a=a^2$ となる。この theorem 自体は後続の `golden_mul_conj` より前に置かれているため、その抽象的恒等式から証明するのではなく、明示座標の二次形式を直接簡約している。

今回確認した generated source では `goldenNorm_ofInt` という名前の後続明示使用は見つからなかった。したがって現時点では、主な役割は `@[simp]` による標準化と、共役・ノルム API の基礎事実を名前付きで公開することにあると評価するのが安全である。

## 直接依存する定義・補題

直接依存は次である。

- `GoldenInt`
- 0162 `goldenOfInt`
- 0164 `goldenNorm`
- 整数上の `0`、乗法、減法、冪に対する `simp` 基本補題

数学的には 0168 `goldenConj_ofInt` と密接に対応するが、Lean proof はそれを使用しない。また `goldenConj` や `golden_mul_conj` も直接依存ではない。

依存関係は概念的に

$$
\texttt{goldenOfInt},\ \texttt{goldenNorm}
\longrightarrow
\texttt{goldenNorm_ofInt}
$$

である。

## 証明または構築の流れ

証明は一行である。

```lean
by
  simp [goldenNorm, goldenOfInt]
```

`goldenOfInt a` を `⟨a,0⟩` に展開し、`goldenNorm` を展開すると、目標は概念的に

$$
a^2+a\cdot0-0^2=a^2
$$

へ落ちる。

その後 `simp` が

$$
a\cdot0=0,\qquad 0^2=0,\qquad a^2+0-0=a^2
$$

を処理して閉じる。

したがって proof flow は

```text
goldenNorm (goldenOfInt a)
→ goldenOfInt を座標へ展開
→ goldenNorm を二次形式へ展開
→ ℤ の零項を simp で除去
→ a^2
```

となる。

## Lean 固有の処理

この theorem では `ext` は不要である。結論の型は `GoldenInt` の等式ではなく `ℤ` の等式なので、`goldenNorm` を展開した時点で整数算術だけになる。

`@[simp]` 属性により、後続で

```lean
goldenNorm (goldenOfInt a)
```

が現れた場合、標準形

```lean
a ^ 2
```

へ自動的に書き換えられる。この向きは自然であり、特殊な黄金整数 API をより一般的な整数算術へ落とす正規化になっている。

また proof 中の `simp [goldenNorm, goldenOfInt]` は、定義展開と標準 simplifier の組合せだけで完結しており、`ring`、`norm_num`、`omega` などの追加 tactic は不要である。

## 冗長・重複箇所

数学的内容は `goldenNorm` と `goldenOfInt` の定義に既に完全に含まれているため、新しい数学情報は増えていない。しかし、

$$
N(a)=a^2
$$

は二次整数環の基本 API なので、名前付き `@[simp]` theorem として公開する価値が高い。

0168 `goldenConj_ofInt` と合わせると、整数軸について

$$
\overline{a}=a,\qquad N(a)=a^2
$$

という二本の基本則が並ぶ。この二つは将来的に共役を bundled ring automorphism、ノルムをその積から定義する抽象 API へ移す場合には一般則から導ける可能性がある。

また `goldenOfInt a` と標準 cast `(a : GoldenInt)` は同じ座標規則を持つため、`goldenNorm ((a : GoldenInt)) = a^2` の標準 cast 版を追加するか、`goldenOfInt a = (a : GoldenInt)` の bridge を用意すると downstream API をさらに Mathlib 寄りに整理できる。

## 最適化候補

候補は次である。

1. 現行の `simp [goldenNorm, goldenOfInt]` を維持する。
2. `rfl` だけで閉じるか Lean build で確認する。
3. `norm_num [goldenNorm, goldenOfInt]` など他 tactic との proof-term 差を比較する。
4. `goldenOfInt a = (a : GoldenInt)` を先に bridge し、標準 cast に対するノルム theorem を主 API にする。
5. 将来 `goldenConj` を ring automorphism として bundle し、ノルムを $x\overline{x}$ から一般的に扱う設計へ寄せる。

2 は今回は Lean build を行わないため未検証である。現行 proof は十分短く、定義の意味も明確なので、局所的な簡約だけを目的とするなら変更優先度は高くない。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自体が必要とするのは、上流の `GoldenInt`、`goldenOfInt`、`goldenNorm` と、整数の基本演算および `simp` infrastructure が中心である。

したがって theorem 単独では `Mathlib` 全体は過剰である可能性が高い。ただし `GoldenOrder` モジュール全体では `CommRing`、`Zsqrtd`、`ring`、`omega`、`norm_num` などを利用するため、実際の最小 import はモジュール単位で Lean build により検証する必要がある。今回は import 最小集合を確定しない。

## Comparator challenge 化の可否

適している。小さな定義的算術 theorem なので、証明スタイルと API 設計の差を明瞭に比較できる。

比較候補は、

- 現行の `simp [goldenNorm, goldenOfInt]`
- `rfl` が成立するか
- 標準 cast `(a : GoldenInt)` を使う版
- bundled conjugation / norm API から一般則として導く版

である。

比較軸は proof-term の短さ、定義変更への耐性、simp normal form、標準 Mathlib API との親和性、必要 import、一般化可能性である。

特に、明示座標から一行で閉じる透明性と、一般 quadratic-order API を使う抽象性の trade-off を測る小さな Comparator challenge になる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `DkMath/FLT/Five/GoldenOrder.lean` generated section である。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在することを確認した。ただし、本 theorem に対応する具体的な PDF ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

Lean source 上で直後に置かれている宣言は

```lean
/-- Conjugation is an involution. -/
theorem goldenConj_invol (x : GoldenInt) :
    goldenConj (goldenConj x) = x := by
  ext <;> simp [goldenConj]
```

である。

したがって依存順の次は **0170 `goldenConj_invol`** とする。0166 で生成元への作用、0168 で整数軸の固定を確認した後、ここで共役を二回適用すると元へ戻る

$$
\overline{\overline{x}}=x
$$

という二次共役の基本対称性を任意の `GoldenInt` に対して証明する段階へ進む。