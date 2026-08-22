# 0193 — `goldenConj_add`

## Lean の型

```lean
theorem goldenConj_add (x y : GoldenInt) :
    goldenConj (x + y) = goldenConj x + goldenConj y := by
  ext <;> simp [goldenConj] <;> ring
```

これは `theorem` であり、黄金整数の共役 `goldenConj` が加法を保存することを示す。

## 数学的主張

`GoldenInt` の元を

$$
x=a+b\varphi,\qquad y=c+d\varphi
$$

と書く。0163 `goldenConj` は座標で

$$
(a,b)\longmapsto(a+b,-b)
$$

と定義されているので、

$$
\overline{x+y}=\overline{x}+\overline{y}
$$

が成り立つ。

実際、

$$
x+y=(a+c)+(b+d)\varphi
$$

に共役を作用させると

$$
\overline{x+y}=(a+c+b+d)-(b+d)\varphi,
$$

一方で

$$
\overline{x}+\overline{y}
=(a+b-b\varphi)+(c+d-d\varphi)
=(a+b+c+d)-(b+d)\varphi
$$

となり一致する。

本 theorem は、黄金共役が単なる座標関数ではなく、加法構造を保つ写像であることを明示する。

## 証明全体での役割

0163 以降では `goldenConj` の二次共役としての性質を段階的に整備してきた。

- 0166 `goldenConj_phi` — $\overline\varphi=1-\varphi$
- 0168 `goldenConj_ofInt` — 整数軸を固定
- 0170 `goldenConj_invol` — $\overline{\overline{x}}=x$
- 0171 `goldenConj_mul` — $\overline{xy}=\overline{x}\,\overline{y}$
- 0175 `goldenNorm_conj` — $N(\overline{x})=N(x)$

0193 は、`GoldenDivisibility.lean` 側で共役の加法・否定・減算・冪に対する互換性を追加するブロックの入口である。

特に後続の relative-primality argument では、元 `beta` とその共役 `goldenConj beta` の差や和を扱う。そのため、共役を加法式の内部へ分配できることは、共通因子を差へ移した後の式変形を標準環演算へ正規化する基礎 API になる。

0171 の乗法保存と 0193 の加法保存が揃うことで、`goldenConj` を将来的に `RingHom` または、0170 の involution を含めて `RingEquiv` として bundle する設計が自然に見えてくる。

## 直接依存する定義・補題

直接依存は次の通りである。

- `GoldenInt`
- 0163 `goldenConj`
- 0121 `goldenAdd` と、それを登録した `Add GoldenInt`
- 0137 `golden_fst_add`
- 0138 `golden_snd_add`
- `GoldenInt.ext`
- Mathlib の整数環演算と `ring` tactic

proof script では `goldenConj` を明示展開し、`ext`、`simp`、`ring` を使う。

概念的には

$$
\text{coordinate conjugation}
+\text{coordinate addition}
\Longrightarrow
\overline{x+y}=\overline{x}+\overline{y}
$$

という一段の構造保存証明である。

## 証明の流れ

現行 proof は非常に短い。

```lean
by
  ext <;> simp [goldenConj] <;> ring
```

1. `ext` で `GoldenInt` の等式を `fst` と `snd` の二つの整数等式へ分解する。
2. `simp [goldenConj]` で共役の座標定義と加法の projection simp lemma を展開する。
3. 残った整数多項式等式を `ring` で正規化して閉じる。

第一座標では、概ね

$$
(a+c)+(b+d)=(a+b)+(c+d)
$$

型の可換環恒等式が残る。第二座標では

$$
-(b+d)=(-b)+(-d)
$$

型の式へ落ちる。

したがって数学的内容は線形だが、Lean では既存の projection API と `ring` を組み合わせて、座標実装の詳細を短く吸収している。

## Lean 固有の処理

`ext` は先に定義された `@[ext] theorem GoldenInt.ext` を利用し、structure equality を二座標の equality へ変換する。

`<;>` は生成された全 goal に後続 tactic を適用するため、

```lean
ext <;> simp [goldenConj] <;> ring
```

は「両座標について同じ正規化パイプラインを走らせる」という意味になる。

`simp [goldenConj]` は `goldenConj` を unfolding するだけでなく、0137–0138 などの `@[simp]` projection lemma を使って `(x + y).fst` / `(x + y).snd` を整数演算へ落とす。

最後の `ring` は `GoldenInt` 上ではなく、既に `ℤ` の式へ還元された後で動く。したがって、この theorem の短さは 0133 以降に整備した座標 simp API の成果でもある。

## 冗長・重複箇所

0171 `goldenConj_mul` と 0193 `goldenConj_add` は、それぞれ乗法・加法保存を個別 theorem として証明している。さらに直後には `goldenConj_neg`、`goldenConj_sub` が続くため、共役の ring-map 的性質が複数の theorem に分散している。

数学的には、`goldenConj` を一度 `RingHom GoldenInt GoldenInt` として構築できれば、加法・乗法・零元・整数 cast などの保存則は bundle の field / generic theorem から得られる。さらに 0170 `goldenConj_invol` を組み合わせれば `RingEquiv` 化も可能である。

一方、現行方式は各性質が explicit coordinate proof として可視であり、FLT5 の証明監査という目的では実装の透明性が高い。抽象化によるコード削減と、座標証明の可視性の trade-off がある。

## 最適化候補

1. **現行 proof を維持する**
   - `ext <;> simp <;> ring` で短く、座標モデルを直接監査できる。

2. **`goldenConj` を `RingHom` として bundle する**
   - `map_add`、`map_mul` などを標準 API として利用可能になる。
   - 0171、0193 とその近傍 theorem の重複削減が期待できる。

3. **`goldenConj` を `RingEquiv` として bundle する**
   - 0170 の involution を inverse として使える。
   - 共役による divisibility transport や unit preservationも一般 theorem に寄せやすい。

4. **`ring` を不要にできる simp 正規形を検討する**
   - 加法保存は線形なので、適切な整数 simp lemma が揃えば `ring` なしで閉じる可能性がある。
   - ただし今回 Lean build は行わないため未検証である。

5. **一般 quadratic-order conjugation へ抽象化する**
   - 黄金整数だけでなく、二次環一般の basis conjugation として共通化できる可能性がある。

局所的には現行 proof が十分簡潔で、主な最適化余地は theorem 単体ではなく共役 API 全体の bundle 化にある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem が直接利用する表面は、

- structure extensionality
- simp
- commutative ring normalization `ring`
- `GoldenInt` の加法と projection API
- `goldenConj`

である。

高度な数論 theorem、整除、解析 API は本 theorem 自身では必要ない。ただし同じ `GoldenDivisibility.lean` module は整除・ノルム・unit・relative-primality をまとめて扱うため、module 全体の最小 import は本 theorem 単独より広い。

今回は Lean build を行わないため、正確な細粒度 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。候補は次の通り。

- A: 現行 `ext <;> simp [goldenConj] <;> ring`
- B: 明示的に `apply GoldenInt.ext` して二座標を個別証明
- C: `goldenConj` を `RingHom` として bundle し `map_add` から取得
- D: `RingEquiv` 化して generic automorphism API から取得
- E: 一般 quadratic-order conjugation theorem の特殊化

比較軸は、proof 行数、座標実装の可視性、抽象化コスト、下流 theorem の簡潔さ、Mathlib 標準 API 再利用度、一般化可能性である。

特に A と C の比較は、「explicit coordinate theorem を積む設計」と「早期に morphism として bundle する設計」の差を測る良い Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenDivisibility.lean` generated section である。

正本 source では 0192 の直後に次の並びを確認した。

```lean
theorem goldenConj_add (x y : GoldenInt) :
    goldenConj (x + y) = goldenConj x + goldenConj y := by
  ext <;> simp [goldenConj] <;> ring

theorem goldenConj_neg (x : GoldenInt) :
    goldenConj (-x) = -goldenConj x := by
  ext <;> simp [goldenConj, add_comm]
```

対象ブランチには `FLT5-main-ja-v0-r1.pdf` と `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0194 `goldenConj_neg`** である。

```lean
theorem goldenConj_neg (x : GoldenInt) :
    goldenConj (-x) = -goldenConj x := by
  ext <;> simp [goldenConj, add_comm]
```

0193 が共役の加法保存を公開したのに続き、0194 は加法逆元の保存

$$
\overline{-x}=-\overline{x}
$$

を明示する。さらにその次の `goldenConj_sub` と合わせて、共役を加法群準同型として扱うための基本 API が揃う。
