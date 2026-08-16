# 0134 — `golden_snd_zero`

## Lean の型

```lean
@[simp] theorem golden_snd_zero : (0 : GoldenInt).snd = 0 := rfl
```

これは `theorem` であり、同時に `@[simp]` 属性を持つ座標射影補題である。

## 数学的主張・宣言の意味

`GoldenInt` は整数対 `⟨a,b⟩` により $a+b\varphi$ を表す。Lean source では零元を

```lean
def goldenZero : GoldenInt := ⟨0, 0⟩
instance : Zero GoldenInt := ⟨goldenZero⟩
```

として定義・登録している。

したがって黄金整数の零元

$$
0=0+0\varphi
$$

の第二座標、すなわち $\varphi$ の係数も $0$ である。本補題はその事実を標準記法 `(0 : GoldenInt)` に対して公開する。

$$
\operatorname{snd}(0_{\mathbb Z[\varphi]})=0.
$$

0133 `golden_fst_zero` が零元の第一座標を扱ったのに対し、本 theorem は同じ零元の第二座標を扱う対称な補題である。

## 証明全体での役割

0132 までで `GoldenInt` の raw coordinate operation が Lean 標準の `Zero`、`One`、`Add`、`Neg`、`Sub`、`Mul` に登録され、0133 から標準記法を具体的な整数座標へ戻す `@[simp]` projection API が始まった。

`golden_snd_zero` は零元についてその API を完成させる第二の補題である。`GoldenInt` の等式を `GoldenInt.ext` により第一座標と第二座標へ分解した後、第二座標側に現れる `(0 : GoldenInt).snd` を整数の `0` に即座に正規化できる。

この小さな補題は、直後に構築される `AddCommGroup GoldenInt` や `CommRing GoldenInt` の証明で使われる

```lean
ext <;> simp
```

という証明様式を支える。特に `zero_add`、`add_zero`、`neg_add_cancel`、`zero_mul`、`mul_zero` など、零元を含む環法則を座標ごとの整数恒等式へ落とす際の simplifier API の一部である。

## 直接依存する定義・補題

直接依存は次の三点である。

- `GoldenInt`
- `goldenZero : GoldenInt := ⟨0, 0⟩`
- `instance : Zero GoldenInt := ⟨goldenZero⟩`

証明自体は数学的補題を参照せず、定義的簡約だけで成立する。

依存関係は概念的に

$$
\texttt{goldenZero}
\longrightarrow
\texttt{Zero GoldenInt}
\longrightarrow
\texttt{golden\_snd\_zero}
$$

である。

0133 `golden_fst_zero` は意味上の対になるが、本 theorem の Lean 証明はそれを呼び出していないため、直接依存ではない。

## 証明・構築の流れ

証明本体は

```lean
rfl
```

だけである。

Lean は `(0 : GoldenInt)` を `Zero GoldenInt` instance により `goldenZero` と解釈し、`goldenZero` を展開すると

```lean
⟨0, 0⟩
```

になる。その `.snd` 射影は定義的に整数 `0` へ評価されるため、左右は reflexivity で同一になる。

概念的には

$$
(0:\texttt{GoldenInt}).\texttt{snd}
\rightsquigarrow
\texttt{goldenZero.snd}
\rightsquigarrow
\langle 0,0\rangle.\texttt{snd}
\rightsquigarrow
0
$$

という reduction である。

## Lean 固有の処理

本 theorem の重要点は `rfl` と `@[simp]` が異なる役割を持つことである。

- `rfl` は、この事実が theorem-level の数学的推論ではなく definitional equality だけで証明できることを示す。
- `@[simp]` は、その定義的事実を downstream proof から安定して利用できる公開 rewrite rule として登録する。

したがって後続コードは `goldenZero` や `Zero GoldenInt` の実装を手動で unfold せず、単に

```lean
simp
```

とするだけで `(0 : GoldenInt).snd` を `0` に簡約できる。

これは実装詳細と利用側 API を分離する典型的な Lean の設計である。定義的には自明でも、明示的な simp lemma を置くことで simplifier に対する契約を固定している。

## 冗長・重複箇所

数学的情報としては `goldenZero := ⟨0,0⟩` に完全に含まれており、新しい定理内容を追加してはいない。その意味では定義情報の再公開である。

また 0133 `golden_fst_zero` とはほぼ同型で、第一射影か第二射影かだけが異なる。この二つは product-like structure における意図的な対称重複である。

一方、Lean API としてはこの重複に意味がある。`simp` は各 projection について明示的な rewrite rule を持てるため、downstream proof が `goldenZero` の内部表現を知る必要がなくなる。

## 最適化候補

候補は次の三系統である。

1. 現行どおり `golden_fst_zero` と `golden_snd_zero` を個別の `@[simp]` theorem として公開する。
2. 専用補題を削除し、simp に `goldenZero` または `Zero GoldenInt` の定義展開を許して処理する。
3. `GoldenInt` の座標 API を generic な product-like abstraction に寄せ、projection simp lemma の生成・再利用を増やす。

2 は宣言数を減らせるが、simplifier が raw implementation を unfold することへの依存が強まり、実装変更時に downstream proof が影響を受けやすくなる。現行方式は一見冗長でも、公開 simp API を明示して実装境界を安定させる点で合理的である。

さらに 0133–0144 付近の座標 projection lemma 群全体を見ると、同じ `rfl` パターンが連続するため、属性付き lemma の生成を補助する局所的なマクロやコード生成も考えられる。ただし小規模な明示列挙のほうが監査可能性は高い。

## 必要 Mathlib import と import 最適化候補

standalone source は全体として `import Mathlib` を利用しているが、本 theorem 単独は高度な Mathlib 定理を必要としない。直接必要なのは、structure と projection、`Zero` typeclass、整数型 `ℤ`、theorem と `@[simp]` 属性、および上流の `GoldenInt` / `goldenZero` 定義である。

したがって本補題だけを理由に `Mathlib` 全体を import する必要はないと考えられる。ただし `GoldenOrder` モジュール全体では直後に `AddCommGroup`、`AddGroupWithOne`、`CommRing`、`Zsqrtd`、`ring`、`omega` などを使用するため、実際の最小 import はモジュール全体の依存関係に支配される。

今回は Lean build を行わないため、具体的な最小 import 集合は未検証である。この import 最適化案は推測として扱う。

## Comparator challenge 化の可否

単独では小さすぎるが、0133 以降の projection simp lemma 群をまとめれば良い Comparator challenge になる。

比較候補は、

- 各座標について明示的な `@[simp]` lemma を置く方式
- raw definitions の unfold に simp を依存させる方式
- generic product-like API や生成補助を用いる方式

である。

比較軸として、`ext <;> simp` だけで閉じる downstream theorem の数、simp trace の長さ、raw implementation への依存度、コード量、定義変更への耐性、監査時の読みやすさを測れる。

本 theorem 自体の証明難度はゼロに近いが、「定義的に自明な事実を public simp API として残す価値」を比較するには良い最小例である。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/GoldenOrder.lean` generated section である。Lean source では

```lean
@[simp] theorem golden_fst_zero : (0 : GoldenInt).fst = 0 := rfl
@[simp] theorem golden_snd_zero : (0 : GoldenInt).snd = 0 := rfl
@[simp] theorem golden_fst_one : (1 : GoldenInt).fst = 1 := rfl
```

と並び、本 theorem が零元の projection pair の第二要素であり、次に単位元 `1` の projection pair へ進むことが確認できる。

対象ブランチには `docs/pdf/FLT5-main-ja-v0-r1.pdf` と `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在することも確認した。ただし本 theorem に対応する具体的 PDF ページは今回直接特定していないため、ページ番号や節番号は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
@[simp] theorem golden_fst_one : (1 : GoldenInt).fst = 1 := rfl
```

である。0133–0134 で零元 `0` の二座標に対する simp API が揃い、次は単位元 `1 = 1 + 0\varphi` の第一座標を標準記法から整数座標へ正規化する段階へ進む。