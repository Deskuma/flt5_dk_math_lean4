# 0269 — `golden_neg_unit_mul_fifth_snd`

## 宣言種別

これは `theorem` である。

## Lean の型

```lean
theorem golden_neg_unit_mul_fifth_snd (epsilon gamma : GoldenInt) :
    (goldenMul (-epsilon) (goldenPow gamma 5)).snd =
      -(goldenMul epsilon (goldenPow gamma 5)).snd := by
  change ((-epsilon) * gamma ^ 5).snd = -(epsilon * gamma ^ 5).snd
  rw [neg_mul]
  rfl
```

型としては、任意の `epsilon gamma : GoldenInt` に対して、左因子 `epsilon` の符号を反転すると、`gamma^5` との積の第二座標も正確に符号反転することを主張している。

## 数学的主張

`GoldenInt` を黄金整数環の座標モデルとし、

$$
\epsilon=a+b\varphi,\qquad \gamma^5=A+B\varphi
$$

と書く。積の第二座標は黄金比の関係 $\varphi^2=\varphi+1$ により

$$
\operatorname{snd}(\epsilon\gamma^5)=bA+(a+b)B
$$

である。

ここで `epsilon` を `-epsilon=-a-b\varphi` に置き換えると、

$$
\operatorname{snd}((-\epsilon)\gamma^5)
=(-b)A+(-a-b)B
=-\bigl(bA+(a+b)B\bigr).
$$

したがって

$$
\operatorname{snd}((-\epsilon)\gamma^5)
=-\operatorname{snd}(\epsilon\gamma^5)
$$

となる。本 theorem はこの符号反転則を座標展開ではなく、環の一般法則 `(-x)y=-(xy)` を利用して証明している。

## 証明全体での役割

0264–0268 では正の代表

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

を第五冪に掛けたときの第二座標

$$
B,\quad A+B,\quad A+2B,\quad 2A+3B,\quad 3A+5B
$$

を個別に計算した。

一方、unit class の実際の代表には符号 $\pm$ が現れうる。ここで負の代表ごとに同じ第五冪座標計算を五回追加する必要はない。本 theorem により、正の sector で得た第二座標公式をそのまま符号反転して負の sector に移せる。

したがって 0269 は「sector arithmetic の倍増」を防ぐ橋である。正の五 sector と負の五 sector を別々の多項式表として保持するのではなく、負号を環構造へ押し戻し、既存の正 sector 計算を再利用できるようにする。

直後の `SignedGoldenRamifierStrippedPacket.unitSector_snd_eq` からは、個々の代表座標の計算から packet の five-adic 第二座標へ議論が進む。0269 はその直前で符号処理を閉じる小さな正規化 lemma と読める。

## 直接依存する定義・補題

証明スクリプトで直接現れるものは次である。

- `GoldenInt`
  - 黄金整数 $a+b\varphi$ の整数座標モデル。
  - 本 theorem では `epsilon`, `gamma` の型として使われる。
- `goldenMul`
  - explicit golden-order API の乗法。
  - `golden_mul_eq` により環の `(*)` と定義的に一致する。
- `goldenPow`
  - explicit golden-order API の自然数冪。
  - `golden_pow_eq` により環の `(^)` と定義的に一致する。
- `neg_mul`
  - 一般環で $(-a)b=-(ab)$ を与える Mathlib の標準補題。
- `GoldenInt` の `Neg`, `Mul`, `Pow` / ring structure
  - `change` 後の式を通常の環記法として扱うために必要である。

正本では

```lean
@[simp] theorem golden_mul_eq (x y : GoldenInt) : goldenMul x y = x * y := rfl
@[simp] theorem golden_pow_eq (x : GoldenInt) (n : ℕ) : goldenPow x n = x ^ n := rfl
```

があり、explicit API と型クラス由来の環演算が定義的に対応している。本 theorem の `change` はこの対応を利用している。

## 証明または構築の流れ

最初に

```lean
change ((-epsilon) * gamma ^ 5).snd = -(epsilon * gamma ^ 5).snd
```

とする。

元の goal は `goldenMul` と `goldenPow` で書かれているが、これらは環の乗法と冪に定義的に一致するため、`change` で通常の ring notation へ移ることができる。この時点では座標展開を一切行っていない。

次に

```lean
rw [neg_mul]
```

で

$$
(-\epsilon)\gamma^5=-(\epsilon\gamma^5)
$$

を適用する。左辺の積そのものが負号の外へ移る。

最後に

```lean
rfl
```

で閉じる。これは `GoldenInt` の negation が座標ごとの negation であり、負の `GoldenInt` の `.snd` が元の `.snd` の負になることが定義的に計算できるためである。

## Lean 固有の処理

数学的には `(-x)y=-(xy)` と「第二座標は negation と可換」の二点だけである。

Lean 上で特徴的なのは、最初から `goldenMul` を `simp` 展開して座標式に落とさず、`change` を使って既に構築済みの ring instance に乗り換えている点である。これにより 0264–0268 のような `ring` 計算は不要になる。

`rw [neg_mul]` の後の `rfl` も重要である。ここで別の座標 negation lemma を呼ばずに済むのは、`GoldenInt` の negation と projection が定義的に整合しているためである。

この証明は explicit API と abstract algebra API を切り替える Lean コードの良い小例になっている。

## 冗長・重複箇所

本 theorem 自体は非常に短く、目立つ冗長性はない。むしろ 0264–0268 で生じうる負 unit 側の重複を除去するための theorem である。

代替として

```lean
simp [golden_mul_eq, golden_pow_eq]
```

のような一括 simplification で閉じる可能性はある。しかし、現在の

```lean
change ...
rw [neg_mul]
rfl
```

は使用する代数法則を明示しており、proof audit の観点では読みやすい。

また `goldenMul` と `goldenPow` が ring notation と `rfl` で一致する API を既に持つため、この theorem 専用の座標展開補題を追加する必要はない。

## 最適化候補

コード長だけを縮めるなら `simpa [golden_mul_eq, golden_pow_eq]` 系の proof を試す余地がある。ただし本タスクでは Lean build を行わないため、実際に同じ goal が安定して閉じるかは未確認である。

設計上は、より一般に任意の `x y : GoldenInt` に対して

$$
\operatorname{snd}((-x)y)=-\operatorname{snd}(xy)
$$

を述べる lemma として切り出す案もある。しかし現 theorem はすでに `epsilon` に任意性があり、右因子だけが `gamma^5` に固定されている。後続で第五冪以外にも同じ符号処理が頻出しない限り、一般化の実益は小さい。

したがって現状では「短くすること」よりも、`change` → `neg_mul` → `rfl` という意図の明瞭さを維持する方が有利に見える。

## 必要 Mathlib import と import 最適化候補

確認できた正本 standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem が Mathlib 側で直接必要とする主な要素は ring の基本法則 `neg_mul` と通常の tactic / rewriting infrastructure である。`GoldenInt`, `goldenMul`, `goldenPow`、およびその ring instance はプロジェクト側で定義されている。

この theorem 自体は `ring`, `omega`, `norm_num` などの重い tactic を使わないため、Mathlib import の最小化余地は 0264–0268 より大きい可能性がある。ただし生成前の個別 module の正確な import 宣言はこのリポジトリの standalone artifact からは確認できず、最小 import path も Lean build を行わずには断定できない。

候補としては algebraic ring basics と当該 `GoldenInt` 定義を供給するプロジェクト module のみまで縮小できる可能性がある、という範囲に留める。

## Comparator challenge 化の可否

可能である。難度は低いが、単なる算術計算とは異なる比較ポイントがある。

```lean
theorem golden_neg_unit_mul_fifth_snd (epsilon gamma : GoldenInt) :
    (goldenMul (-epsilon) (goldenPow gamma 5)).snd =
      -(goldenMul epsilon (goldenPow gamma 5)).snd := by
  ...
```

を goal として与えた場合、比較対象は次のようになる。

1. `goldenMul` を座標展開して `ring` に持ち込む brute-force proof。
2. `golden_mul_eq` / `golden_pow_eq` または definitional equality を利用して abstract ring law へ移る proof。
3. `neg_mul` を使い `rfl` で終える現行の最小構造 proof。

したがって challenge としては、行数ではなく「既存の algebraic structure を認識し、座標計算を避けられるか」を評価すると面白い。小規模ながら proof abstraction の質を比較できる。

## PDF との対応

対象ブランチには

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

今回も GitHub コネクタから PDF バイナリ本文を解析可能な形で取得できず、外部経由での PDF 取得も成功しなかった。そのため 0269 に対応する具体的ページ・節番号、PDF 本文との一対一対応は確認できていない。ここは推測せず、本稿の技術的記述はリポジトリ上の Lean source を正本としている。

## 次に読むべき宣言

次は `SignedGoldenRamifierStrippedPacket.unitSector_snd_eq` である。

正本 source では `golden_neg_unit_mul_fifth_snd` の直後に置かれ、コメントは「packet の大きな five-adic coordinate が有限 unit sector のどれでも保存される」ことを述べている。

ここからは unit representative 自身の座標計算ではなく、`SignedGoldenRamifierStrippedPacket` が持つ `beta` の第二座標情報を sector 表現へ運ぶ段階に進む。0269 までで正負の unit 側の符号処理が閉じ、次の theorem から nonzero sector 排除に必要な packet-level divisibility 情報との接続が始まる。