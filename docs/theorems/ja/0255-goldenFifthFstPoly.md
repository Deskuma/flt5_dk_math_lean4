# 0255 — `goldenFifthFstPoly`

## Lean の型

```lean
/-- First-coordinate polynomial of `(p + q*phi)^5`. -/
def goldenFifthFstPoly (p q : ℤ) : ℤ :=
  p ^ 5 + 10 * p ^ 3 * q ^ 2 + 10 * p ^ 2 * q ^ 3 +
    10 * p * q ^ 4 + 3 * q ^ 5
```

これは `theorem` ではなく `def` であり、黄金整数

$$
\gamma=p+q\varphi
$$

の第五冪 `γ^5` の第一座標を与える整数係数多項式を名前付き API として定義する。

## 数学的主張・宣言の意味

黄金整数では

$$
\varphi^2=\varphi+1
$$

なので、通常の二項展開で得られる高い冪の `φ` をこの二次関係で `1,φ` 基底へ還元すると、

$$
(p+q\varphi)^5=A(p,q)+B(p,q)\varphi
$$

と一意に書ける。本定義はその第一座標

$$
A(p,q)
=p^5+10p^3q^2+10p^2q^3+10pq^4+3q^5
$$

を `goldenFifthFstPoly p q` と名付ける。

ここではまだ、この多項式が実際に `(goldenPow gamma 5).fst` と一致することを証明していない。その接続は後続の `goldenPow_five_fst` が担当する。したがって 0255 は第五冪座標の「公式そのもの」を定義する宣言である。

## 証明全体での役割

直前の 0254 までで、ramifier-stripped packet の `beta` は一般 coprime-factor theorem を通じて

$$
\beta=\varepsilon\gamma^5
$$

という unit × fifth-power の形へ送られる準備が整った。

次の `GoldenFifthPowerCoordinates.lean` では、この抽象的な第五冪表示を具体的な整数座標へ戻して算術条件を読み取る。本定義はその最初の座標 polynomial である。

module コメントでは、`gamma=p+q*φ` の第五冪の二座標を名前付けした後、代表 unit

$$
1,\varphi,\ldots,\varphi^4
$$

を掛けたときの第二座標を計算し、unit class modulo fifth powers を五つの明示的な arithmetic sector に分けると説明されている。ここでいう sector は幾何的領域ではなく、純粋に代数的な unit class である。

後続 source では `goldenFifthFstPoly` が次の用途に現れる。

- `goldenPow_five_fst` で `gamma^5` の第一座標と同一視する。
- unit `φ^i` を掛けた第五冪の第二座標公式に組み込む。
- modulo 5 で `goldenFifthFstPoly r s ≡ r + 3s` を証明する。
- 第一座標の 5-整除から `goldenNorm gamma` の 5-整除を導く。
- 非零 unit sector を排除する five-adic contradiction に用いる。

したがって本定義は、抽象的な fifth-power extraction と後段の具体的 five-adic sector arithmetic を接続する座標インターフェースである。

## 直接依存する定義・補題

本宣言は単なる整数多項式の定義なので、直接依存は非常に小さい。

- `ℤ`
- 整数の加法・乗法
- 自然数冪 `(^)`

`GoldenInt`、`goldenPow`、`goldenMul` 自体は本定義の型には現れない。数学的由来は黄金整数の第五冪だが、API としては純粋な二変数整数多項式へ切り出されている。

概念的には、上流の

$$
\varphi^2=\varphi+1
$$

と第五冪展開が背景にあるが、Lean 上のこの `def` 自体にはそれらの theorem dependency はない。

## 構築の流れ

構築は一段だけである。

```lean
def goldenFifthFstPoly (p q : ℤ) : ℤ :=
  p ^ 5 + 10 * p ^ 3 * q ^ 2 + 10 * p ^ 2 * q ^ 3 +
    10 * p * q ^ 4 + 3 * q ^ 5
```

数学的には、

1. `(p+qφ)^5` を二項展開する。
2. `φ²=φ+1` を反復して `1,φ` 基底へ還元する。
3. `1` 側の係数だけを集める。
4. 得られた整数多項式をこの名前で固定する。

Lean ではこの導出過程を定義内部に持たせず、後続の `goldenPow_five_fst` で `simp` と `ring` により実装との一致を証明する設計になっている。

## Lean 固有の処理

この宣言には tactic proof がない。`def` の右辺がそのまま計算規則になる。

`p q : ℤ` が明示されているため、係数 `10`、`3` や冪演算もすべて整数として elaboration される。後続 proof では

```lean
simp [goldenPow, goldenMul, goldenOne, goldenFifthFstPoly]
ring
```

のように本定義を unfold し、整数多項式の正規化へ落とすことができる。

また `GoldenInt` を引数に取らず座標 `p q` を直接取る設計なので、後続の modulo 5 theorem では structure projection を介さず一般の整数 `r s` に対して多項式合同を述べられる。

## 冗長・重複箇所

数学的には `(goldenPow gamma 5).fst` を毎回展開すれば、この named polynomial を独立に定義しなくても済む。その意味では表現上の重複である。

しかし専用定義を置く利点は大きい。

- 巨大な第五冪展開を theorem statement から隠せる。
- modulo 5 や整除の議論を純粋な `ℤ` 多項式として扱える。
- unit-sector の式を短く保てる。
- `goldenPow` の実装変更と arithmetic lemma の表面を分離できる。

第一座標と第二座標は対になっているため、二つを一つの pair-valued polynomial として定義する設計も考えられるが、個別座標 theorem の使いやすさとの比較が必要である。

## 最適化候補

1. **現行の二変数整数多項式を維持する**
   - modulo arithmetic と `ring` に最も直接的で、監査しやすい。

2. **第一・第二座標を pair として bundle する**
   - 例えば `goldenFifthCoords : ℤ × ℤ → ℤ × ℤ` を定義し、projection theorem を派生させる。
   - 二座標の整合性は高まるが、個別の整除 theorem では projection が増える。

3. **一般指数の coordinate recurrence を導入する**
   - `n` 乗の二座標を recurrence で定義し、`n=5` を特殊化する。
   - 一般性は上がるが、FLT5 専用 proof には過剰抽象化の可能性がある。

4. **多項式ライブラリ `Polynomial` として表現する**
   - 係数・評価・modulo map を一般 API へ寄せられる可能性がある。
   - 現行の整数算術 tactic に比べ proof burden が増える可能性もある。

現状では、第五冪専用の explicit polynomial が downstream の five-adic 計算に非常に適しており、局所的な変更優先度は低い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 `def` 単独なら必要なのは整数・冪・基本環演算だけであり、Mathlib 全体は明らかに過大である。後続 module では `ring`、`norm_num`、`Int.ModEq`、素数・整除 API などを利用するため、`GoldenFifthPowerCoordinates.lean` 全体の最小 import は本宣言単独より広い。

Lean build は今回行わないため、正確な最小 import 集合は未検証である。候補としては整数環、ring tactic、modular arithmetic、divisibility 周辺の modular import へ分割できる可能性がある。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行の explicit `def goldenFifthFstPoly`
- B: `(goldenPow gamma 5).fst` を毎回直接展開
- C: 第一・第二座標を pair-valued function へ bundle
- D: 一般 `n` 乗 coordinate recurrence から `n=5` を導出
- E: `Polynomial` / multivariate polynomial 表現を利用

比較軸は、

- downstream theorem の statement 長
- `ring` / `simp` の proof cost
- modulo 5 theorem の書きやすさ
- coordinate implementation 変更への頑健性
- generality と FLT5 専用性のバランス
- generated proof term / elaboration cost

である。

特に A と C は、「局所的に読みやすい scalar API」と「二座標の構造的一貫性」の比較として良い課題になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenFifthPowerCoordinates.lean` generated section である。

source の module コメントでは、この module が `gamma=p+q*φ` の第五冪の二座標を定義し、代表 unit `1,φ,...,φ^4` による五つの arithmetic sector を具体化すると説明している。

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし本 `def` に対応する具体的ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0256 `goldenFifthSndPoly`** である。

```lean
/-- Second-coordinate polynomial of `(p + q*phi)^5`. -/
def goldenFifthSndPoly (p q : ℤ) : ℤ :=
  5 * q * (p ^ 4 + 2 * p ^ 3 * q + 4 * p ^ 2 * q ^ 2 +
    3 * p * q ^ 3 + q ^ 4)
```

0255 が第五冪の第一座標を固定したのに対し、0256 は第二座標を固定する。特に第二座標には最初から可視な因子

$$
5q
$$

が現れる。この five-divisibility が後続の unit-sector 排除で重要な役割を持つ。
