# 0360 — `GoldenUnitFifthClass`

## 宣言種別

この宣言は **`def`** である。

```lean
/-- Existence of `i < 5` and `delta` with `x = phi^i * delta^5`. -/
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ∃ i : Fin 5, ∃ delta : GoldenInt,
    x = goldenMul (goldenPow goldenPhi i.val) (goldenPow delta 5)
```

`GoldenUnitFifthClass x` は、黄金整数 `x` が fifth power を法として `1, φ, φ², φ³, φ⁴` のいずれかの代表元に属することを表す命題である。

## Lean の型

```lean
GoldenUnitFifthClass : GoldenInt → Prop
```

引数 `x : GoldenInt` に対して命題を返す述語である。

内部では

```lean
∃ i : Fin 5, ∃ delta : GoldenInt, ...
```

と書かれているため、代表指数 `i` は型の段階で

$$
0 \le i < 5
$$

に制限される。

`i.val : ℕ` はその `Fin 5` 要素を自然数として取り出した値であり、`goldenPow goldenPhi i.val` が代表 unit `φ^i` を与える。

## 数学的意味

定義を通常の数式へ直すと、

$$
\operatorname{GoldenUnitFifthClass}(x)
\iff
\exists i\in\{0,1,2,3,4\},\ \exists \delta\in\mathbb Z[\varphi],
\quad
x=\varphi^i\delta^5.
$$

ここで `GoldenInt` は

$$
a+b\varphi,
\qquad
\varphi^2=\varphi+1
$$

を座標で実装した黄金整数環である。

重要なのは、この定義自体は `GoldenUnit x` を仮定していない点である。任意の `x : GoldenInt` に対して fifth-class 表現を持つかどうかを述べる一般の predicate として定義されている。

実際の unit 分類では後続の

```lean
theorem goldenUnitFifthClass_of_unit (x : GoldenInt) (hx : GoldenUnit x) :
    GoldenUnitFifthClass x
```

が、unit であるすべての `x` がこの predicate を満たすことを証明する。

## 証明全体での役割

0359 `goldenUnit_descent` までで、measure が 1 より大きい黄金 unit は、`φ` または `φ⁻¹` を一度掛けることでより小さい unit へ strict descent できることが確立された。

0360 は、その降下の **到達目標を命題として固定する定義** である。

分類目標は

$$
x=\varphi^i\delta^5,
\qquad
0\le i<5.
$$

指数を 5 で割った剰余だけ残し、5 の倍数分を `delta^5` 側へ吸収する構造になっている。

したがって unit 群を fifth powers で割ったときの有限代表を

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

の 5 個へ縮約するための interface predicate である。

この定義の後では、まず `φ` / `φ⁻¹` を掛けても fifth class が適切に移ることを示す補題群が置かれ、その後 `goldenUnitFifthClass_of_unit` が 0359 の strict descent を `Nat.strong_induction_on` で繰り返して全 unit の分類を完成させる。

さらに後段の `SignedGoldenUnitClasses.lean` では、この分類結果が stripped packet の unit-times-fifth-power 表現

$$
\beta=\epsilon\gamma^5
$$

の `epsilon` を 5 個の代表 `φ^i` へ落とすために使われる。これにより無限個の unit 候補を有限 5 sector へ変換できる。

## 直接依存する定義・補題

この `def` の本体が直接参照するプロジェクト内宣言は次である。

- `GoldenInt` — 黄金整数の座標型。
- `goldenPhi : GoldenInt` — 基底 unit `φ`。
- `goldenPow : GoldenInt → ℕ → GoldenInt` — 黄金整数の自然数冪。
- `goldenMul : GoldenInt → GoldenInt → GoldenInt` — 黄金整数の乗法。

型レベルでは Mathlib / Lean の

- `Prop`,
- 存在量化 `∃`,
- `Fin 5`,
- `Fin.val`,
- 自然数リテラル `5`,

を利用する。

0359 `goldenUnit_descent` はこの定義本体の直接依存ではない。依存方向は逆であり、後続 `goldenUnitFifthClass_of_unit` が 0359 を利用して `GoldenUnitFifthClass` を証明する。

## 構築の流れ

この宣言は `def` なので証明スクリプトは存在せず、命題の形を構築しているだけである。

### 1. 代表指数を `Fin 5` で取る

```lean
∃ i : Fin 5,
```

これにより `i` は 0〜4 に制限される。

単に `i : ℕ` として

```lean
i < 5
```

を別仮定にするのではなく、有限性を型へ組み込んでいる。

### 2. fifth-power の基底を取る

```lean
∃ delta : GoldenInt,
```

として、5 乗される黄金整数 `delta` を witness とする。

### 3. 代表 unit と fifth power の積として一致させる

```lean
x = goldenMul
      (goldenPow goldenPhi i.val)
      (goldenPow delta 5)
```

すなわち

$$
x=\varphi^i\delta^5
$$

を要求する。

この等式だけが predicate の実質的内容である。

## Lean 固有の処理

### `Fin 5`

`Fin 5` を使うことで、指数の範囲条件が証明項ではなく型そのものになる。

後続では `fin_cases i` によって 5 ケースを機械的に完全列挙できるため、unit sector の有限場合分けと非常に相性がよい。

### `i.val`

`goldenPow` の指数は `ℕ` を要求するため、`Fin 5` から自然数値を `i.val` で取り出している。

`i.isLt` はこの定義内では明示的に使われない。`i : Fin 5` という型に既に `i.val < 5` が保持されているためである。

### `Prop` と witness

これは data structure ではなく `Prop` なので、分類 witness `i` と `delta` は論理的存在証明として保持される。

後続 theorem では

```lean
rcases hx with ⟨i, delta, hx⟩
```

の形で witness を取り出して sector 遷移を証明する。

## 冗長・重複箇所

定義自体は非常に小さく、実質的な冗長性はない。

考えられる別表現としては、

```lean
∃ i : ℕ, i < 5 ∧ ∃ delta : GoldenInt, ...
```

や、unit class を quotient として抽象化する方法がある。しかし現在の `Fin 5` 表現は後続の `fin_cases` と直接接続でき、5 sector を明示的に扱う FLT5 証明には適している。

また `goldenMul` / `goldenPow` は後に通常の `*` / `^` と一致することが証明されているが、この層では explicit golden API を維持するため意図的に使用されていると読める。

## 最適化候補

1. `GoldenUnitFifthClass` を `GoldenUnitClassesModFifth` と統合・別名化する設計は考えられる。ただし前者は単一 `x` の predicate、後者は全 unit を量化した contract なので、現在の分離には明確な役割がある。
2. 通常の環演算を使い
   ```lean
   x = goldenPhi ^ i.val * delta ^ 5
   ```
   と書けば短くなる可能性があるが、explicit API の監査性は下がる。
3. 将来 quotient group を導入するなら fifth powers による剰余類として抽象化できる可能性がある。しかし現証明は `Fin 5` の具体的 case split を強く利用するため、必ずしも簡潔化にはならない。

これらは設計上の候補であり、今回 Lean ビルドを行っていないため変更後の互換性は未確認である。

## 必要 Mathlib import と import 最適化候補

生成 standalone `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

しかしこの定義単体では tactic は一切使わず、外部機能として必要なのは主に `Fin 5` と基本論理だけである。`GoldenInt`、`goldenPhi`、`goldenPow`、`goldenMul` が既に利用可能なら、`Mathlib` 全体を必要とする宣言ではない。

Comparator 用の極小環境では `Fin` を提供する Lean / Mathlib の基礎 import と、黄金整数 API を定義したローカル依存だけで十分である可能性が高い。

ただしリポジトリの実モジュール単位での **厳密な最小 import 集合は Lean ビルドを行っていないため未確認** である。

## Comparator challenge 化の可否

定義そのものを穴埋め challenge にしても難度は低く、ほぼ仕様転記になるため、単独 challenge としての価値は小さい。

一方、次のような仕様理解 challenge には向く。

```lean
def GoldenUnitFifthClass (x : GoldenInt) : Prop :=
  ?_
```

に対して、

- 代表指数を `Fin 5` にすること、
- fifth-power base `delta : GoldenInt` を存在量化すること、
- `x = φ^i * delta^5` を explicit golden API で表すこと、

を要求すれば、有限 unit-class interface を正確に再構成できるかを確認できる。

より有用なのは、この定義を前提として直後の sector-shift 補題や `goldenUnitFifthClass_of_unit` を challenge 化することである。そちらでは 0359 の descent と `Fin 5` の有限場合分けを実際に理解する必要がある。

## 次に読むべき宣言

次は 0361 `golden_phi_four_mul_inv_five` である。宣言種別は **`private theorem`**。

```lean
private theorem golden_phi_four_mul_inv_five :
    goldenPhi ^ 4 * goldenPhiInv ^ 5 = goldenPhiInv := by
  ...
```

これは `φ⁻¹` を掛けたとき指数 0 の class が指数 4 の class へ回り込むための具体的恒等式である。

概念的には

$$
\varphi^4(\varphi^{-1})^5
=\varphi^{-1}
$$

であり、指数を fifth powers modulo で扱う際の「$-1 \equiv 4 \pmod 5$」を黄金 unit の具体的積として認証する。

0360 が分類の target predicate を定めるのに対し、0361 からはその class を `φ` / `φ⁻¹` の乗法でどう移動させるかを支える補題群へ進む。