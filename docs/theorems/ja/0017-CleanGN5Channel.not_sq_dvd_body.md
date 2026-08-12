# 0017 — `CleanGN5Channel.not_sq_dvd_body`

> 本文書は日本語正本です。英語版は本正本からの対応翻訳です。

## Lean の型

```lean
theorem CleanGN5Channel.not_sq_dvd_body
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    ¬ q ^ 2 ∣ g * GN5 g y := by
  intro hqSqBody
  apply h.noLift
  have hqCoprimeGap : Nat.Coprime q g :=
    (Nat.Prime.coprime_iff_not_dvd h.prime).mpr h.not_dvd_gap
  have hqSqCoprimeGap : Nat.Coprime (q ^ 2) g :=
    hqCoprimeGap.pow_left 2
  exact Nat.Coprime.dvd_of_dvd_mul_left hqSqCoprimeGap hqSqBody
```

完全修飾名は `DkMath.FLT.Five.CleanGN5Channel.not_sq_dvd_body` です。

## 数学的主張

`CleanGN5Channel g y q` は、$q$ が素数で、$q∤g$、かつ $q^2∤GN5(g,y)$ であることを保持します。本定理は、これらを用いて平方 $q^2$ が積全体にも入らないことを示します。

$$
q^2∤g\,GN5(g,y)
$$

背理法で $q^2∣g\,GN5(g,y)$ と仮定します。$q∤g$ と素数性から $q$ と $g$ は互いに素であり、したがって $q^2$ と $g$ も互いに素です。積を割る $q^2$ を、互いに素な因子 $g$ から除去すると $q^2∣GN5(g,y)$ が得られ、`h.noLift` と矛盾します。

## 証明全体での役割

直前の `CleanGN5Channel.dvd_body` は $q∣g\,GN5(g,y)$ を与えました。本定理は同じ body に対して $q^2∤g\,GN5(g,y)$ を与えます。したがって body における $q$ の指数はちょうど $1$ です。

後続の `not_fifth_power_body_of_clean` は、body が第五冪 $x^5$ だと仮定します。`dvd_body` と素数性から $q∣x$ を得ると、$q^2∣x^5$、したがって $q^2∣g\,GN5(g,y)$ となり、本定理と衝突します。本定理は局所 valuation-one obstruction の平方整除版の中心です。

## 直接依存する定義・補題

- `DkMath.FLT.Five.CleanGN5Channel`
- フィールド `h.prime : Nat.Prime q`
- フィールド `h.not_dvd_gap : ¬ q ∣ g`
- フィールド `h.noLift : ¬ q ^ 2 ∣ GN5 g y`
- `Nat.Prime.coprime_iff_not_dvd`
- `Nat.Coprime.pow_left`
- `Nat.Coprime.dvd_of_dvd_mul_left`
- `DkMath.FLT.Five.GN5`

`h.dvd_GN5` は本定理では使いません。これは「$q$ が body を割る」側ではなく、「平方が body を割らない」側だけを証明しているためです。

## 証明の流れ

1. `intro hqSqBody` により $q^2∣g\,GN5(g,y)$ を仮定する。
2. `apply h.noLift` により、目標を $q^2∣GN5(g,y)$ の構成へ変える。
3. 素数性と $q∤g$ から `Nat.Coprime q g` を得る。
4. `pow_left 2` により `Nat.Coprime (q ^ 2) g` を得る。
5. `Nat.Coprime.dvd_of_dvd_mul_left` で積の左因子 $g$ を除去し、$q^2∣GN5(g,y)$ を得る。
6. これは `h.noLift` と矛盾する。

## Lean 固有の処理

`apply h.noLift` は否定命題 `¬ q ^ 2 ∣ GN5 g y` を関数として使い、現在の矛盾目標を正の整除命題へ変換します。

```lean
have hqCoprimeGap : Nat.Coprime q g :=
  (Nat.Prime.coprime_iff_not_dvd h.prime).mpr h.not_dvd_gap
```

ここでは素数 $q$ に対する「$q$ と $g$ が互いに素であること」と「$q$ が $g$ を割らないこと」の同値を `.mpr` で右から左へ使用しています。

`hqCoprimeGap.pow_left 2` は左成分だけを平方し、`Nat.Coprime (q ^ 2) g` を作ります。最後の `dvd_of_dvd_mul_left` は、$q^2$ と左因子 $g$ が互いに素であるため、$q^2∣g\,GN5(g,y)$ から右因子への整除を抽出します。

## 冗長・重複箇所

本証明は valuation を導入せず、整除性と互いに素性だけで局所指数上限を表現しています。後段の `Valuation.lean` は同じ障害を valuation の上下界として再包装するため、数学的内容には重なりがあります。しかし本定理はより初等的で依存が軽く、直接的な平方整除矛盾に利用できるため、削除すべき重複ではありません。

中間事実 `hqCoprimeGap` と `hqSqCoprimeGap` は一式に圧縮できますが、現在の形は素数非整除から平方互いに素性へ進む二段階を明示します。

## 最適化候補

1. 二つの `have` を一つの式へ畳み込めますが、可読性が下がる可能性があります。
2. `Nat.Coprime.pow_left` の指数を一般化し、$q^n$ の no-lift を扱う共通補題へ抽象化できます。
3. `Nat.Coprime.dvd_of_dvd_mul_left` の左右方向を誤りにくくするため、body 固有の補助補題を保持する現設計は妥当です。
4. valuation API が既に利用可能な層では、$v_q(g)=0$ と $v_q(GN5)=1$ から積の valuation を計算する別証明と比較できます。
5. `[simp]` 属性は否定的整除命題を広く自動化するため、通常は付けない方が安全です。

以上は設計上の分析または未検証の提案です。Lean ビルドによる比較は行っていません。

## 必要 Mathlib import と import 最適化候補

standalone 生成物は `import Mathlib` を使用しています。本定理が直接必要とするのは、自然数の素数・整除・互いに素性・冪、および次の補題群です。

- `Nat.Prime.coprime_iff_not_dvd`
- `Nat.Coprime.pow_left`
- `Nat.Coprime.dvd_of_dvd_mul_left`

実ファイル `CleanChannel.lean` には後続で `dvd_of_dvd_pow`、存在証人、`ring`、具体値の `norm_num` も使われます。そのため、ファイル単位の最小 import は本定理だけからは確定できません。`Mathlib` から素数・整除性の個別モジュールへ絞れる可能性はありますが、未検証です。

## Comparator challenge 化の可否

良い Comparator challenge になります。候補は次の通りです。

- 現行の互いに素性による因子除去証明。
- witness 形式で整除を展開し、Euclid の補題を明示的に使う証明。
- `Nat.Coprime.pow_left` を使わず、素因子の議論から直接 $q^2$ と $g$ の互いに素性を示す証明。
- valuation を用いて積の $q$-進指数が $1$ 以下であることを示す証明。
- 中間 `have` を一式へ圧縮した証明。

比較軸は proof term の大きさ、必要 import、左右因子の読みやすさ、一般化可能性、エラーメッセージの局所性です。現行証明は初等的な API だけで数学的構造を明示する点が強みです。

## 次に読むべき定理

次は `DkMath.FLT.Five.not_fifth_power_GN5_of_clean` です。

この定理は full body より先に `GN5(g,y)` 単体を対象とし、`h.dvd_GN5` と `h.noLift` を使って

$$
¬\exists x\in\mathbb{N},\ GN5(g,y)=x^5
$$

を示します。clean channel が完全第五冪を排除する最初の完成した no-fifth-power 消費定理です。

## 根拠と推論の区別

定理の型、証明、宣言順、後続定理での利用は `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/CleanChannel.lean` の生成ソースで確認しました。証明全体での役割、冗長性評価、import 最小化、一般化案、Comparator 案には解説上の分析または未検証の提案が含まれます。Lean ビルドは行っていません。

---

[prev](./0016-CleanGN5Channel.dvd_body.md) < 0017 > [next](./0018-not_fifth_power_GN5_of_clean.md)
