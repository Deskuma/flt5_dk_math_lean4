# 0019 — `not_fifth_power_body_of_clean`

> 本文書は日本語正本です。英語版は本正本からの対応翻訳です。

## Lean の型

```lean
theorem not_fifth_power_body_of_clean
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    ¬ ∃ x : ℕ, g * GN5 g y = x ^ 5 := by
  rintro ⟨x, hx⟩
  have hqDivPow : q ∣ x ^ 5 := by
    rw [← hx]
    exact h.dvd_body
  have hqDivX : q ∣ x := h.prime.dvd_of_dvd_pow hqDivPow
  obtain ⟨k, rfl⟩ := hqDivX
  apply h.not_sq_dvd_body
  rw [hx]
  use q ^ 3 * k ^ 5
  ring
```

完全修飾名は `DkMath.FLT.Five.not_fifth_power_body_of_clean` です。

## 数学的主張

`CleanGN5Channel g y q` が成立するなら、full body $g\,GN5(g,y)$ は自然数の完全第五冪ではありません。

$$
¬\exists x\in\mathbb{N},\ g\,GN5(g,y)=x^5
$$

clean channel は、素数 $q$ が full body を割る一方、その平方 $q^2$ は full body を割らないことを保証します。したがって full body における $q$ の指数はちょうど $1$ です。完全第五冪ではすべての素因数指数が $5$ の倍数になるため、指数 $1$ は両立しません。

## 証明全体での役割

この定理は `CleanGN5Channel` の局所情報を、第五冪差の因数分解に現れる full body の完全第五冪排除へ変換する主要な消費定理です。

直前の `not_fifth_power_GN5_of_clean` は `GN5(g,y)` 単体を対象にしました。本定理は gap 因子 $g$ を含む積へ対象を広げます。そのため、単なる `h.dvd_GN5` と `h.noLift` ではなく、すでに構築された

- `h.dvd_body : q ∣ g * GN5 g y`
- `h.not_sq_dvd_body : ¬ q ^ 2 ∣ g * GN5 g y`

を直接利用します。

後続の FLT5 縮約では、第五冪差

$$
z^5-y^5=(z-y)\,GN5(z-y,y)
$$

が左辺の第五冪 $x^5$ と等しいため、適切な clean channel を供給できれば本定理が直ちに矛盾を与えます。したがって本定理は「局所 valuation-one 証明書」と「大域的な第五冪不可能性」を接続する橋です。

## 直接依存する定義・補題

- `DkMath.FLT.Five.CleanGN5Channel`
- `DkMath.FLT.Five.CleanGN5Channel.dvd_body`
- `DkMath.FLT.Five.CleanGN5Channel.not_sq_dvd_body`
- フィールド `h.prime : Nat.Prime q`
- `Nat.Prime.dvd_of_dvd_pow`
- `rintro`
- `obtain`
- `rw`
- `ring`

`GN5` の具体的な多項式定義は証明中で展開されません。必要なのは clean channel が提供する整除性 API だけです。

## 証明の流れ

1. full body がある自然数 $x$ の第五冪に等しいと仮定する。
2. `h.dvd_body` と等式 `hx` から $q∣x^5$ を得る。
3. $q$ の素数性と `Nat.Prime.dvd_of_dvd_pow` により $q∣x$ を得る。
4. $x=qk$ と書く。
5. `h.not_sq_dvd_body` を適用し、full body が $q^2$ で割れることを示す目標へ移る。
6. `hx` により full body を $(qk)^5$ へ書き換える。
7. 商 $q^3k^5$ を明示し、

$$
(qk)^5=q^2\left(q^3k^5\right)
$$

を `ring` で証明する。
8. `h.not_sq_dvd_body` と矛盾して終了する。

## Lean 固有の処理

```lean
rintro ⟨x, hx⟩
```

は否定された存在命題を反証法の形で展開し、証人 $x$ と等式 `hx` を同時に導入します。

```lean
have hqDivPow : q ∣ x ^ 5 := by
  rw [← hx]
  exact h.dvd_body
```

ここでは等式の向きを反転して、目標の `x ^ 5` を full body へ戻しています。直前の定理が `simpa [hx] using h.dvd_GN5` を用いたのに対し、本定理は `rw [← hx]` と名前付き API `h.dvd_body` を使います。

```lean
obtain ⟨k, rfl⟩ := hqDivX
```

は整除性から商 $k$ を取り出し、その場で $x$ を $qk$ に置き換えます。最後の `use q ^ 3 * k ^ 5` は `q^2` に対する明示的な商を与えます。`ring` は自然数半環上の多項式恒等式だけを閉じ、整除性や素数性の推論は行いません。

## 冗長・重複箇所

証明骨格は `not_fifth_power_GN5_of_clean` とほぼ同じです。異なるのは、対象と利用する局所 API です。

- `GN5` 単体版は `h.dvd_GN5` と `h.noLift` を使う。
- full body 版は `h.dvd_body` と `h.not_sq_dvd_body` を使う。

両者の共通部分を、任意の自然数 $N$ について

$$
q∣N\land q^2∤N \Longrightarrow ¬\exists x,\ N=x^5
$$

という一般補題へ切り出せます。ただし現行実装は各対象の意味を定理名と依存関係に残すため、局所的な可読性が高い利点があります。

明示的な商 `q ^ 3 * k ^ 5` の構成も前定理と重複します。一般指数 $n\ge2$ へ抽象化する場合は $q^{n-2}k^n$ を使う共通補題へ移せます。

## 最適化候補

1. `prime_dvd_not_sq_dvd_not_pow` のような一般補題を作り、二つの第五冪排除定理を特殊化として書けます。
2. 一般補題を指数 $n\ge2$ へ拡張すれば、FLT3・FLT7 などの局所 no-lift 証明と共有できる可能性があります。
3. `rw [← hx]` と `exact h.dvd_body` は明快ですが、`simpa [hx] using h.dvd_body` との proof term・エラーメッセージ比較が可能です。
4. `obtain ⟨k, rfl⟩` 後の明示的 witness を `dvd_pow` 系補題の合成で置き換えられる可能性があります。
5. valuation 層では $v_q(g\,GN5)=1$ と $5∣v_q(x^5)$ の衝突としてより抽象的に表現できます。
6. `[simp]` 属性は不要です。否定された存在命題を広域の simplifier に登録する利点は小さく、探索の予測可能性を損なう恐れがあります。

以上の最適化案は未検証です。Lean ビルドによる比較は行っていません。

## 必要 Mathlib import と import 最適化候補

standalone 生成物は `import Mathlib` を使用しています。本定理が直接必要とする機能は次の範囲です。

- 自然数の素数と整除性
- 自然数の冪
- `Nat.Prime.dvd_of_dvd_pow`
- tactic `rintro`, `obtain`, `rw`
- 半環上の `ring`

本定理自体は `omega`、`norm_num`、`Nat.factorization`、p-adic valuation を使いません。個別 Mathlib モジュールへの import 縮小は可能性がありますが、実ファイル `CleanChannel.lean` 全体では互いに素性、具体的数値評価、`norm_num` も利用するため、定理単独の最小 import とファイル全体の最小 import は一致しません。import 最小化は未検証です。

## Comparator challenge 化の可否

良い Comparator challenge になります。

比較候補は次の通りです。

- 現行の整除証人展開と `ring` による初等的証明。
- 一般補題 $q∣N\land q^2∤N\Rightarrow N$ は第五冪でない、を先に証明して特殊化する方法。
- `dvd_pow` 系補題だけで $q^2∣x^5$ を構成する方法。
- `Nat.factorization` による素因数指数の合同条件を使う方法。
- valuation API で $v_q=1$ と第五冪の指数倍性を衝突させる方法。
- `rw [← hx]` と `simpa [hx] using ...` の比較。

比較軸は proof term の大きさ、import 範囲、一般化可能性、エラー局所性、証明の数学的透明性です。現行証明は valuation を導入せず、局所指数 $1$ の矛盾を整除証人だけで可視化する点が強みです。

## 次に読むべき定理

次は `DkMath.FLT.Five.cleanGN5Channel_one_one_31` です。

これは

$$
CleanGN5Channel(1,1,31)
$$

を具体的に構成し、素数 $31$ が $GN5(1,1)$ に一度だけ現れ、gap $1$ を割らないことを `norm_num` で検証します。抽象的な clean-channel 消費定理から、有限素数 escape の具体的 provider へ進む宣言です。

## 根拠と推論の区別

定理の型、証明、宣言順、直接利用する補題は `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/CleanChannel.lean` の生成ソースで確認しました。証明全体での役割、重複評価、一般化、import 最小化、Comparator 案には解説上の分析または未検証の提案が含まれます。既存 PDF は補助的な文脈資料であり、Lean ソースを優先しました。Lean ビルドは行っていません。

---

[prev](./0018-not_fifth_power_GN5_of_clean.md) < 0019 > [next](./0020-cleanGN5Channel_one_one_31.md)
