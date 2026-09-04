# 0018 — `not_fifth_power_GN5_of_clean`

> 本文書は日本語正本です。英語版は本正本からの対応翻訳です。

## Lean の型

```lean
theorem not_fifth_power_GN5_of_clean
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    ¬ ∃ x : ℕ, GN5 g y = x ^ 5 := by
  rintro ⟨x, hx⟩
  have hqDivPow : q ∣ x ^ 5 := by
    simpa [hx] using h.dvd_GN5
  have hqDivX : q ∣ x := h.prime.dvd_of_dvd_pow hqDivPow
  obtain ⟨k, rfl⟩ := hqDivX
  apply h.noLift
  rw [hx]
  use q ^ 3 * k ^ 5
  ring
```

完全修飾名は `DkMath.FLT.Five.not_fifth_power_GN5_of_clean` です。

## 数学的主張

`CleanGN5Channel g y q` が与えられると、`GN5(g,y)` は自然数の完全第五冪ではありません。

$$
¬\exists x\in\mathbb{N},\ GN5(g,y)=x^5
$$

構造体は $q$ が素数で、$q∣GN5(g,y)$ かつ $q^2∤GN5(g,y)$ であることを保持します。一方、もし $GN5(g,y)=x^5$ なら、素数 $q$ が $x^5$ を割ることから $q∣x$ が従い、したがって $q^2∣x^5=GN5(g,y)$ となります。これは `noLift` と矛盾します。

## 証明全体での役割

本定理は clean channel を完全第五冪排除へ変換する最初の完成した消費定理です。直前の `dvd_body` と `not_sq_dvd_body` は full body $g\,GN5(g,y)$ の局所指数を制御しましたが、本定理はより小さい対象 `GN5(g,y)` 単体を扱います。

後続の `not_fifth_power_body_of_clean` は同じ議論を full body へ持ち上げます。また `GN5_one_one_not_fifth_power` は具体的な clean channel `cleanGN5Channel_one_one_31` を本定理へ渡し、$GN5(1,1)=31$ が第五冪でないことを直ちに得ます。

## 直接依存する定義・補題

- `DkMath.FLT.Five.CleanGN5Channel`
- `DkMath.FLT.Five.GN5`
- フィールド `h.prime : Nat.Prime q`
- フィールド `h.dvd_GN5 : q ∣ GN5 g y`
- フィールド `h.noLift : ¬ q ^ 2 ∣ GN5 g y`
- `Nat.Prime.dvd_of_dvd_pow`
- `simpa`
- `rintro`
- `obtain`
- `ring`

`h.not_dvd_gap` は使いません。対象が full body ではなく `GN5` 単体なので、gap との互いに素性は不要です。

## 証明の流れ

1. `GN5 g y = x ^ 5` となる $x$ の存在を仮定する。
2. `h.dvd_GN5` を等式 `hx` で書き換え、$q∣x^5$ を得る。
3. `h.prime.dvd_of_dvd_pow` により $q∣x$ を得る。
4. $x=qk$ と置き換える。
5. `h.noLift` を適用し、$q^2∣GN5(g,y)$ を示せば矛盾となる形へ移す。
6. `hx` で `GN5(g,y)` を $(qk)^5$ に書き換える。
7. 商として $q^3k^5$ を与え、$q^2(q^3k^5)=(qk)^5$ を `ring` で証明する。

## Lean 固有の処理

`rintro ⟨x, hx⟩` は否定された存在命題を展開し、証人 $x$ と等式 `hx` を同時に導入します。

```lean
have hqDivPow : q ∣ x ^ 5 := by
  simpa [hx] using h.dvd_GN5
```

ここでは `h.dvd_GN5` の被除数 `GN5 g y` を `hx` で `x^5` に変換しています。

`obtain ⟨k, rfl⟩ := hqDivX` は整除証明 $q∣x$ から $x=qk$ という証人を取り出し、その場で $x$ を置換します。最後の `use q ^ 3 * k ^ 5` は $q^2$ の商を明示し、`ring` が自然数半環上の多項式恒等式を閉じます。

## 冗長・重複箇所

後続の `not_fifth_power_body_of_clean` は同じ骨格を持ちます。相違は、そこでは `h.dvd_body` と `h.not_sq_dvd_body` を使い、対象が $g\,GN5(g,y)$ になる点です。共通部分を一般補題へ抽象化する余地はありますが、現状の二定理は対象と依存が明確で読みやすい利点があります。

$q^2$ の商として $q^3k^5$ を直接構成する部分は第五冪に特化しています。一般の指数 $n\ge2$ へ拡張するなら $q^{n-2}k^n$ を使う共通補題にできます。

## 最適化候補

1. 「素数 $q$ が $x^n$ を割り、$n\ge2$ なら $q^2∣x^n$」という一般補題を切り出せます。
2. `obtain ⟨k, rfl⟩` と明示的な商構成を、`dvd_pow` 系補題の組み合わせへ置き換えられる可能性があります。
3. `simpa [hx]` の向きは簡潔ですが、`rw [hx] at h.dvd_GN5` のような破壊的書き換えより局所性が高く、現行形は妥当です。
4. valuation 層では $v_q(GN5)=1$ と第五冪なら $5∣v_q(GN5)$ の衝突として表現できます。
5. `[simp]` 属性を付ける定理ではありません。否定された存在命題を自動簡約へ広く投入すると予期せぬ探索を招く可能性があります。

以上は未検証の設計案を含みます。Lean ビルドによる比較は行っていません。

## 必要 Mathlib import と import 最適化候補

standalone 生成物は `import Mathlib` を使用しています。本定理が直接必要とする機能は、自然数の素数・整除・冪、存在証人の分解、半環上の `ring` です。

特に必要な主要補題・tactic は次の通りです。

- `Nat.Prime.dvd_of_dvd_pow`
- `ring`
- `simpa`
- `rintro`
- `obtain`

実ファイル `CleanChannel.lean` は同じモジュール内で互いに素性、`norm_num`、具体的 clean channel の構成も使います。したがって本定理単独の最小 import とファイル全体の最小 import は一致しません。個別 Mathlib モジュールへの縮小は可能性がありますが、未検証です。

## Comparator challenge 化の可否

良い Comparator challenge になります。

- 現行の witness 展開と `ring` による証明。
- `dvd_pow` 系補題だけで $q^2∣x^5$ を構成する証明。
- `Nat.factorization` または valuation を用いる証明。
- 一般指数 $n\ge2$ の補題を先に作って特殊化する証明。
- `omega` や `norm_num` に依存しない現行証明との import・proof term 比較。

比較軸は proof term の大きさ、import 範囲、指数一般化の容易さ、エラー局所性、数学的説明力です。現行証明は初等的な整除証人を明示し、局所指数 $1$ と第五冪の衝突を直接見せる点が強みです。

## 次に読むべき定理

次は `DkMath.FLT.Five.not_fifth_power_body_of_clean` です。

この定理は `dvd_body` と `not_sq_dvd_body` を消費し、

$$
¬\exists x\in\mathbb{N},\ g\,GN5(g,y)=x^5
$$

を示します。`GN5` 単体の障害から、第五冪差そのものに現れる full body の障害へ進む定理です。

## 根拠と推論の区別

定理の型、証明、宣言順、後続での利用は `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/CleanChannel.lean` の生成ソースで確認しました。証明全体での役割、冗長性評価、import 最小化、一般化案、Comparator 案には解説上の分析または未検証の提案が含まれます。既存 PDF は補助的な文脈資料であり、Lean ソースを優先しました。Lean ビルドは行っていません。