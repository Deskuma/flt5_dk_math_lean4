# 0016 — `CleanGN5Channel.dvd_body`

> 本文書は日本語正本です。英語版は本正本からの対応翻訳です。

## Lean の型

```lean
theorem CleanGN5Channel.dvd_body
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    q ∣ g * GN5 g y := by
  exact dvd_mul_of_dvd_right h.dvd_GN5 g
```

完全修飾名は `DkMath.FLT.Five.CleanGN5Channel.dvd_body` です。

## 数学的主張

`CleanGN5Channel g y q` が与えられると、そのフィールド `h.dvd_GN5` から $q∣GN5(g,y)$ が得られます。したがって $g$ を左から掛けた積も $q$ で割れます。

$$
q∣GN5(g,y)\Longrightarrow q∣g\,GN5(g,y)
$$

素数性、gap 非整除、平方非整除はこの結論には不要です。

## 証明全体での役割

先行する第五冪差分解では body が $g\,GN5(g,y)$ と表されます。本定理は `CleanGN5Channel` が保持する局所因子を、その full body へ移す最初の消費 API です。

後続の `not_fifth_power_body_of_clean` は、body が第五冪だと仮定したとき、本定理により $q$ がその第五冪を割ることを得ます。その後、素数の第五冪整除性から $q∣x$ を導き、`not_sq_dvd_body` と衝突させます。

## 直接依存する定義・補題

- `DkMath.FLT.Five.CleanGN5Channel`
- 構造体フィールド `CleanGN5Channel.dvd_GN5`
- `dvd_mul_of_dvd_right`
- `DkMath.FLT.Five.GN5`

数学的には一般の整除性閉性だけを用い、`h.prime`、`h.not_dvd_gap`、`h.noLift` には依存しません。

## 証明の流れ

1. `h.dvd_GN5` から $q∣GN5(g,y)$ を取り出す。
2. `dvd_mul_of_dvd_right` にその証拠と左因子 $g$ を渡す。
3. $q∣g\,GN5(g,y)$ を得る。

証明項は一行です。

```lean
exact dvd_mul_of_dvd_right h.dvd_GN5 g
```

## Lean 固有の処理

`dvd_mul_of_dvd_right` は右因子を割る事実を積全体へ持ち上げます。ここでは `h.dvd_GN5 : q ∣ GN5 g y` に対し、追加因子として `g` を指定しています。

積の表示は `g * GN5 g y` ですが、補題名の `right` は整除される因子が右側にあることを示します。可換性の書換えや `simpa [Nat.mul_comm]` は不要です。

定理は namespace `CleanGN5Channel` 内にあるため、値 `h` に対して `h.dvd_body` とメソッド風にも利用できます。

## 冗長・重複箇所

結論は `h.dvd_GN5` からその場で一行導けるため、論理的には薄いラッパーです。しかし後続証明では「clean channel が body を割る」という意味のある名前を提供し、積の向きや補題選択を局所化します。

したがって削除可能な重複ではあるものの、公開 API と可読性の観点では保持する価値があります。

## 最適化候補

1. `[simp]` 属性は通常不要です。整除命題を自動書換え対象にすると探索が不透明になる可能性があります。
2. body を専用定義にする場合、結論をその定義で述べるラッパーへ更新できます。
3. 一般化するなら、`CleanGN5Channel` 固有ではなく「右因子を割れば積を割る」標準補題の直接利用で十分です。
4. 後続で積の順序が逆転する場合に限り、対称版の局所補題を追加する価値を監査できます。

これらは設計上の提案であり、Lean ビルドによる検証は行っていません。

## 必要 Mathlib import と import 最適化候補

standalone 生成物は `import Mathlib` を使用しています。本定理単体に必要なのは自然数の整除関係、乗法、`dvd_mul_of_dvd_right`、およびローカル定義 `CleanGN5Channel` と `GN5` です。

Mathlib 側は整除性の基本補題を提供する最小モジュールまで絞れる可能性があります。ただし実ファイル `CleanChannel.lean` には素数、互いに素性、冪整除、`ring` を使う後続定理も含まれるため、ファイル単位の import 最適化は本定理だけでは決まりません。最小 import は未検証です。

## Comparator challenge 化の可否

小さな Comparator challenge に適しています。

- `exact dvd_mul_of_dvd_right h.dvd_GN5 g`
- `exact dvd_mul_left g h.dvd_GN5` に相当する別 API が利用可能か調べる。
- witness を展開して `rcases h.dvd_GN5 with ⟨k, hk⟩` から直接構成する。
- `simpa [Nat.mul_comm]` を介する証明と比較する。

比較軸は証明項の短さ、積の向きの明瞭さ、標準補題への依存、生成される proof term の単純さです。現行証明が最も直接的である可能性が高い、という評価は推論です。

## 次に読むべき定理

次は `DkMath.FLT.Five.CleanGN5Channel.not_sq_dvd_body` です。

本定理が $q$ の body への整除を与えるのに対し、次の定理は

$$
q^2∤g\,GN5(g,y)
$$

を示します。そこで初めて `prime`、`not_dvd_gap`、`noLift` の残り三フィールドが結合され、局所指数が body 全体でもちょうど $1$ であることが固定されます。

## 根拠と推論の区別

定理の型、証明、宣言順、後続での `h.dvd_body` 利用は `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/CleanChannel.lean` の生成ソースで確認しました。役割評価、API 保持の判断、import 最小化、Comparator 案は解説上の分析または未検証の提案を含みます。Lean ビルドは行っていません。

---

[prev](./0015-CleanGN5Channel.md) < 0016 > [next](./0017-CleanGN5Channel.not_sq_dvd_body.md)
