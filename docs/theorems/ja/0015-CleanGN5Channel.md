# 0015 — `CleanGN5Channel`

> 本文書は日本語正本です。英語版は本正本からの対応翻訳です。

## Lean の型

```lean
structure CleanGN5Channel (g y q : ℕ) : Prop where
  prime : Nat.Prime q
  dvd_GN5 : q ∣ GN5 g y
  not_dvd_gap : ¬ q ∣ g
  noLift : ¬ q ^ 2 ∣ GN5 g y
```

完全修飾名は `DkMath.FLT.Five.CleanGN5Channel` です。

## 数学的主張

`CleanGN5Channel g y q` は、素数 $q$ が残余核 `GN5 g y` に局所的に一度だけ現れ、gap $g$ には現れないことを表す証明データです。

四つのフィールドは次の条件を固定します。

1. $q$ は素数である。
2. $q$ は $GN5(g,y)$ を割る。
3. $q$ は gap $g$ を割らない。
4. $q^2$ は $GN5(g,y)$ を割らない。

したがって、$q$ に関する局所指数を素因数分解の言葉で読めば、gap 側の指数は $0$、`GN5` 側の指数はちょうど $1$ です。

$$
v_q(g)=0,\qquad v_q(GN5(g,y))=1
$$

ここで valuation 記法は構造体そのものには現れず、上の式は四フィールドの数学的解釈です。

## 証明全体での役割

第五冪差の body は先行定理により

$$
(g+y)^5-y^5=g\,GN5(g,y)
$$

と分解されます。`CleanGN5Channel` は、この積の中に「第五冪へ持ち上がれない素因子」を指定する局所証明書です。

$q$ は `GN5` を割るため body を割ります。一方、gap を割らず、`GN5` には平方で入らないため、body にも $q^2$ は入れません。ところが自然数の第五冪を $q$ が割るなら、素因数指数は少なくとも $5$ になります。この不一致が後続の `not_fifth_power_GN5_of_clean` と `not_fifth_power_body_of_clean` の反証核になります。

本構造体は、一般論そのものを証明するのではなく、各 provider が提示すべき局所条件を明示的に束ねます。コメントにもあるとおり、フィールドを意図的に露出させることで、素数候補の供給元を監査しやすくしています。

## 直接依存する定義・補題

直接依存は次の二つです。

- `DkMath.FLT.Five.GN5`
- `Nat.Prime`、自然数の整除関係 `Dvd.dvd`

構造体宣言自体に証明 tactic はありません。先行する `GN5` の因数分解定理や具体値補題も、型の形成には直接依存しません。

## 証明の流れ

これは theorem ではなく `Prop` 値の structure なので、証明スクリプトはありません。構築側では次の順序で証拠を供給します。

1. `prime` に $q$ の素数性を与える。
2. `dvd_GN5` に $q∣GN5(g,y)$ を与える。
3. `not_dvd_gap` に $q∤g$ を与える。
4. `noLift` に $q^2∤GN5(g,y)$ を与える。

利用側では `h.prime`、`h.dvd_GN5`、`h.not_dvd_gap`、`h.noLift` と投影し、整除性・互いに素性・平方非整除性を個別に使います。

## Lean 固有の処理

`structure ... : Prop` であるため、`CleanGN5Channel g y q` の値は計算データではなく証明データです。各フィールドもすべて命題であり、証明無関係性の対象になります。

`¬ q ∣ g` は `¬ (q ∣ g)`、`¬ q ^ 2 ∣ GN5 g y` は `¬ (q^2 ∣ GN5 g y)` と解釈されます。Lean の演算子優先順位により、現行表記で意図した型になります。

`noLift` は valuation API を用いず、平方非整除という低コストなインターフェースで「指数が $2$ 未満」を記録します。`dvd_GN5` と合わせることで、素因子指数がちょうど $1$ であることを後続証明が利用できます。

## 冗長・重複箇所

`prime`、`dvd_GN5`、`not_dvd_gap`、`noLift` は後続定理でそれぞれ独立に使われるため、現時点で明白な冗長フィールドはありません。

一方、`not_dvd_gap` と `prime` から `Nat.Coprime q g` を毎回導出できます。これを構造体に第五フィールドとして保存する案もありますが、導出可能な事実を重複保持すると構築側の負担と整合性監査が増えるため、現行の最小構成が自然です。

`noLift` を `padicValNat q (GN5 g y) = 1` のような valuation 等式へ置き換える設計も可能ですが、より重い API と非零条件を伴います。現行構造体は直接的な整除性証明に適しています。

## 最適化候補

1. 頻出するなら、`CleanGN5Channel.coprime_gap : Nat.Coprime q g` を派生補題として追加する。
2. `dvd_body` と `not_sq_dvd_body` を `[simp]` や専用 API としてどこまで公開するか監査する。
3. provider 構築向けに、具体値書換えと `norm_num` をまとめる補助コンストラクタを検討する。
4. valuation 層との往復補題を用意し、平方非整除版と `padicValNat = 1` 版の二重実装を避ける。

これらは未検証の設計提案です。Lean ビルドは行っていません。

## 必要 Mathlib import と import 最適化候補

standalone 生成物は `import Mathlib` を使用しています。構造体宣言そのものに必要なのは、自然数、冪、整除関係、`Nat.Prime`、および先行定義 `GN5` です。

候補としては `Mathlib.Data.Nat.Prime.Basic` 周辺と、`GN5` を提供するローカルモジュールまで絞れる可能性があります。ただし実際の `CleanChannel.lean` は直後の互いに素性・整除性定理も含むため、ファイル単位の最小 import は構造体単体より広くなる可能性があります。最小集合はビルド未実施のため未確定です。

## Comparator challenge 化の可否

構造体そのものは証明 tactic の比較対象ではありませんが、構築と消費の両面で良い challenge になります。

1. `(g,y,q)=(1,1,31)` の具体例を `GN5_one_one` を再利用して構築する。
2. 同じ例を `norm_num [GN5]` の直接計算で構築し、依存と可読性を比較する。
3. `prime` と `not_dvd_gap` から `Nat.Coprime q g` を導く最短証明を比較する。
4. `noLift` を valuation-one 等式から導く版と、因数分解・数値計算から直接示す版を比較する。

比較軸は証明項の透明性、provider の監査容易性、必要 import、一般化可能性、具体値補題の再利用です。

## 次に読むべき定理

次は `DkMath.FLT.Five.CleanGN5Channel.dvd_body` です。

この定理は `h.dvd_GN5` を積の右因子へ持ち上げ、

$$
q∣g\,GN5(g,y)
$$

を得ます。構造体が束ねた局所情報を第五冪 body へ流し込む最初の投影定理です。

## 根拠と推論の区別

構造体の型、四フィールド、宣言順、モジュールコメント、直後の利用定理は `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/CleanChannel.lean` の生成ソースで確認した事実です。valuation による読み替え、設計評価、import 最小化、最適化候補、Comparator 案は解説上の分析または未検証の提案を含みます。既存 PDF は補助的な物語資料として扱い、Lean 宣言に反する主張は採用していません。Lean ビルドは行っていません。

---

[prev](./0014-GN5_two_one.md) < 0015 > [next](./0016-CleanGN5Channel.dvd_body.md)
