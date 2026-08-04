# 0025 — `coprime_gap_GN5_of_coprime_of_five_not_dvd`

## Lean の型

```lean
theorem coprime_gap_GN5_of_coprime_of_five_not_dvd
    {g y : ℕ} (hgy : Nat.Coprime g y) (h5g : ¬ 5 ∣ g) :
    Nat.Coprime g (GN5 g y)
```

任意の自然数 `g`, `y` について、`g` と `y` が互いに素であり、例外素数 `5` が `g` を割らないなら、`g` と `GN5 g y` も互いに素であることを示します。

## 数学的主張

仮定は

$$
\gcd(g,y)=1,\qquad 5\nmid g
$$

です。結論は

$$
\gcd\bigl(g,GN5(g,y)\bigr)=1
$$

です。

前号の補題により、`g` と `GN5(g,y)` の共通素因子 `q` が存在すれば、

$$
q\mid 5y^4
$$

となります。`q` は素数なので、

$$
q\mid 5\qquad\text{または}\qquad q\mid y^4
$$

です。前者では `q=5` となり、`q ∣ g` と合わせて `5 ∣ g` が従い、仮定に反します。後者では `q ∣ y` が従い、`q ∣ g` と合わせて `g` と `y` の互いに素性に反します。したがって共通素因子は存在しません。

## 証明全体での役割

この定理は Reduction 層における Branch B の因子分離原理です。第五冪差の body

$$
g\,GN5(g,y)
$$

について、例外素数 `5` が gap `g` に入らない場合、二因子 `g` と `GN5(g,y)` が互いに素であることを保証します。

この互いに素性は、後続で積が第五冪であることから各因子を個別の第五冪へ分離するための前提になります。すなわち、本定理は「合同解析による共通因子の分類」から「互いに素な第五冪積の分解」へ渡す橋です。

## 直接依存する定義・補題

- `GN5`
- `dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5`
- `Nat.coprime_iff_gcd_eq_one`
- `Nat.exists_prime_and_dvd`
- `Nat.gcd_dvd_left`
- `Nat.gcd_dvd_right`
- `Nat.Prime.dvd_mul`
- `Nat.dvd_prime`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.not_coprime_of_dvd_of_dvd`

数学的な中心依存は前号の局所ルーティング補題です。その他は、gcd が `1` でないときに共通素因子を取り出し、素数の積整除性と冪整除性で矛盾へ運ぶ標準 API です。

## 証明の流れ

Lean 本体は次の通りです。

```lean
refine (Nat.coprime_iff_gcd_eq_one).2 ?_
by_contra hg
rcases Nat.exists_prime_and_dvd (n := Nat.gcd g (GN5 g y)) hg with
  ⟨q, hq, hqgcd⟩
have hqg : q ∣ g :=
  hqgcd.trans (Nat.gcd_dvd_left g (GN5 g y))
have hqGN : q ∣ GN5 g y :=
  hqgcd.trans (Nat.gcd_dvd_right g (GN5 g y))
have hq5y : q ∣ 5 * y ^ 4 :=
  dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5 hqg hqGN
rcases hq.dvd_mul.mp hq5y with hq5 | hqy4
· have hqeq : q = 5 :=
    ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hq5).resolve_left hq.ne_one
  exact h5g (hqeq ▸ hqg)
· have hqy : q ∣ y := hq.dvd_of_dvd_pow hqy4
  exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqg hqy) hgy
```

1. `Nat.Coprime` を gcd が `1` であるという目標へ変換する。
2. gcd が `1` でないと仮定し、その gcd を割る素数 `q` を取り出す。
3. gcd の標準整除性から `q ∣ g` と `q ∣ GN5 g y` を得る。
4. 前号の補題で `q ∣ 5*y^4` を得る。
5. 素数の積整除性により `q ∣ 5` と `q ∣ y^4` に分岐する。
6. `q ∣ 5` の枝では `q=5` を示し、`¬ 5 ∣ g` と矛盾させる。
7. `q ∣ y^4` の枝では `q ∣ y` を示し、`Nat.Coprime g y` と矛盾させる。

## Lean 固有の処理

`Nat.exists_prime_and_dvd` は、`Nat.gcd g (GN5 g y) ≠ 1` から直接使える形で共通素因子を返します。ここでは gcd 自体が `0` かもしれない場合も含め、ライブラリ側の定理が必要な非自明性を処理しています。

`hq.dvd_mul.mp hq5y` は、素数 `q` が積を割るなら一方の因子を割るという Euclid の補題です。第二因子が `y ^ 4` なので、後段では `hq.dvd_of_dvd_pow` により基数 `y` へ整除性を降ろします。

`q ∣ 5` から `q=5` を得る部分は少し精密です。`Nat.dvd_prime` は `q=1 ∨ q=5` 型の選択肢を返すため、`hq.ne_one` で `q=1` を除外しています。`by decide : Nat.Prime 5` は具体的素数性を決定手続きで供給します。

`hqeq ▸ hqg` は、等式 `q=5` を整除性 `q ∣ g` に代入し、`5 ∣ g` を作る dependent rewrite です。

## 冗長・重複箇所

`hqg` と `hqGN` の導出は対称的で、gcd の左右射影をそれぞれ書いています。局所補題として共通素因子の二つの整除性を組にして返すこともできますが、現在の二行は標準 API の対応が明瞭です。

`q=5` の証明は、`Nat.Prime.eq_of_dvd_of_natAbs_le` のような別経路よりも `Nat.dvd_prime` を使う現行形が直接的です。ただし式が長いため、

```lean
have hqeq : q = 5 := hq.eq_five_of_dvd hq5
```

のような DkMath 固有補題を作れば可読性は上がります。しかし用途がこの一箇所だけなら抽象化過多です。

## 最適化候補

- gcd 反証の定型部分を、`Nat.Coprime` を共通素因子不存在として扱う補題へ置き換えられる可能性があります。
- `q ∣ 5` から `q=5` を得る部分を、小さな局所補題へ分離すると本証明の二分岐構造がさらに見やすくなります。
- 本定理を一般素数 `p` と剰余項 `p*y^n` に抽象化することは可能ですが、`GN5` 固有の Reduction 読解という目的では現行の専用定理名が適切です。
- `Nat.Coprime g (GN5 g y)` を先に common-prime exclusion として証明し、最後にライブラリ補題で変換する別構成も Comparator 候補になります。

これらは未検証のリファクタリング案であり、Lean ビルドによる確認は本号では行っていません。

## 必要 Mathlib import と import 最適化候補

standalone 生成物は `import Mathlib` を使用しています。本定理が直接利用するのは、自然数の gcd・互いに素性・素数・整除性・冪に関する API、および DkMath 側の `GN5` と前号の補題です。

厳密な最小 import は未検証です。候補としては自然数の素数・gcd・整除性を提供する個別 Mathlib モジュールへ縮小できます。`ring`、`omega`、`norm_num` は本定理本体では使用せず、具体素数 `5` の確認に `decide` を使用します。ただし同一 `Reduction.lean` 内の前後の定理が別 tactic を必要とする可能性があるため、ファイル単位の import 最小化は宣言単体より広い監査が必要です。

## Comparator challenge 化

Comparator challenge に非常に適しています。主張は短い一方、証明方針には明確な比較軸があります。

- 現行の gcd 反証＋共通素因子抽出版。
- `Nat.Coprime` の素因子特徴付けを直接用いる版。
- `%` と合同式を中心にした版。
- `q ∣ 5` の枝を数値正規化で処理する版と、`Nat.dvd_prime` で構造的に処理する版。
- 二分岐を小補題へ分解する可読性重視版と、一つの term proof に圧縮する版。

評価軸は、前号の API を再利用しているか、例外素数 `5` の枝が明示されているか、互いに素性の矛盾が読み取りやすいか、具体数値 tactic への依存が小さいかです。

## 根拠と推測の区別

定理型、証明本体、宣言順、直後の `branchB_coprime_gap_GN5` は、リポジトリ内の `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/Reduction.lean` 生成区間を根拠とします。

既存の日英 PDF は FLT5 証明全体の narrative context を補いますが、本局所定理の最終的な形式的根拠は Lean ソースです。PDF 内で本宣言名そのものへの独立した詳細解説があるかは本号では確認できず、上記の役割説明は Lean の宣言順と後続利用から読んだものです。import 最小化と一般化案は未検証の提案です。

## 次に読むべき定理

`DkMath.FLT.Five.branchB_coprime_gap_GN5`

これは `CounterexamplePack` から得た

$$
\gcd(z-y,y)=1
$$

と Branch B 仮定

$$
5\nmid z-y
$$

を本定理へ代入し、

$$
\gcd\bigl(z-y,GN5(z-y,y)\bigr)=1
$$

を得る薄い接続定理です。一般的な因子分離原理を、実際の FLT5 反例候補の gap 座標へ適用します。
