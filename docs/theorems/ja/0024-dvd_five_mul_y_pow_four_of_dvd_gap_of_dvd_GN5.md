# 0024 — `dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5`

## Lean の型

```lean
theorem dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5
    {g y q : ℕ} (hqg : q ∣ g) (hqGN : q ∣ GN5 g y) :
    q ∣ 5 * y ^ 4
```

任意の自然数 `g`, `y`, `q` について、`q` が gap `g` と `GN5 g y` の双方を割るなら、`q` は例外項 `5 * y ^ 4` も割ることを示します。`q` の素数性や `g` と `y` の互いに素性は、この補題自体では仮定しません。

## 数学的主張

既出の gap 分解

$$
GN5(g,y)=g\left(g^3+5g^2y+10gy^2+10y^3\right)+5y^4
$$

を考えます。`q ∣ g` なら第一項全体は `q` の倍数です。さらに `q ∣ GN5(g,y)` なので、和から第一項を除いた剰余も `q` の倍数となり、

$$
q\mid 5y^4
$$

が従います。

これは合同式

$$
GN5(g,y)\equiv 5y^4\pmod g
$$

を、一般の共通因子 `q` に対する整除性として取り出した補題です。

## 証明全体での役割

この定理は、gap と `GN5` の共通因子を例外素数 `5` へ絞り込む Reduction 層の合同解析入口です。

後続の `coprime_gap_GN5_of_coprime_of_five_not_dvd` では、`g` と `GN5(g,y)` の gcd に素因子 `q` があると仮定します。本定理により `q ∣ 5y^4` を得て、素数性から次の二分岐へ進みます。

1. `q ∣ 5` なら `q=5` であり、`¬ 5 ∣ g` と矛盾する。
2. `q ∣ y^4` なら `q ∣ y` であり、`Nat.Coprime g y` と矛盾する。

したがって、`g` と `y` が互いに素で、かつ `5 ∤ g` なら、gap と `GN5` は互いに素になります。本定理は、その反証の中央で「共通因子の行き先は `5` または `y` しかない」と固定する局所ルーティング補題です。

## 直接依存する定義・補題

- `GN5`
- `GN5_eq_gap_mul_add_five_mul_y_pow_four`
- `dvd_mul_of_dvd_left`
- `Nat.dvd_add_right`

数学的内容の中心は `GN5_eq_gap_mul_add_five_mul_y_pow_four` です。その他は、既知の整除性を積へ持ち上げ、和の一方の項を除去する標準的な自然数整除性 API です。

## 証明の流れ

Lean 本体は次の通りです。

```lean
have hdecomp :
    GN5 g y =
      g * (g ^ 3 + 5 * g ^ 2 * y + 10 * g * y ^ 2 + 10 * y ^ 3) +
        5 * y ^ 4 := by
  exact GN5_eq_gap_mul_add_five_mul_y_pow_four g y
have hqPrefix :
    q ∣ g * (g ^ 3 + 5 * g ^ 2 * y + 10 * g * y ^ 2 + 10 * y ^ 3) :=
  dvd_mul_of_dvd_left hqg _
rw [hdecomp] at hqGN
exact (Nat.dvd_add_right hqPrefix).mp hqGN
```

1. 既存恒等式を `hdecomp` として局所名に固定する。
2. `q ∣ g` を `dvd_mul_of_dvd_left` で多項式前半全体の整除性へ持ち上げる。
3. `hqGN` の中で `GN5 g y` を分解形へ書き換える。
4. `Nat.dvd_add_right hqPrefix` の順方向を使い、和全体の整除性から右項 `5*y^4` の整除性を取り出す。

## Lean 固有の処理

`Nat.dvd_add_right hqPrefix` は、左項が `q` で割れることを既知として、

```lean
q ∣ a + b ↔ q ∣ b
```

という形の同値を返します。ここでは `.mp` によって、書き換え後の `hqGN : q ∣ prefix + 5*y^4` から目標を得ています。

`hdecomp` を別途作るのは数学的には冗長に見えますが、書き換え対象の式を明示し、後続の `rw [hdecomp] at hqGN` を安定させます。また `dvd_mul_of_dvd_left hqg _` の `_` は、第二因子を目標型から Lean に推論させるプレースホルダーです。

この証明では減算を使わず、和に対する整除性同値で剰余項を取り出しています。自然数上で切り捨て減算を避けるため、Lean にとっても堅牢な書き方です。

## 冗長・重複箇所

`hdecomp` は既存定理をそのまま再型付けしています。次のように直接書き換える短縮案はあります。

```lean
rw [GN5_eq_gap_mul_add_five_mul_y_pow_four] at hqGN
exact (Nat.dvd_add_right (dvd_mul_of_dvd_left hqg _)).mp hqGN
```

ただし、長い多項式を含む目標では中間名 `hqPrefix` が証明の意味を明確にします。現行証明は行数より監査性を優先した形であり、実質的な重複は小さいです。

定理名は長いものの、前提と結論を完全に表しています。namespace を導入して `GN5.dvd_exceptional_term` のように短縮する案もありますが、宣言探索時の明示性との交換条件になります。

## 最適化候補

- `hdecomp` を `rw [GN5_eq_gap_mul_add_five_mul_y_pow_four] at hqGN` に統合して証明を短縮できる可能性があります。
- 同型の一般補題「`n = g*A+r`、`q∣g`、`q∣n` なら `q∣r`」を抽象化できます。ただし Mathlib の `Nat.dvd_add_right` がほぼその役割を担うため、DkMath 固有補題を追加する利益は限定的です。
- 後続用途が合同式中心なら、`GN5 g y % g = (5*y^4) % g` の剰余版を併設する案があります。しかし現在の素因子反証では整除性版の方が直接的です。
- 定理の引数 `q` は素数に限らないため、一般因子に対する再利用性を保持する現行型が適切です。ここで `Nat.Prime q` を追加する最適化は不要です。

## 必要 Mathlib import と import 最適化候補

standalone 生成物は `import Mathlib` を使用しています。本定理が直接必要とする機能は、自然数の冪・加法・乗法・整除性、`dvd_mul_of_dvd_left`、`Nat.dvd_add_right`、および DkMath 側の `GN5` と gap 分解定理です。

元の分割モジュールに対する厳密な最小 import はこの記事ではビルド検証していません。自然数整除性と基本代数を提供する個別 Mathlib モジュールへ縮小できる可能性はありますが、未検証の import 最適化案です。`ring` や `omega` は本定理の証明では直接使用しませんが、依存する gap 分解定理の構築側では `ring` が必要です。

## Comparator challenge 化

小規模で明瞭な Comparator challenge に適しています。

比較候補は次の通りです。

- 現行の `Nat.dvd_add_right` を使う構造的証明。
- 整除性の witness をすべて展開し、代数計算で剰余項の witness を構成する証明。
- `%` による合同式へ移してから整除性へ戻す証明。
- `hdecomp` と `hqPrefix` を保持する監査重視版と、二行へ圧縮した短縮版。

評価軸は、自然数減算を避けているか、既存 API を適切に使っているか、長い多項式に対する可読性、後続の素因子分岐へ接続しやすいかです。witness 展開版や剰余版は、現行証明より複雑になる可能性が高いです。

## 根拠と推測の区別

定理型、証明本体、宣言順、直後の `coprime_gap_GN5_of_coprime_of_five_not_dvd` での利用は、リポジトリ内の `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/Reduction.lean` 生成区間を根拠とします。

既存の日本語・英語 PDF は FLT5 証明全体の文脈を補う資料ですが、本記事の形式的根拠は Lean ソースです。import 最小化、namespace 化、剰余版 API の追加は未検証の提案です。

## 次に読むべき定理

`DkMath.FLT.Five.coprime_gap_GN5_of_coprime_of_five_not_dvd`

これは、

$$
\gcd(g,y)=1,\qquad 5\nmid g
$$

のもとで、

$$
\gcd\bigl(g,GN5(g,y)\bigr)=1
$$

を示します。本号の `q ∣ 5y^4` を素数の積整除分岐へ渡し、共通素因子が `5` または `y` に由来する二つの可能性をそれぞれ排除する、本格的な共通因子反証です。