# 0047 — `five_not_dvd_GN5_of_five_not_dvd_gap`

## 1. 宣言

```lean
theorem five_not_dvd_GN5_of_five_not_dvd_gap
    {g y : ℕ} (h5g : ¬ 5 ∣ g) :
    ¬ 5 ∣ GN5 g y := by
  intro h5GN
  have hdecomp := GN5_eq_g_pow_four_add_five_mul g y
  have h5tail :
      5 ∣ 5 * (g ^ 3 * y + 2 * g ^ 2 * y ^ 2 + 2 * g * y ^ 3 + y ^ 4) :=
    dvd_mul_of_dvd_left (dvd_refl 5) _
  rw [hdecomp] at h5GN
  have h5g4 : 5 ∣ g ^ 4 := (Nat.dvd_add_left h5tail).mp h5GN
  exact h5g ((by decide : Nat.Prime 5).dvd_of_dvd_pow h5g4)
```

完全修飾名は `DkMath.FLT.Five.five_not_dvd_GN5_of_five_not_dvd_gap` である。

## 2. Lean の型

```lean
{g y : ℕ} → (¬ 5 ∣ g) → ¬ 5 ∣ GN5 g y
```

`g` と `y` は暗黙引数であり、唯一の明示的仮定 `h5g` は gap `g` が 5 で割り切れないことを表す。結論は residual factor `GN5 g y` も 5 で割り切れないという否定命題である。

## 3. 数学的主張

既刊 0009 の五進分解は

$$
GN5(g,y)=g^4+5\bigl(g^3y+2g^2y^2+2gy^3+y^4\bigr)
$$

を与える。したがって

$$
GN5(g,y)\equiv g^4\pmod 5
$$

である。

もし $5\mid GN5(g,y)$ なら、右辺の第二項は自明に 5 の倍数なので $5\mid g^4$ となる。5 は素数だから $5\mid g$ が従い、仮定 $5\nmid g$ と矛盾する。ゆえに

$$
5\nmid g \Longrightarrow 5\nmid GN5(g,y)
$$

が成立する。

## 4. 証明全体での役割

この補題は Branch B、すなわち gap が 5 で割り切れない側で、第五冪 body

$$
Body5(g,y)=g\,GN5(g,y)
$$

のどちらの因子にも 5 が入らないことを保証する片側である。

直後の `five_not_dvd_x_of_branchB` では、Fermat 方程式から `Body5 (z-y) y = x^5` を得た後、もし $5\mid x$ なら $5\mid Body5(z-y,y)$ となる。素数 5 による積の整除を gap 側と `GN5` 側へ分岐し、gap 側は Branch B 仮定で、`GN5` 側は本補題で排除する。そのため本補題は、signed Branch A ルーティングに入る前の五進的な入口ガードである。

## 5. 直接依存する定義・補題

1. `GN5`

   gap 座標における第五円分因子を表す定義。

2. `GN5_eq_g_pow_four_add_five_mul`

   `GN5` を $g^4+5K$ の形へ展開する既刊 0009 の補題。

3. `dvd_mul_of_dvd_left`

   $5\mid5$ から $5\mid5K$ を構成する一般整除補題。

4. `Nat.dvd_add_left`

   加法の一方が割り切れるとき、和の整除と他方の整除を移送する補題。ここでは $5\mid5K$ と $5\mid(g^4+5K)$ から $5\mid g^4$ を取り出す。

5. `Nat.Prime.dvd_of_dvd_pow`

   素数が冪を割るなら底を割るという補題。`(by decide : Nat.Prime 5)` と組み合わせて使う。

## 6. 証明の流れ

1. 結論が否定なので `intro h5GN` により反対仮定 $5\mid GN5(g,y)$ を導入する。
2. `GN5_eq_g_pow_four_add_five_mul g y` を `hdecomp` として保存する。
3. 残余項 $5K$ が 5 で割り切れることを `h5tail` として構成する。
4. `rw [hdecomp] at h5GN` により、反対仮定を $5\mid(g^4+5K)$ へ書き換える。
5. `Nat.dvd_add_left` によって $5\mid g^4$ を得る。
6. 5 の素数性から $5\mid g$ を得て `h5g` に適用し、矛盾を閉じる。

## 7. Lean 固有の処理

### 7.1 否定は関数

`¬ 5 ∣ GN5 g y` は `(5 ∣ GN5 g y) → False` なので、証明は `intro h5GN` から始まる。最後も `h5g` を、導出した `5 ∣ g` に適用して `False` を得ている。

### 7.2 `have hdecomp := ...` による型推論

`hdecomp` の型注釈は省略され、定理適用から完全な等式型が推論される。この等式は証明対象そのものではなく、局所的な書換規則として使われる。

### 7.3 `_` プレースホルダ

```lean
dvd_mul_of_dvd_left (dvd_refl 5) _
```

の `_` は右側の乗数全体を elaborator に推論させる。式が長いため、同じ多項式をもう一度記述せずに済む。

### 7.4 `rw ... at` による仮定側の正規化

目標ではなく `h5GN` の内部だけを五進分解へ書き換える。これにより、以後の整除推論が加法形に対して直接行える。

### 7.5 `by decide` による具体的素数性

`Nat.Prime 5` は決定可能な閉命題なので、証明項を `by decide` で生成している。一般の素数変数を扱う補題ではなく、例外素数 5 に特化した実装である。

## 8. 冗長・重複箇所

証明は短く、数学的な重複はほぼない。ただし次の局所的冗長性はある。

- `hdecomp` を一度名前付けしてから一回だけ `rw` に使っている。
- 長い residual polynomial が定理の右辺と `h5tail` の型の双方に現れる。
- `Nat.Prime 5` の `by decide` は後続の五進補題でも繰り返される可能性がある。

これらはいずれも可読性との交換条件であり、現行証明は各推論段階が明示されている利点が大きい。

## 9. 最適化候補

### 9.1 分解等式を直接書き換える

`hdecomp` を省き、次のように直接書ける可能性がある。

```lean
rw [GN5_eq_g_pow_four_add_five_mul] at h5GN
```

ただし暗黙の引数推論と書換対象の安定性を考えると、現行の名前付けは監査しやすい。

### 9.2 合同式または `%` による証明

`GN5 g y % 5 = g ^ 4 % 5` を先に補題化すれば、剰余算術として短く表現できる。ただし現行証明は整除 API だけで完結し、後続の `dvd_mul` 推論と語彙が統一されている。

### 9.3 一般素数版

次の一般補題を抽出できる。

```lean
Nat.Prime p → n = a ^ k + p * t → ¬ p ∣ a → ¬ p ∣ n
```

しかし本開発で重要なのは円分指数と一致する特別な素数 5 であるため、抽象化はコード量を増やすだけになる可能性がある。

### 9.4 残余項の局所名

長い多項式を `let K := ...` と置けば視覚的には簡潔になるが、`simp [K]` や `dsimp [K]` が追加で必要になり、Lean 証明としては必ずしも短くならない。

## 10. 必要 Mathlib import と import 最適化候補

生成済み standalone ソースは `import Mathlib` で全体を構成しているため、この宣言が現状の成果物で利用可能であることは確認できる。

本定理が直接必要とする機能は概ね次である。

- 自然数の整除と加法整除補題
- `Nat.Prime.dvd_of_dvd_pow`
- `decide` による `Nat.Prime 5` の証明
- 上流の `GN5` と `GN5_eq_g_pow_four_add_five_mul`

分割元 `SignedBranchA.lean` の正確な import 行はこのリポジトリの公開成果物から直接取得できなかったため、最小 import の断定は避ける。推測としては、上流の Branch A／GN5 モジュールを import すれば Mathlib の必要部分は推移的に導入される。import 最適化を行うなら、元 `dkmath` リポジトリの分割モジュールを基準に `lake env lean` または import 監査ツールで確認すべきであり、本記事ではビルドを実行していない。

## 11. Comparator challenge 化の可否

 **適している。** 

課題としては、次の宣言と五進分解だけを与え、整除 API を使って証明させる形がよい。

```lean
theorem challenge
    {g y : ℕ} (h5g : ¬ 5 ∣ g) :
    ¬ 5 ∣ GN5 g y := by
  sorry
```

比較点は次の通りである。

- 加法整除補題を正しい向きで使えるか。
- `Nat.Prime.dvd_of_dvd_pow` によって $5\mid g^4$ から $5\mid g$ を得られるか。
- `norm_num` や巨大な展開に逃げず、既存の構造補題を再利用できるか。
- 否定命題を関数として自然に処理できるか。

短いが、Lean の整除 API、書換え、具体的素数性を同時に問える良い基礎 challenge である。

## 12. 根拠と留保

宣言名、型、証明本体、直後の宣言、および `SignedBranchA.lean` に属することは、対象ブランチの生成済み `Flt5DkMath/FLT5StandAlone.lean` で確認した。数学的説明はその kernel-checked Lean コードを主根拠とする。

既存 PDF は証明全体の signed five-adic／golden descent という物語的背景を補う資料であり、本補題の逐語的証明より Lean ソースを優先した。分割元ファイルの正確な import 行は確認できなかったため、その箇所は推測として明示した。

## 13. 次に読むべき定理

次は

```lean
DkMath.FLT.Five.five_not_dvd_x_of_branchB
```

を読むべきである。この定理は Branch B 候補で $5\nmid x$ を示す。Fermat 方程式が与える完全第五冪 body に 5 が入ると仮定し、積 `gap * GN5` のどちらへ 5 が入るかを素数性で分岐する。gap 側を Branch B 仮定で、本号の `GN5` 側を本補題で排除するため、本号の直接的な consumer である。
