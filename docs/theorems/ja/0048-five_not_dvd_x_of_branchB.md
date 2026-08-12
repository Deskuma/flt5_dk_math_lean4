# 0048 — `five_not_dvd_x_of_branchB`

## 1. 宣言

```lean
theorem five_not_dvd_x_of_branchB
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    ¬ 5 ∣ x := by
  intro h5x
  have hyz : y ≤ z := (right_lt_of_fermat5Equation hPack.hx hPack.hEq).le
  have hbody : Body5 (z - y) y = x ^ 5 :=
    body5_eq_fifth_power_of_fermat hyz hPack.hEq
  have h5x5 : 5 ∣ x ^ 5 := h5x.trans (dvd_pow_self x (by decide))
  have h5body : 5 ∣ Body5 (z - y) y := by
    rw [hbody]
    exact h5x5
  unfold Body5 at h5body
  rcases (by decide : Nat.Prime 5).dvd_mul.mp h5body with h5gap | h5GN
  · exact hBranch h5gap
  · exact (five_not_dvd_GN5_of_five_not_dvd_gap hBranch) h5GN
```

完全修飾名は `DkMath.FLT.Five.five_not_dvd_x_of_branchB` である。

## 2. Lean の型

```lean
{x y z : ℕ} →
CounterexamplePack x y z →
(¬ 5 ∣ z - y) →
¬ 5 ∣ x
```

原始的な正の Fermat 反例候補 `hPack` と Branch B 条件 `hBranch` を受け取り、第一座標 `x` が 5 で割り切れないことを返す。

## 3. 数学的主張

`CounterexamplePack x y z` から

$$
x^5+y^5=z^5
$$

があり、Branch B 条件は

$$
5\nmid(z-y)
$$

である。Fermat 方程式を gap 座標へ移すと

$$
Body5(z-y,y)=(z-y)GN5(z-y,y)=x^5
$$

となる。

仮に $5\mid x$ なら $5\mid x^5$ であり、したがって

$$
5\mid (z-y)GN5(z-y,y)
$$

である。5 は素数なので、

$$
5\mid(z-y)
$$

または

$$
5\mid GN5(z-y,y)
$$

のどちらかである。前者は Branch B 仮定に反し、後者は既刊 0047 `five_not_dvd_GN5_of_five_not_dvd_gap` に反する。ゆえに $5\nmid x$ である。

## 4. 証明全体での役割

この補題は signed Branch A ルーティングの前処理である。Branch B では gap と residual の双方が 5 で割れないことから、Fermat 方程式の第五冪側 `x^5`、したがって底 `x` にも 5 が入らないことを確定する。

後続の剰余・符号分岐では、第五冪が法 5 で底に一致することや、どちらの差 `z-y` / `z-x` が 5 で割れるかを整理する。本補題はその際に `x` 自身が例外素数 5 を含まないことを保証する局所ガードである。

## 5. 直接依存する定義・補題

1. `CounterexamplePack`

   正値、原始性、Fermat 方程式を保持する構造体。

2. `right_lt_of_fermat5Equation`

   `hPack.hx` と `hPack.hEq` から $y<z$、したがって $y\le z$ を得る。

3. `Body5`

   `Body5 g y = g * GN5 g y` と定義された第五冪 body。

4. `body5_eq_fifth_power_of_fermat`

   Fermat 方程式から `Body5 (z-y) y = x^5` を与える bridge。

5. `dvd_pow_self`

   $x\mid x^5$ を与え、`h5x : 5 ∣ x` と推移させて $5\mid x^5$ を得る。

6. `Nat.Prime.dvd_mul`

   素数 5 が積を割るとき、どちらか一方の因子を割るという分岐を与える。

7. `five_not_dvd_GN5_of_five_not_dvd_gap`

   Branch B 条件から $5\nmid GN5(z-y,y)$ を与える既刊 0047。

## 6. 証明の流れ

1. 否定結論なので `intro h5x` で $5\mid x$ を仮定する。
2. `right_lt_of_fermat5Equation` から `hyz : y ≤ z` を得る。
3. `body5_eq_fifth_power_of_fermat` により `Body5 (z-y) y = x^5` を得る。
4. `h5x` と `dvd_pow_self` から $5\mid x^5$ を得る。
5. `hbody` で書き換え、$5\mid Body5(z-y,y)$ を得る。
6. `Body5` を展開し、素数 5 の `dvd_mul` で gap 側と `GN5` 側へ場合分けする。
7. gap 側は `hBranch`、`GN5` 側は既刊 0047 で矛盾させる。

## 7. Lean 固有の処理

### 7.1 否定命題を関数として扱う

結論 `¬ 5 ∣ x` は `(5 ∣ x) → False` なので、`intro h5x` で開始する。各分岐も否定仮定 `hBranch` または既刊補題の否定結論へ整除証明を適用して閉じる。

### 7.2 `.le` による狭い順序変換

`right_lt_of_fermat5Equation ...` の結論は `y < z` であり、末尾の `.le` により `y ≤ z` へ変換している。これは自然数減算を使う `body5_eq_fifth_power_of_fermat` の前提に合わせる処理である。

### 7.3 整除の推移

```lean
h5x.trans (dvd_pow_self x (by decide))
```

は $5\mid x$ と $x\mid x^5$ を合成する。`by decide` は指数 5 が 0 でないという `dvd_pow_self` の側条件を解決する。

### 7.4 `unfold` 後の素数積分岐

`Body5` は抽象名のままでは積として見えないため、`unfold Body5 at h5body` で `5 ∣ (z-y) * GN5 ...` へ露出させる。その後、`Nat.Prime.dvd_mul.mp` が和型の二分岐を返し、`rcases ... with h5gap | h5GN` で処理する。

### 7.5 具体的素数性の `by decide`

`Nat.Prime 5` は閉じた決定可能命題なので `(by decide : Nat.Prime 5)` で供給される。

## 8. 冗長・重複箇所

証明は依存関係が明瞭で、実質的な重複は少ない。ただし次は局所的に圧縮可能である。

- `hbody` と `h5body` を別々に置かず、一つの `simpa [Body5, hbody]` へ寄せる余地がある。
- `Nat.Prime 5` の `by decide` は周辺補題でも繰り返される。
- 最終二分岐は `exact` だけなので、`rcases` 後を `exact Or.elim ...` 形式へ畳むこともできる。

ただし現行形は、方程式 bridge、第五冪への整除移送、積の素数分岐という三つの数学的段階を明示しており、博物館的な可読性に優れる。

## 9. 最適化候補

### 9.1 `simpa` による body 整除の直接構成

`h5body` は次のように短縮できる可能性がある。

```lean
have h5body : 5 ∣ Body5 (z - y) y := by
  simpa [hbody] using h5x5
```

ただし等式の向きに依存するため、現行の `rw [hbody]` は安定して読みやすい。

### 9.2 `Body5` 専用の素数分岐補題

頻出するなら、

```lean
Nat.Prime p → p ∣ Body5 g y → p ∣ g ∨ p ∣ GN5 g y
```

を抽出できる。しかし現状では `unfold Body5` と標準 API だけで十分短い。

### 9.3 5 専用素数証明の共有

`five_prime : Nat.Prime 5` を局所定理として共有すれば `by decide` の重複を減らせる。ただし閉命題の `by decide` は明快で、共有名を増やすほどの利益は小さい。

## 10. 必要 Mathlib import と import 最適化候補

生成済み `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用しており、本定理がその環境で成立することは確認できる。

直接必要な機能は概ね次である。

- 自然数の順序と減算
- 自然数の整除推移、`dvd_pow_self`
- `Nat.Prime.dvd_mul`
- `decide` による具体的命題の証明
- 上流の `CounterexamplePack`、`Body5`、Fermat bridge、0047 の補題

本宣言は生成物上で `SignedBranchA.lean` 部分に属する。分割元モジュールの正確な import 行はこのリポジトリでは取得できなかったため、最小 import は未確認である。推測としては Branch A / Provider / GN5 系の上流モジュールが推移的に必要機能を導入する。import 最適化は元 `dkmath` の分割ソースで個別ビルドまたは import 監査を行って確認すべきであり、本作業では Lean ビルドを実行していない。

## 11. Comparator challenge 化の可否

 **適している。** 

```lean
theorem challenge
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    ¬ 5 ∣ x := by
  sorry
```

比較点は次である。

- Fermat 方程式を `Body5 = x^5` へ正規化できるか。
- $5\mid x$ から $5\mid x^5$ を整除推移で構成できるか。
- `Body5` を展開して `Nat.Prime.dvd_mul` を使えるか。
- 二分岐を Branch B 仮定と 0047 の補題で正しく閉じられるか。
- `omega` や全面展開に逃げず、既存 bridge を再利用できるか。

複数の既刊補題を短い consumer 証明へ合成するため、依存追跡と Lean API 運用の双方を測れる良い challenge である。

## 12. 根拠と留保

宣言名、型、証明本体、`SignedBranchA.lean` に属すること、および直後の宣言が `pow_five_mod_five` であることは、対象ブランチの生成済み `Flt5DkMath/FLT5StandAlone.lean` で確認した。数学的説明はこの kernel-checked Lean コードを主根拠とする。

既存の日英 PDF は signed five-adic / golden descent の全体文脈を補う資料として扱い、個別宣言の厳密な内容では Lean ソースを優先した。分割元 `SignedBranchA.lean` の正確な import 行は未確認であり、その点は推測として明示した。

## 13. 次に読むべき定理

次は

```lean
DkMath.FLT.Five.pow_five_mod_five
```

を読むべきである。この定理は

$$
n^5\bmod 5=n\bmod 5
$$

を示し、第五冪 Fermat 方程式を法 5 上で底の合同式へ落とす。Branch A / Branch B の signed routing を剰余計算で整理する次の基礎補題である。
