# 0062 — `five_not_dvd_left_of_coprime_of_dvd_add`

## 1. 対象宣言

```lean
private theorem five_not_dvd_left_of_coprime_of_dvd_add
    {u v : ℕ} (hcop : Nat.Coprime u v) (h5sum : 5 ∣ u + v) :
    ¬ 5 ∣ u := by
  intro h5u
  have h5v : 5 ∣ v := (Nat.dvd_add_right h5u).mp h5sum
  exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 5) h5u h5v) hcop
```

本宣言は `private theorem` であり、`SignedFiveAdic` 層内部だけで使う補助補題である。

## 2. Lean の型

暗黙の自然数 `u v` に対して、

```lean
Nat.Coprime u v → 5 ∣ u + v → ¬ 5 ∣ u
```

を与える。

ここで `Nat.Coprime u v` は `gcd u v = 1` に相当し、結論 `¬ 5 ∣ u` は「5 は左成分 `u` を割らない」という否定命題である。

## 3. 数学的主張

数学的には極めて基本的な互いに素性の帰結である。

$$
\gcd(u,v)=1,
\qquad
5\mid(u+v)
$$

とする。もし $5\mid u$ なら、$5\mid(u+v)$ から差を取って $5\mid v$ も従う。すると 5 は $u,v$ の共通因子となり、$5>1$ なので $\gcd(u,v)=1$ に反する。したがって

$$
5\nmid u.
$$

本質は素数性ではなく「$1<5$」である。一般に $1<d$、$\gcd(u,v)=1$、$d\mid u+v$ なら、$d$ が一方を割ることはない。

## 4. FLT5 証明全体での役割

この補題は `SumGN5` の sum orientation を法 25 で評価する前処理である。

後続の `SumGN5_cast_mod25_eq_five` は

```lean
have h5u : ¬ 5 ∣ u :=
  five_not_dvd_left_of_coprime_of_dvd_add hcop h5sum
```

として本補題を直接利用する。続く右側対称版から `¬ 5 ∣ v` も得て、`u` と `v` の双方が 5 の倍数でないことを固定したうえで、`SumGN5 u v` の `ZMod 25` 上の値を 5 に絞り込む。

したがって役割は

```text
coprime(u,v) + 5 | (u+v)
          ↓
       5 ∤ u
          ↓
  mod-25 residual analysis
```

という局所的な five-adic 前処理である。

## 5. 直接依存する定義・補題

直接使っているものは次の通りである。

- `Nat.Coprime u v`
- `Nat.dvd_add_right`
- `Nat.not_coprime_of_dvd_of_dvd`
- `norm_num` による `(1 < 5)` の閉包

特に

```lean
(Nat.dvd_add_right h5u).mp h5sum
```

は、既知の `5 ∣ u` を使って

```lean
5 ∣ u + v ↔ 5 ∣ v
```

の必要な向きを取り出し、`h5v : 5 ∣ v` を作る。

## 6. 証明の流れ

証明は四段だけである。

1. `intro h5u` で結論の否定を仮定し、`5 ∣ u` を導入する。
2. `Nat.dvd_add_right h5u` と `h5sum` から `h5v : 5 ∣ v` を得る。
3. `5>1`、`5∣u`、`5∣v` から `u,v` は互いに素でないことを得る。
4. それを仮定 `hcop : Nat.Coprime u v` に適用して矛盾を閉じる。

証明木としては

```text
hcop : Coprime u v
h5sum : 5 | u+v
  assume h5u : 5 | u
       ↓ dvd_add_right
     h5v : 5 | v
       ↓ common divisor 5 > 1
  ¬ Coprime u v
       ↓ hcop
      False
```

である。

## 7. Lean 固有の処理

### 7.1 否定命題を `intro` で開く

結論は `¬ 5 ∣ u`、すなわち Lean 内部では

```lean
5 ∣ u → False
```

なので、`intro h5u` で通常の含意証明として開始できる。

### 7.2 `Nat.dvd_add_right` の向き

`Nat.dvd_add_right h5u` は、`u` が既に 5 で割れるという情報を固定して、和の可除性と残りの項の可除性を結び付ける。`.mp h5sum` により和から右項へ進む。

### 7.3 `Nat.not_coprime_of_dvd_of_dvd`

この補題は「1 より大きい共通因子が存在するなら互いに素でない」をそのまま提供する。5 が素数であることを使わず、

```lean
(by norm_num : 1 < 5)
```

だけを渡している点が重要である。

## 8. 冗長・重複箇所

直後には完全に左右対称な

```lean
five_not_dvd_right_of_coprime_of_dvd_add
```

があり、こちらは `Nat.dvd_add_left` を使う以外ほぼ同形である。

この二補題は数学的には一つの一般補題から導出できるため、コード上は意図的な左右対称の重複が存在する。

ただし現状の形には、後続証明で `h5u` と `h5v` をそれぞれ明示的な名前で取り出せるため、局所的な可読性という利点がある。

## 9. 最適化候補

第一候補は一般化である。例えば概念的には

```lean
lemma not_dvd_left_of_coprime_of_one_lt_of_dvd_add
    {d u v : ℕ}
    (hd : 1 < d)
    (hcop : Nat.Coprime u v)
    (hsum : d ∣ u + v) :
    ¬ d ∣ u
```

のような補題を用意すれば、5 固有の二補題を共通化できる。

第二候補は対称性利用である。右側版を左側版に `u` と `v` を交換して適用し、`Nat.Coprime.symm` と `Nat.add_comm` で済ませる設計も可能である。ただし、この程度の短い補題では現行の直接証明のほうが Lean の elaboration と読解の双方で素直である可能性が高い。

第三候補として、後続が常に左右両方の非可除性を必要とするなら

```lean
¬ 5 ∣ u ∧ ¬ 5 ∣ v
```

を一度に返す補題へまとめる案もある。

## 10. 必要 Mathlib import と import 最適化候補

対象ブランチで確認できる standalone artifact は

```lean
import Mathlib
```

を使用している。

本補題単独で必要なのは、少なくとも自然数の gcd / coprime / divisibility 関連定理と `norm_num` tactic である。元の分割 `DkMath/FLT/Five/SignedFiveAdic.lean` はこの博物館ブランチでは直接取得できなかったため、正確な最小 import は未確認である。

推測としては、自然数の gcd・coprime 定理を提供するモジュールと `Mathlib.Tactic.NormNum` 相当まで縮小可能性がある。ただし import 名そのものはビルド確認なしには断定しない。

## 11. Comparator challenge 化

適している。

課題としては、同じ型

```lean
{u v : ℕ} → Nat.Coprime u v → 5 ∣ u + v → ¬ 5 ∣ u
```

を固定し、次の実装を比較できる。

- 現行の `dvd_add_right` + `not_coprime_of_dvd_of_dvd`
- gcd を直接操作する証明
- 一般化補題を経由する証明
- 左右同時の非可除性補題から射影する証明

評価軸は、証明行数だけでなく、依存する補題数、対称版への再利用性、tactic 依存、Mathlib import の小ささがよい。

難度は低いが、`Nat.Coprime` API と可除性の加法補題を覚えるための良い micro challenge である。

## 12. 根拠と推測

確定根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された Lean コードである。そこでは本補題の直後に右側対称版、その後に `SumGN5_cast_mod25_eq_five` が置かれ、本補題を直接呼び出している。

既存の日英 PDF の具体的ページ対応は今回確認していないため、PDF に固有の説明・ページ番号は補っていない。import 最小化に関する記述も、分割元ファイルをこのブランチから直接取得できなかったため推測として区別した。

## 13. 次に読むべき定理

次は直後の private lemma

```lean
private theorem five_not_dvd_right_of_coprime_of_dvd_add
    {u v : ℕ} (hcop : Nat.Coprime u v) (h5sum : 5 ∣ u + v) :
    ¬ 5 ∣ v
```

である。

本号の完全な左右対称版を確認したあと、両者が合流する `SumGN5_cast_mod25_eq_five` へ進むのが依存順として自然である。
