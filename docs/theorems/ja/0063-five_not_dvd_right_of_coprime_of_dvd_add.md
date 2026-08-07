# 0063 — `five_not_dvd_right_of_coprime_of_dvd_add`

## 1. 対象宣言

```lean
private theorem five_not_dvd_right_of_coprime_of_dvd_add
    {u v : ℕ} (hcop : Nat.Coprime u v) (h5sum : 5 ∣ u + v) :
    ¬ 5 ∣ v := by
  intro h5v
  have h5u : 5 ∣ u := (Nat.dvd_add_left h5v).mp h5sum
  exact (Nat.not_coprime_of_dvd_of_dvd (by norm_num : 1 < 5) h5u h5v) hcop
```

本宣言は `private theorem` であり、`SignedFiveAdic` 層内部だけで用いられる補助補題である。0062 `five_not_dvd_left_of_coprime_of_dvd_add` の完全な左右対称版である。

## 2. Lean の型

暗黙の自然数 `u v` に対して、

```lean
Nat.Coprime u v → 5 ∣ u + v → ¬ 5 ∣ v
```

を与える。

`Nat.Coprime u v` は自然数上の互いに素性を表し、結論 `¬ 5 ∣ v` は「5 は右成分 `v` を割らない」という否定命題である。

## 3. 数学的主張

数学的には 0062 と同じ原理である。

$$
\gcd(u,v)=1,
\qquad
5\mid(u+v)
$$

とする。仮に $5\mid v$ なら、$5\mid(u+v)$ から $5\mid u$ が従う。したがって 5 は $u$ と $v$ の共通因子になる。しかし $5>1$ なので、これは $\gcd(u,v)=1$ に矛盾する。ゆえに

$$
5\nmid v.
$$

本質は 5 の素数性ではなく、共通因子として 1 より大きいことにある。一般には $1<d$、$\gcd(u,v)=1$、$d\mid u+v$ なら $d$ はどちらの成分も割れない。

## 4. FLT5 証明全体での役割

この補題は sum orientation の five-adic 解析へ入る直前に、右成分 `v` が 5 の倍数ではないことを固定する。

直後の `SumGN5_cast_mod25_eq_five` では、0062 と本号を並べて

```lean
have h5u : ¬ 5 ∣ u :=
  five_not_dvd_left_of_coprime_of_dvd_add hcop h5sum
have h5v : ¬ 5 ∣ v :=
  five_not_dvd_right_of_coprime_of_dvd_add hcop h5sum
```

とし、`u` と `v` の双方について 5 非可除性を確保する。その情報を使って `SumGN5 u v` の法 25 における値を 5 に固定する。

したがって 0062–0063 の二本は、

```text
Coprime u v + 5 | (u+v)
          ↓
   5 ∤ u  and  5 ∤ v
          ↓
  SumGN5 mod 25 analysis
```

という前処理対を形成する。本号単独では小さいが、後続の residual valuation へ渡す入力条件の半分を担う。

## 5. 直接依存する定義・補題

証明が直接使うものは次の通りである。

- `Nat.Coprime u v`
- `Nat.dvd_add_left`
- `Nat.not_coprime_of_dvd_of_dvd`
- `norm_num` による `(1 < 5)` の証明

特に

```lean
(Nat.dvd_add_left h5v).mp h5sum
```

は既知の `5 ∣ v` を固定し、

```lean
5 ∣ u + v ↔ 5 ∣ u
```

の必要な向きを使って `h5u : 5 ∣ u` を取り出す。

## 6. 証明の流れ

証明は 0062 と鏡像である。

1. `intro h5v` で否定結論を開き、`5 ∣ v` を仮定する。
2. `Nat.dvd_add_left h5v` と `h5sum` から `h5u : 5 ∣ u` を得る。
3. `1 < 5`、`5 ∣ u`、`5 ∣ v` から `u,v` が互いに素でないことを得る。
4. それを `hcop : Nat.Coprime u v` に適用して `False` を得る。

証明木は

```text
hcop : Coprime u v
h5sum : 5 | u+v
  assume h5v : 5 | v
       ↓ dvd_add_left
     h5u : 5 | u
       ↓ common divisor 5 > 1
  ¬ Coprime u v
       ↓ hcop
      False
```

である。

## 7. Lean 固有の処理

### 7.1 `¬ P` は `P → False`

結論 `¬ 5 ∣ v` は Lean では `5 ∣ v → False` なので、証明は `intro h5v` から始まる。

### 7.2 `Nat.dvd_add_left` の向き

0062 が `Nat.dvd_add_right h5u` を用いたのに対し、本号では `Nat.dvd_add_left h5v` を使う。左右の既知項が入れ替わっただけで、証明構造は完全に対称である。

### 7.3 共通因子から `Nat.Coprime` を否定する

```lean
Nat.not_coprime_of_dvd_of_dvd
```

へ渡しているのは

```lean
(by norm_num : 1 < 5)
```

と二つの可除性証明である。`Nat.Prime 5` は不要であり、この補題が five-adic 専用に見えて実際にはより一般的な gcd 事実であることが分かる。

## 8. 冗長・重複箇所

最大の重複は 0062 との左右対称性である。両者は

- `u` と `v` の交換
- `dvd_add_right` と `dvd_add_left` の交換

だけで同じ証明を繰り返している。

数学的には一つの一般補題から左右を同時に導ける。しかし後続 `SumGN5_cast_mod25_eq_five` では `h5u` と `h5v` を別名で直ちに利用するため、二本を明示しておくことは局所的な可読性を高める。

## 9. 最適化候補

第一候補は 0062 を再利用する対称化である。概念的には本号を

```lean
have := five_not_dvd_left_of_coprime_of_dvd_add hcop.symm ?_
```

の形へ寄せ、`Nat.add_comm` で和を交換する方法がある。ただし短い補題に対して rewrite を追加するため、現行の直接証明より必ずしも読みやすくはならない。

第二候補は一般化である。例えば

```lean
lemma not_dvd_of_coprime_of_one_lt_of_dvd_add
    {d u v : ℕ}
    (hd : 1 < d)
    (hcop : Nat.Coprime u v)
    (hsum : d ∣ u + v) :
    ¬ d ∣ u ∧ ¬ d ∣ v
```

のように左右を一度に返せば、0062 と本号を一つの共通事実へまとめられる。

第三候補は、後続 consumer に合わせた private helper として

```lean
five_not_dvd_both_of_coprime_of_dvd_add
```

を用意し、`SumGN5_cast_mod25_eq_five` 側で一度だけ分解する設計である。

ただし現行コードは短く、使用 API も標準的で、保守上の問題は小さい。

## 10. 必要 Mathlib import と import 最適化候補

対象ブランチで確認できる生成済み standalone artifact は

```lean
import Mathlib
```

を使用している。

本補題単独で必要なのは、自然数の gcd / coprime / divisibility API と `norm_num` tactic である。生成 artifact の manifest では元ソースが `DkMath/FLT/Five/SignedFiveAdic.lean` であることまで確認できるが、この博物館ブランチから分割元ファイルそのものは直接取得できなかったため、正確な最小 import 行は未確認である。

推測としては `Nat.Coprime` と加法可除性補題を提供する自然数 gcd 系モジュール、および `Mathlib.Tactic.NormNum` 相当まで縮小できる可能性が高い。ただし Lean ビルドを行っていないため import 名は断定しない。

## 11. Comparator challenge 化

適している。0062 と対にすると特に良い micro challenge になる。

固定する型は

```lean
{u v : ℕ} → Nat.Coprime u v → 5 ∣ u + v → ¬ 5 ∣ v
```

で、比較候補は次である。

- 現行の `dvd_add_left` + `not_coprime_of_dvd_of_dvd`
- 0062 を `u ↔ v` 交換で再利用する証明
- gcd を直接操作する証明
- 左右同時補題から右成分だけ射影する証明

評価軸として、証明行数、依存補題数、対称性の再利用、elaboration の安定性、import の小ささが使える。

## 12. 根拠と推測

確定根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` である。生成ヘッダには `DkMath/FLT/Five/SignedFiveAdic.lean` が ordered source module として記録され、本補題の完全な Lean 本体と、その直後の `SumGN5_cast_mod25_eq_five` における直接利用を確認した。

既存の日英 PDF の具体的ページ対応は今回確認していないため、PDF 固有の説明やページ番号は推測で補っていない。import 最小化についても、分割元ファイルを直接取得できていないため推測として明示した。

## 13. 次に読むべき定理

次は直後の private theorem

```lean
private theorem SumGN5_cast_mod25_eq_five
    {u v : ℕ} (hcop : Nat.Coprime u v) (h5sum : 5 ∣ u + v) :
    (SumGN5 u v : ZMod 25) = 5
```

である。

0062 と本号で得た `5 ∤ u`、`5 ∤ v` が初めて合流し、`SumGN5` の法 25 residual を正確に 5 へ固定する段階である。依存順として次に読むべき自然な宣言である。
