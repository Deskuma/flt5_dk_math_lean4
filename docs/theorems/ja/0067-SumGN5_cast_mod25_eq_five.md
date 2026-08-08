# 0067 — `SumGN5_cast_mod25_eq_five`

## Lean の型

```lean
private theorem SumGN5_cast_mod25_eq_five
    {u v : ℕ} (hcop : Nat.Coprime u v) (h5sum : 5 ∣ u + v) :
    (SumGN5 u v : ZMod 25) = 5 := by
  have h5u : ¬ 5 ∣ u :=
    five_not_dvd_left_of_coprime_of_dvd_add hcop h5sum
  have h5v : ¬ 5 ∣ v :=
    five_not_dvd_right_of_coprime_of_dvd_add hcop h5sum
  by_cases h : v ≤ u
  · rw [SumGN5, if_pos h]
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h
    subst u
    rcases h5sum with ⟨k, hk⟩
    have hcarrier : d + 2 * v = 5 * k := by omega
    have hcarrierZ :
        (d : ZMod 25) + 2 * (v : ZMod 25) = 5 * (k : ZMod 25) := by
      have hcast := congrArg (fun n : ℕ => (n : ZMod 25)) hcarrier
      simpa using hcast
    have hdZ : (d : ZMod 25) = 5 * (k : ZMod 25) - 2 * (v : ZMod 25) := by
      exact eq_sub_of_add_eq hcarrierZ
    rcases fourth_power_zmod25_decomposition h5v with ⟨q, hq⟩
    simp only [Nat.add_sub_cancel_left]
    push_cast
    rw [hdZ, hq]
    ring_nf
    rw [hq]
    ring_nf
    simp only [show (25 : ZMod 25) = 0 by decide,
      show (50 : ZMod 25) = 0 by decide,
      show (250 : ZMod 25) = 0 by decide,
      show (625 : ZMod 25) = 0 by decide,
      mul_zero, add_zero, sub_zero]
  · rw [SumGN5, if_neg h]
    have huv : u ≤ v := Nat.le_of_not_ge h
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le huv
    subst v
    rcases h5sum with ⟨k, hk⟩
    have hcarrier : d + 2 * u = 5 * k := by omega
    have hcarrierZ :
        (d : ZMod 25) + 2 * (u : ZMod 25) = 5 * (k : ZMod 25) := by
      have hcast := congrArg (fun n : ℕ => (n : ZMod 25)) hcarrier
      simpa using hcast
    have hdZ : (d : ZMod 25) = 5 * (k : ZMod 25) - 2 * (u : ZMod 25) := by
      exact eq_sub_of_add_eq hcarrierZ
    rcases fourth_power_zmod25_decomposition h5u with ⟨q, hq⟩
    simp only [Nat.add_sub_cancel_left]
    push_cast
    rw [hdZ, hq]
    ring_nf
    rw [hq]
    ring_nf
    simp only [show (25 : ZMod 25) = 0 by decide,
      show (50 : ZMod 25) = 0 by decide,
      show (250 : ZMod 25) = 0 by decide,
      show (625 : ZMod 25) = 0 by decide,
      mul_zero, add_zero, sub_zero]
```

この宣言は `private` であり、`SignedFiveAdic.lean` 内部で sum orientation の residual `SumGN5` を法 25 で固定する局所補題である。

## 数学的主張

自然数 `u,v` が互いに素で、かつ

$$
5\mid(u+v)
$$

を満たすなら、

$$
\operatorname{SumGN5}(u,v)\equiv5\pmod{25}
$$

である。

`SumGN5` は `Nat.sub` を避けるため `v ≤ u` とその反対に分けて定義される。例えば `v ≤ u` 側で `u=v+d` と書けば、carrier 条件は

$$
u+v=d+2v=5k
$$

となるので、`ZMod 25` では

$$
d=5k-2v.
$$

これを `SumGN5` の多項式へ代入すると、法 25 で残る本質的な項は `v^4` に集約される。互いに素性と `5∣u+v` から `5∤v` が従い、0065 より

$$
v^4=1+5q\quad\text{in }\mathrm{ZMod}\ 25.
$$

したがって多項式全体は 5 へ落ちる。`u ≤ v` 側も完全に対称で、今度は `5∤u` と `u^4=1+5q` を使う。

## 証明全体での役割

0066 が difference orientation の `GN5` residual を法 25 で 5 に固定したのに対し、本補題は sum orientation に同じ exact five-adic 情報を与える。

後段 `nonempty_signedFiveAdicPacket_of_normalForm` の `sumGap` branch では、本補題を

```lean
have hcast : (SumGN5 u v : ZMod 25) = 5 :=
  SumGN5_cast_mod25_eq_five hPack.hxy h5sum
```

として直接呼び、その後

$$
\operatorname{SumGN5}(u,v)\bmod25=5
$$

へ戻す。そこから

$$
5\mid\operatorname{SumGN5}(u,v),\qquad
25\nmid\operatorname{SumGN5}(u,v)
$$

を得て、最終的に

$$
v_5(\operatorname{SumGN5}(u,v))=1
$$

を packet へ格納する。

これにより difference / sum の二方向は、後段から見れば同じ `residual_mod_twentyFive = 5` という共通インターフェースへ同化される。

## 直接依存する定義・補題

- `SumGN5` — 0059
- `five_not_dvd_left_of_coprime_of_dvd_add` — 0062
- `five_not_dvd_right_of_coprime_of_dvd_add` — 0063
- `fourth_power_zmod25_decomposition` — 0065
- `Nat.exists_eq_add_of_le`
- `Nat.le_of_not_ge`
- `Nat.add_sub_cancel_left`
- `congrArg`
- `eq_sub_of_add_eq`
- `omega`
- `push_cast`
- `ring_nf`
- `simp only`
- `ZMod 25`

数学的な核心依存は、互いに素性から両成分が 5 の倍数でないことを確保する 0062・0063 と、非零剰余の第四冪を `1+5q` 型へ持ち上げる 0065 である。

## 証明の流れ

1. 0062・0063 から `h5u : 5 ∤ u` と `h5v : 5 ∤ v` を得る。
2. `by_cases h : v ≤ u` で `SumGN5` の piecewise 定義と同じ二枝へ分岐する。
3. `v ≤ u` 側では `u=v+d` と書き、`5∣u+v` の witness `k` を取り出す。
4. `omega` により `d+2v=5k` を作る。
5. この自然数等式を `congrArg` で `ZMod 25` へ cast し、`d=5k-2v` の形へ変形する。
6. 0065 を `v` に適用して `v^4=1+5q` を得る。
7. `Nat.add_sub_cancel_left` で `Nat.sub` を消し、`push_cast` で多項式を `ZMod 25` 上へ移す。
8. `hdZ` と `hq` を代入し、`ring_nf` を二度使って正規化する。
9. `25,50,250,625` が `ZMod 25` で 0 であることを明示して `simp only` で結論 5 を得る。
10. `v ≤ u` でない側では `u ≤ v` を作り、`u` と `v` を入れ替えた完全対称の処理を行う。

## Lean 固有の処理

最大の Lean 固有要素は、`SumGN5` が `Nat.sub` の切り詰め減算を安全に扱うため piecewise に定義されていることである。数学的には対称多項式の一つの恒等式として扱いたいところだが、Lean 証明は定義と同じ順序分岐を再現する。

`Nat.exists_eq_add_of_le` で小さい方との差 `d` を自然数として導入すると、`Nat.sub` が `Nat.add_sub_cancel_left` で消え、以後は通常の多項式計算になる。

また `h5sum` の witness を `rcases` で具体化してから `omega` で `d+2v=5k` を作る点も、自然数 arithmetic と `ZMod` algebra の境界を明確に分離している。`congrArg` はその境界を跨ぐ cast の橋である。

## 冗長・重複箇所

二つの branch は `u` と `v` を交換したほぼ完全な鏡像である。`hcarrier`、`hcarrierZ`、`hdZ`、0065 の適用、`push_cast`、二回の `ring_nf`、最後の `simp only` が重複している。

さらに 0066 と同様、`25,50,250,625` を個別に `show ... = 0 by decide` で消す処理も機械的である。

`rw [hq]; ring_nf; rw [hq]; ring_nf` と同じ第四冪等式を二度使う点は、多項式正規化の途中で第四冪が再出現するための実装上の事情だが、証明意図としてはやや読みにくい。

## 最適化候補

第一候補は、二枝共通の局所補題を作ることである。例えば「`a=b+d`、`d+2b=5k`、`5∤b` なら該当する residual 多項式は `ZMod 25` で 5」という形にすれば、piecewise branch は引数配置だけになる。

第二候補は `SumGN5` の対称性補題を先に証明し、一方の順序 branch のみを本質証明として、他方を対称性で回収する方法である。`SumGN5 u v = SumGN5 v u` が自然に得られるなら、重複量は大きく減る。

第三候補は、`u+v≡0 (mod 5)` から `u≡-v (mod 5)` を直接使い、`ZMod 25` 上で residual の一次 5-adic 項だけを抽出する補助補題を設計する方法である。ただし本定理は mod 25 の情報を必要とするため、mod 5 の等式だけでは不足し、現在の `d=5k-2v` のように 5 の倍数 witness を保持する設計は合理的である。

第四候補は「25 の倍数は `ZMod 25` で 0」を一般補助補題化して concrete `show` 群を削ることである。

## 必要 Mathlib import と import 最適化候補

確認できた生成済み `Flt5DkMath/FLT5StandAlone.lean` では `import Mathlib` が使われている。本補題単独では少なくとも自然数の順序・減算、`Nat.Coprime`、`ZMod`、`omega`、`push_cast`、`ring_nf`、`simp`、`decide` が必要である。

対象ブランチでは生成元 `DkMath/FLT/Five/SignedFiveAdic.lean` の正確な import 行を直接確認できていないため、最小 import の具体的モジュール名は未確認であり、この部分は推測である。

import 最適化を行うなら、まず `ZMod` と tactic 群を個別 import へ分け、次に `Nat.Coprime`・順序・減算補題の由来を追い、Lean ビルドで不足依存を検証する必要がある。本回では Lean ビルドは行っていない。

## Comparator challenge 化の可否

非常に適している。本定理は数学的主張が明確である一方、Lean 実装には複数の設計余地がある。

- 現行: piecewise 定義と同じ二枝を直接証明
- 候補 A: 共通局所補題で左右 branch を統合
- 候補 B: `SumGN5` の対称性を使い一枝だけ証明
- 候補 C: `ZMod 25` 上の専用 residual lemma を設計
- 候補 D: concrete coefficient 消去を一般 `ZMod` API へ置換

比較軸は、証明行数、左右重複率、数学的対称性の可視性、`Nat.sub` 依存度、tactic 依存度、法 25 のハードコード量、将来の一般化可能性である。

## 根拠と推測

定理名・型・証明本体、および直後の consumer は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` で確認した。同ソースでは `nonempty_signedFiveAdicPacket_of_normalForm` の `sumGap` branch が本補題を直接呼び、得られた `ZMod 25` 等式を自然数 mod 25、5 可除、25 非可除、`padicValNat = 1` へ変換している。

GitHub コード検索は今回 upstream 502 となったため、検索機能による分割元ファイルや PDF の横断確認はできなかった。既存の日英 PDF の本定理に対応する具体的ページは未確認であり、ページ番号や本文は推測で補っていない。

## 次に読むべき定理

```lean
private theorem mod_twentyFive_eq_five_of_zmod_eq_five
    {n : ℕ} (h : (n : ZMod 25) = 5) :
    n % 25 = 5
```

0066・0067 で得た `ZMod 25` 上の等式を、後段 packet が必要とする自然数の剰余式 `n % 25 = 5` へ戻す bridge である。difference / sum の双方がこの一点に合流するため、依存順の次の宣言として読むのが自然である。
