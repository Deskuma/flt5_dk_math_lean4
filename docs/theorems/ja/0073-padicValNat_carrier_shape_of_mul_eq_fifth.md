# 0073 — `padicValNat_carrier_shape_of_mul_eq_fifth`

## Lean の型

```lean
theorem padicValNat_carrier_shape_of_mul_eq_fifth
    {carrier residual distinguished : ℕ}
    (hc0 : carrier ≠ 0) (hr0 : residual ≠ 0) (_hd0 : distinguished ≠ 0)
    (hEq : carrier * residual = distinguished ^ 5)
    (hrVal : padicValNat 5 residual = 1) :
    ∃ m : ℕ, padicValNat 5 carrier = 4 + 5 * m := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hpow :
      padicValNat 5 (distinguished ^ 5) =
        5 * padicValNat 5 distinguished := by simp
  have hmul :
      padicValNat 5 (carrier * residual) =
        padicValNat 5 carrier + padicValNat 5 residual := by
    simpa using (padicValNat.mul (p := 5) hc0 hr0)
  have hvalEq :
      5 * padicValNat 5 distinguished = padicValNat 5 carrier + 1 := by
    calc
      5 * padicValNat 5 distinguished =
          padicValNat 5 (distinguished ^ 5) := hpow.symm
      _ = padicValNat 5 (carrier * residual) := by rw [hEq]
      _ = padicValNat 5 carrier + padicValNat 5 residual := hmul
      _ = padicValNat 5 carrier + 1 := by rw [hrVal]
  have hdValPos : 0 < padicValNat 5 distinguished := by
    have : 0 < 5 * padicValNat 5 distinguished := by
      rw [hvalEq]
      exact Nat.succ_pos _
    exact Nat.pos_of_mul_pos_left this
  have hcVal :
      padicValNat 5 carrier = 5 * padicValNat 5 distinguished - 1 :=
    Nat.eq_sub_of_add_eq hvalEq.symm
  refine ⟨padicValNat 5 distinguished - 1, ?_⟩
  have hsplit :
      (padicValNat 5 distinguished - 1) + 1 = padicValNat 5 distinguished :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hdValPos)
  calc
    padicValNat 5 carrier = 5 * padicValNat 5 distinguished - 1 := hcVal
    _ = 5 * ((padicValNat 5 distinguished - 1) + 1) - 1 := by rw [hsplit]
    _ = 4 + 5 * (padicValNat 5 distinguished - 1) := by omega
```

根拠は `docs/flt5-theorem-museum` ブランチの生成済み `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/SignedFiveAdic.lean` 部分である。

## 数学的主張

自然数 `carrier`, `residual`, `distinguished` が

$$
carrier\cdot residual=distinguished^5
$$

を満たし、`carrier` と `residual` が非零で、さらに

$$
v_5(residual)=1
$$

ならば、ある $m\in\mathbb N$ が存在して

$$
v_5(carrier)=4+5m
$$

となる。すなわち

$$
v_5(carrier)\equiv4\pmod5
$$

である。

証明の核心は付値の加法性である。積の式から

$$
v_5(carrier)+v_5(residual)=5v_5(distinguished)
$$

を得て、$v_5(residual)=1$ を代入すると

$$
v_5(carrier)+1=5v_5(distinguished)
$$

となる。よって carrier の付値は $5$ の倍数より一つ小さく、必ず $4\pmod5$ に属する。

## 証明全体での役割

0072 `padicValNat_five_eq_one_of_dvd_not_sq` は residual に対して $v_5=1$ を確定した。本補題はその情報と五乗積

$$
carrier\cdot residual=distinguished^5
$$

を結合し、もう一方の因子 carrier の five-adic load を

$$
4+5m
$$

という厳密な合同クラスへ押し出す。

この結論は直後の `SignedFiveAdicPacket` のフィールド

```lean
carrier_padicValNat_shape :
  ∃ m : ℕ, padicValNat 5 carrier = 4 + 5 * m
```

として保存される。`nonempty_signedFiveAdicPacket_of_normalForm` では difference orientation と sum orientation の双方から本補題が直接呼ばれ、以後の層は residue 計算を開き直さず packet に保存された five-adic 形だけを利用できる。

## 直接依存する定義・補題

Lean ソース上で直接使われている主要要素は次の通り。

- `padicValNat`
- `padicValNat.mul`
- `Fact (Nat.Prime 5)`
- `Nat.eq_sub_of_add_eq`
- `Nat.sub_add_cancel`
- `Nat.succ_le_of_lt`
- `Nat.pos_of_mul_pos_left`
- `omega`
- `simp` による `padicValNat 5 (distinguished ^ 5) = 5 * padicValNat 5 distinguished` の処理

証明全体での直接の前段データは `hEq` と `hrVal` であり、博物館の依存順では特に 0072 が `hrVal` を供給する。

## 証明の流れ

1. `Fact (Nat.Prime 5)` をローカル instance として導入する。
2. 五乗の付値を

   $$
   v_5(distinguished^5)=5v_5(distinguished)
   $$

   と書く。
3. `padicValNat.mul` により

   $$
   v_5(carrier\cdot residual)=v_5(carrier)+v_5(residual)
   $$

   を得る。
4. `hEq` と `hrVal` を繋ぎ、

   $$
   5v_5(distinguished)=v_5(carrier)+1
   $$

   を得る。
5. 右辺が正なので $v_5(distinguished)>0$ を導く。
6. 自然数減算を安全に扱えることを確認した上で

   $$
   v_5(carrier)=5v_5(distinguished)-1
   $$

   とする。
7. witness として

   $$
   m=v_5(distinguished)-1
   $$

   を選ぶ。
8. `omega` で

   $$
   5(m+1)-1=4+5m
   $$

   を閉じる。

## Lean 固有の処理

### `Fact (Nat.Prime 5)`

`padicValNat` の積法則は底が素数であることを typeclass 経由で要求するため、

```lean
letI : Fact (Nat.Prime 5) := ⟨by decide⟩
```

を導入している。数学上は「5 は素数」の一言だが、Lean では API の前提として instance を供給する必要がある。

### 非零仮定

`padicValNat.mul` は `carrier ≠ 0` と `residual ≠ 0` を要求するので `hc0`, `hr0` が直接使われる。一方 `_hd0 : distinguished ≠ 0` はこの証明本体では使われていない。`distinguished` の付値が正であることは `hvalEq` から内部的に導かれている。

### 自然数減算

結論を $4+5m$ の形にするため witness を `padicValNat 5 distinguished - 1` とする。このとき truncating subtraction を避けるため、まず `hdValPos` を証明し、その後 `Nat.sub_add_cancel` を使っている。これは整数上なら不要な Lean/Nat 固有の処理である。

## 冗長・重複箇所

最も目立つのは `_hd0` が未使用である点である。定理の現行型では distinguished の非零性を要求するが、証明は `hEq`, `hrVal`, `hc0`, `hr0` から必要な positivity を回収している。したがって現在の実装だけを見る限り `_hd0` は冗長である。

また `hpow`, `hmul`, `hvalEq`, `hdValPos`, `hcVal`, `hsplit` と中間名を細かく分けている。これは監査性には優れるが、短縮だけを目的とするなら一部は `calc` に統合できる。

## 最適化候補

1. `_hd0` を定理型から削除できるかを Lean ビルドで検証する。現行証明では未使用なので有力候補だが、本博物館ではビルドを行っていないため未検証である。
2. 「$v_p(r)=k$ かつ $c r=d^e$ なら $v_p(c)\equiv-k\pmod e$」という一般補題へ抽象化する。本補題は $p=e=5$, $k=1$ の特殊形である。
3. 自然数の `- 1` を経由せず、`5 * t = c + 1` から直接 `c = 4 + 5 * (t - 1)` を返す小補題を切り出すと five-adic 算術と Nat 算術を分離できる。
4. `Fact (Nat.Prime 5)` の生成を周辺の five-adic セクションで共有できるなら、各補題の instance boilerplate を減らせる。

## 必要 Mathlib import と import 最適化候補

生成済み standalone artifact で確認できる import は

```lean
import Mathlib
```

であり、この状態で本定理が収録されていることは確認できる。manifest は元モジュールを `DkMath/FLT/Five/SignedFiveAdic.lean` と記録しているが、この分割元ファイル自体は `docs/flt5-theorem-museum` ブランチでは取得できなかったため、元ファイルの正確な import 行は未確認である。

最小化する場合は `padicValNat` と `padicValNat.mul` を提供する p-adic valuation 系モジュール、および `omega` tactic を提供する import が中心になると考えられる。ただし具体的な最小 import 名は本ブランチ上の資料だけでは確定していないため、ここは **推測** とする。最小 import の確定には分割元 `SignedFiveAdic.lean` の復元または別 worktree 上での import 削減ビルドが必要である。

## Comparator challenge 化の可否

**適性は高い。**

入力を

```lean
carrier * residual = distinguished ^ 5
padicValNat 5 residual = 1
```

とし、出力を

```lean
∃ m : ℕ, padicValNat 5 carrier = 4 + 5 * m
```

に固定すれば、複数の証明戦略を比較しやすい。

比較対象としては、

- 現行の `padicValNat.mul` + Nat 算術型
- congruence を先に立てる型
- 一般 valuation-congruence 補題を経由する型
- `_hd0` を除去した最小仮定型

が考えられる。判定基準は行数よりも、非零前提の透明性、Nat subtraction の安全性、一般化可能性、Mathlib API への依存の薄さがよい。

## 次に読むべき宣言

Lean ソースの直後は

```lean
inductive SignedFiveAdicSource
    (u v w carrier residual distinguished : ℕ) : Prop
```

である。difference orientation と sum orientation のどちらから共通の `carrier/residual/distinguished` 三つ組が来たかを記録する provenance 型であり、その直後の `SignedFiveAdicPacket` が本補題の結論を含む全 five-adic invariant を一つに束ねる。

したがって依存順では次に `DkMath.FLT.Five.SignedFiveAdicSource` を読むのが自然である。

## 根拠と注意

- 定理本体、直後の `SignedFiveAdicSource`、`SignedFiveAdicPacket`、および `nonempty_signedFiveAdicPacket_of_normalForm` における直接使用は、対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` で確認した。
- standalone manifest は元モジュール名を `DkMath/FLT/Five/SignedFiveAdic.lean` と記録している。
- 分割元 `DkMath/FLT/Five/SignedFiveAdic.lean` は対象ブランチでは取得できなかったため、正確な最小 import は未確認である。
- 既存日本語・英語 PDF における本定理の具体的ページ対応は今回確認できなかったため、PDF 固有の説明やページ番号は推測で補っていない。
