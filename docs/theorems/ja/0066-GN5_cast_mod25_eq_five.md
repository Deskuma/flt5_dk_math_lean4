# 0066 — `GN5_cast_mod25_eq_five`

## Lean の型

```lean
private theorem GN5_cast_mod25_eq_five
    {g y : ℕ} (h5g : 5 ∣ g) (h5y : ¬ 5 ∣ y) :
    (GN5 g y : ZMod 25) = 5 := by
  rcases h5g with ⟨k, rfl⟩
  rcases fourth_power_zmod25_decomposition h5y with ⟨q, hq⟩
  unfold GN5
  push_cast
  rw [hq]
  ring_nf
  simp only [show (25 : ZMod 25) = 0 by decide,
    show (50 : ZMod 25) = 0 by decide,
    show (250 : ZMod 25) = 0 by decide,
    show (625 : ZMod 25) = 0 by decide,
    mul_zero, add_zero]
```

この宣言は `private` であり、`SignedFiveAdic.lean` 内部で difference orientation の residual `GN5` を法 25 で固定する局所補題である。

## 数学的主張

自然数 `g,y` について

$$
5\mid g,\qquad 5\nmid y
$$

ならば、`GN5` を法 25 へ写した値は

$$
\operatorname{GN5}(g,y)\equiv 5\pmod{25}
$$

となる。

`g=5k` と書くと

$$
\operatorname{GN5}(5k,y)
=(5k)^4+5(5k)^3y+10(5k)^2y^2+10(5k)y^3+5y^4.
$$

最初の四項はそれぞれ 625、625、250、50 の倍数を含むので法 25 で消える。したがって

$$
\operatorname{GN5}(5k,y)\equiv 5y^4\pmod{25}.
$$

前号 0065 より、$5\nmid y$ ならある $q\in\mathbb N$ が存在して

$$
y^4=1+5q\quad\text{in }\mathrm{ZMod}\ 25
$$

と書ける。ゆえに

$$
5y^4=5+25q=5\quad\text{in }\mathrm{ZMod}\ 25,
$$

となる。

## 証明全体での役割

この補題は difference orientation の cyclotomic residual に **5-adic valuation がちょうど 1 であることを取り出す入口** である。

後段 `nonempty_signedFiveAdicPacket_of_normalForm` の difference branch では、`g=w-v` に対して本補題から

$$
(\operatorname{GN5}(w-v,v):\mathrm{ZMod}\ 25)=5
$$

を得る。そこから自然数の剰余

$$
\operatorname{GN5}(w-v,v)\bmod 25=5
$$

へ戻し、$5$ は割るが $25$ は割らない、したがって `padicValNat 5 (...) = 1` という valuation 情報へ変換する。

依存の流れは概略

```text
5 ∣ g        5 ∤ y
  ↓            ↓ 0065
 g = 5k     y^4 = 1 + 5q  in ZMod 25
    \          /
     \        /
      GN5 展開
         ↓
  GN5(g,y) = 5  in ZMod 25
         ↓
  mod 25 = 5
         ↓
  5 ∣ GN5, 25 ∤ GN5
         ↓
  v₅(GN5) = 1
```

となる。

## 直接依存する定義・補題

- `GN5` — 0006
- `fourth_power_zmod25_decomposition` — 0065
- `ZMod 25`
- 可除性 witness を取り出す `rcases`
- `push_cast`
- `rw`
- `ring_nf`
- `simp only`
- `decide` による `25 = 0` などの `ZMod 25` 計算

本質的な数学依存は `GN5` の多項式定義と 0065 の第四冪分解である。

## 証明の流れ

1. `h5g : 5 ∣ g` を `rcases` し、`g = 5 * k` と具体化する。
2. 0065 を `y` に適用し、`hq : (y : ZMod 25)^4 = 1 + 5 * q` を得る。
3. `GN5` を定義展開する。
4. `push_cast` で自然数係数と積・冪の cast を `ZMod 25` の演算へ押し込む。
5. `rw [hq]` で $y^4$ を $1+5q$ に置換する。
6. `ring_nf` で多項式を正規化する。
7. `25,50,250,625` が `ZMod 25` で 0 であることを `decide` で明示し、`simp only` で不要項を消して結論 5 を得る。

## Lean 固有の処理

数学では「$g$ は 5 の倍数だから $g$ を含む高次項は法 25 で消える」とまとめて言えるが、Lean の現行証明は `g=5*k` を実際に代入し、係数を `25,50,250,625` まで数値化して消している。

`push_cast` は `GN5` の自然数多項式を `ZMod 25` の多項式として扱える形へ変換する。続く `ring_nf` は多項式正規化を担当し、最後の `simp only` は法 25 で 0 になる具体的な係数だけを消す。

`show (25 : ZMod 25) = 0 by decide` のような補題をその場で与えているため、法 25 という固定 modulus が証明スクリプトに強く埋め込まれている。

## 冗長・重複箇所

`25,50,250,625` の四つについて個別に `show ... = 0 by decide` を並べる部分は機械的である。いずれも 25 の倍数が `ZMod 25` で 0 になる同一原理である。

また `GN5` を完全展開してから `ring_nf` しているが、既存の `GN5_eq_g_pow_four_add_five_mul` などの分解補題を利用すれば、「$g$ を含む部分」と「$5y^4$」の構造をより数学的に見せられる可能性がある。

一方、現行証明は固定された多項式をそのまま監査でき、一般補題への依存が少ないという長所もある。

## 最適化候補

第一候補は、25 の倍数が `ZMod 25` で 0 になることを一般的な `ZMod` API または補助補題でまとめ、四つの具体的 `show ... by decide` を減らすことである。

第二候補は `GN5_eq_g_pow_four_add_five_mul` を使ってから `g=5k` を代入し、法 25 で残る項が $5y^4$ だけであることを構造的に示す方法である。これにより `GN5` の完全展開への依存を弱められるかもしれない。

第三候補として、素数 $p$ に対して「$p\mid g$、$p\nmid y$、$y^{p-1}=1+pq$ mod $p^2$ 型の情報から residual が $p$ mod $p^2$ になる」という一般化を検討できる。ただし `GN5` の係数は指数 5 固有なので、過度な一般化になる可能性もある。

## 必要 Mathlib import と import 最適化候補

確認できた生成済み `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用し、manifest 上では本補題の元モジュールとして `DkMath/FLT/Five/SignedFiveAdic.lean` が並んでいる。

この補題単独では少なくとも `ZMod`、cast simplification (`push_cast`)、ring normalization (`ring_nf`)、基本 tactic (`simp`, `decide`) が必要になる。博物館ブランチでは分割元 `DkMath/FLT/Five/SignedFiveAdic.lean` を直接取得できなかったため、正確な最小 import の具体的モジュール名は未確認であり、ここは推測である。

import 最適化は分割元の import 行を取得し、`Mathlib` 全体から `ZMod`・ring tactic・cast tactic 周辺へ縮小して Lean ビルドで検証して初めて確定できる。本回では Lean ビルドは行っていない。

## Comparator challenge 化の可否

適している。目標は短いが、証明方針に複数の明確な流派がある。

- 現行: `rcases` + `unfold GN5` + `push_cast` + `ring_nf` + concrete `simp`
- 候補 A: 既存の `GN5` 分解補題を利用する構造的証明
- 候補 B: `ZMod` の divisibility / characteristic API を前面に出す証明
- 候補 C: 法 $p^2$ の一般補助補題を経由する証明

比較軸は、行数だけでなく、係数 25 へのハードコード量、数学的構造の可視性、tactic 依存度、一般化可能性、import の軽さである。

## 根拠と推測

定理名・型・証明本体は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` で確認した。また同ソース内で、後段の difference branch が本補題を `GN5 (w - v) v` に適用し、その結果を mod 25、5-divisibility、25-nondivisibility、5-adic valuation 1 へ順に変換することも確認した。

GitHub コード検索は今回一時的に upstream 502 となり、分割元 `DkMath/FLT/Five/SignedFiveAdic.lean` は博物館ブランチ上で 404 だった。したがって分割元の正確な import 行は未確認である。

既存の日英 PDF の具体的対応箇所も GitHub 検索障害のため今回確認できていない。PDF のページ番号や説明は推測で補っていない。

## 次に読むべき定理

```lean
private theorem SumGN5_cast_mod25_eq_five
    {u v : ℕ} (hcop : Nat.Coprime u v) (h5sum : 5 ∣ u + v) :
    (SumGN5 u v : ZMod 25) = 5
```

本号が difference orientation の residual を処理したのに対し、次号は sum orientation の `SumGN5` residual を同じ法 25 の値 5 に固定する。0062・0063 の互いに素補題と 0065 の第四冪分解がここで合流する。
