# 0413 `padicValNat_lower_bound_d5`

## 宣言種別

`theorem`

## Lean の型

```lean
theorem padicValNat_lower_bound_d5
    {x q : ℕ}
    (hx : 0 < x)
    (hq : Nat.Prime q)
    (hqx : q ∣ x) :
    5 ≤ padicValNat q (x ^ 5) := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hvalX : 1 ≤ padicValNat q x := by
    exact (@padicValNat_dvd_iff_le q (Fact.mk hq) x 1 hx.ne').mp (by simpa using hqx)
  have hpow : padicValNat q (x ^ 5) = 5 * padicValNat q x := by simp
  rw [hpow]
  omega
```

この theorem は、正整数 `x` を素数 `q` が割るなら、その第五冪 `x^5` における `q`-進付値は少なくとも 5 であることを証明する。

## 数学的主張

仮定は

$$
0<x,
\qquad q\text{ は素数},
\qquad q\mid x
$$

である。

`q ∣ x` から

$$
v_q(x)\ge 1
$$

を得る。付値の冪公式

$$
v_q(x^5)=5v_q(x)
$$

を用いれば、

$$
v_q(x^5)
=5v_q(x)
\ge 5
$$

となる。

Lean 上の結論は

```lean
5 ≤ padicValNat q (x ^ 5)
```

である。

数学的には非常に基本的な局所評価だが、この証明では後続の clean-channel contradiction に必要な「第五冪側の local load は最低 5」という下側境界を明示的な theorem として固定している。

## 証明全体での役割

0412 までで golden zero-sector の無条件 closure は完了した。0413 からは `Valuation.lean` に入り、同じ FLT5 contradiction を `padicValNat` で再構成する独立ルートが始まる。

正本のモジュール説明では、この valuation route は

```text
complete fifth power  -> local load at least 5
clean GN5 channel     -> local load at most 1
```

という衝突を作る。

0413 はその前半、すなわち

$$
\text{complete fifth power}
\Longrightarrow
\text{local }q\text{-adic load}\ge5
$$

を担当する。

直後の `padicValNat_clean_body_upper_bound` は clean channel に対して同じ局所付値を高々 1 と評価し、さらに `padicValNat_clean_body_eq_one` が正確に 1 とする。最終的に `counterexample_false_of_clean_GN5Channel_by_padicValNat` が第五冪側の `≥5` と clean body 側の `=1` を同一量へ移して矛盾させる。

したがって 0413 は、valuation proof route の lower-bound lemma である。

## 直接依存する定義・補題

### `padicValNat`

自然数に対する `q`-進付値を返す Mathlib の関数である。

この theorem では

```lean
padicValNat q x
padicValNat q (x ^ 5)
```

を比較する。

### `Nat.Prime q`

```lean
hq : Nat.Prime q
```

が `q` の素数性を供給する。

`padicValNat` の主要補題は型クラス経由で素数性を要求するため、証明冒頭で

```lean
letI : Fact (Nat.Prime q) := ⟨hq⟩
```

として proposition の証明を instance に変換する。

### `padicValNat_dvd_iff_le`

証明の最初の実質的な橋である。

正本では

```lean
(@padicValNat_dvd_iff_le q (Fact.mk hq) x 1 hx.ne').mp
```

として明示的に適用している。

この補題により、正の基数 `x` について

$$
q^1\mid x
\Longleftrightarrow
1\le v_q(x)
$$

を使える。

仮定 `hqx : q ∣ x` は `q^1 ∣ x` と同値なので、`simpa` により `hvalX : 1 ≤ padicValNat q x` が得られる。

### `padicValNat` の冪公式

```lean
have hpow : padicValNat q (x ^ 5) = 5 * padicValNat q x := by simp
```

として `simp` が解決している。

数学的には

$$
v_q(x^5)=5v_q(x)
$$

である。

### `omega`

最後の自然数線形算術

```lean
5 ≤ 5 * padicValNat q x
```

を `hvalX : 1 ≤ padicValNat q x` から閉じる。

## 証明または構築の流れ

### 1. 素数性を instance 化する

```lean
letI : Fact (Nat.Prime q) := ⟨hq⟩
```

Mathlib の `padicValNat` API が要求する `[Fact (Nat.Prime q)]` を局所的に供給する。

### 2. `q ∣ x` を付値下界へ変換する

```lean
have hvalX : 1 ≤ padicValNat q x := by
  exact (@padicValNat_dvd_iff_le q (Fact.mk hq) x 1 hx.ne').mp
    (by simpa using hqx)
```

`hx : 0 < x` から `hx.ne' : x ≠ 0` を得る。

そして `hqx : q ∣ x` を `q^1 ∣ x` として `padicValNat_dvd_iff_le` に渡し、

```lean
1 ≤ padicValNat q x
```

を得る。

### 3. 第五冪の付値を展開する

```lean
have hpow : padicValNat q (x ^ 5) = 5 * padicValNat q x := by
  simp
```

これで目標を第五冪そのものから基底 `x` の付値へ移す。

### 4. 線形算術で閉じる

```lean
rw [hpow]
omega
```

目標は

```lean
5 ≤ 5 * padicValNat q x
```

となり、`hvalX` から直ちに従う。

## Lean 固有の処理

### 1. proposition から `Fact` instance への変換

数学では「`q` は素数」という仮定をそのまま使うが、Lean の Mathlib API では

```lean
[Fact (Nat.Prime q)]
```

という typeclass 引数として要求される場面がある。

そのため

```lean
letI : Fact (Nat.Prime q) := ⟨hq⟩
```

が必要になる。

これは新しい数学的仮定ではなく、既存の `hq` を instance search が利用できる形に包装しているだけである。

### 2. `@` による implicit argument の露出

```lean
@padicValNat_dvd_iff_le q (Fact.mk hq) x 1 hx.ne'
```

では `@` により implicit argument を明示化している。

この書き方は theorem の引数順を完全に固定できる一方、Mathlib API の引数構造への依存が強くなる。

### 3. `hx.ne'`

```lean
hx : 0 < x
```

から

```lean
hx.ne' : x ≠ 0
```

を取り出し、`padicValNat_dvd_iff_le` の非零条件を満たす。

正の自然数という FLT5 の前提が、付値 API の定義域条件を自然に供給している。

### 4. `simpa` による `q^1` の正規化

`padicValNat_dvd_iff_le` は指数 `1` に対して `q ^ 1 ∣ x` を扱うが、手元には `q ∣ x` がある。

```lean
by simpa using hqx
```

により `q ^ 1 = q` の単純化を Lean に任せている。

### 5. `simp` による付値の冪公式

```lean
by simp
```

だけで

```lean
padicValNat q (x ^ 5) = 5 * padicValNat q x
```

を得ている。

この一行は Mathlib に登録された `padicValNat` の power simplification rule に依存する。

### 6. `omega`

最後は自然数上の Presburger arithmetic であり、`omega` が適している。

ここでは付値に関する新しい知識を `omega` が発見しているのではなく、既に得た `1 ≤ padicValNat q x` を 5 倍するだけである。

## 冗長・重複箇所

### `letI` と `Fact.mk hq` の重複

冒頭で

```lean
letI : Fact (Nat.Prime q) := ⟨hq⟩
```

を登録している一方、`padicValNat_dvd_iff_le` の明示適用では

```lean
(Fact.mk hq)
```

を直接渡している。

したがって局所 instance を作った後に同じ素数性証明を明示的に再構成しており、Lean コードとして多少重複している。

ただし、この形は theorem の implicit/typeclass 引数を完全に固定するため安定性を優先した書き方とも解釈できる。

### `hpow` の中間名

```lean
have hpow : ... := by simp
rw [hpow]
```

は

```lean
simp only [...] -- 適切な補題
```

などで目標へ直接適用できる可能性がある。

しかし `hpow` と命名することで数学的な主要ステップ

$$
v_q(x^5)=5v_q(x)
$$

が可視化されており、解説・監査上は有用である。

## 最適化候補

### 1. typeclass inference を使って `padicValNat_dvd_iff_le` を簡潔化する

`letI` 後に instance inference が十分働くなら、`Fact.mk hq` を明示せずに補題を適用できる可能性がある。

例えば概念的には

```lean
have hvalX : 1 ≤ padicValNat q x := by
  apply (padicValNat_dvd_iff_le ...).mp
  simpa using hqx
```

のように書ける可能性がある。

ただし正確な implicit argument の推論可否は Lean build を行っていないため未確認である。

### 2. 第五冪専用から一般指数版への抽象化

数学的には同じ証明で、任意の `n` に対して

$$
q\mid x
\Longrightarrow
n\le v_q(x^n)
$$

という一般形が考えられる。

第五冪専用 theorem は FLT5 の依存グラフを読みやすくする利点があるため、一般化する場合も 0413 自体は corollary として残す価値がある。

### 3. `omega` を単純な単調性補題へ置換する選択肢

最後は `hvalX` の 5 倍だけなので、乗法の単調性を用いて tactic 依存を減らすことも可能である。

ただし現行の `omega` は短く明確であり、実用上の問題はない。

## 必要 Mathlib import と import 最適化候補

standalone 正本は

```lean
import Mathlib
```

を使用している。

0413 が直接必要とする Mathlib 側の機能は少なくとも、

- `padicValNat`
- `padicValNat_dvd_iff_le`
- `Fact`
- `Nat.Prime`
- `omega`

である。

従って umbrella import `Mathlib` より狭い import へ縮小できる余地は大きい。

特に valuation API を提供する Mathlib の p-adic valuation 関連モジュールと `omega` tactic のモジュールが中心候補になる。

ただし、このリポジトリの固定 Mathlib 版における正確な最小 module path と transitive import 集合は Lean build を行っていないため未確認である。従って具体的な最小 import 宣言を断定しない。

`Valuation.lean` 全体としては後続 theorem が `CleanGN5Channel`、`GN5`、`Body5`、`CounterexamplePack` など DkMath 側の宣言も必要とするため、0413 単独最小 import とモジュール全体の最小 import は分けて考えるべきである。

## Comparator challenge 化の可否

### 単独 challenge

適している。

0413 は短いが、Comparator に次の複数の能力を要求できる。

1. proposition `Nat.Prime q` を `Fact` instance に変換する。
2. 可除性 `q ∣ x` を `padicValNat` の下界へ翻訳する。
3. 第五冪に対する付値公式を適用する。
4. 最後の自然数算術を閉じる。

単なる `ring` や一発 `simp` よりも、Mathlib API の接続能力を評価しやすい。

### challenge としての注意点

`padicValNat_dvd_iff_le` をそのまま名前付きで与えると探索難度はかなり下がる。

より有用な challenge にするなら、

- `padicValNat` の基本 API は利用可能
- theorem 本体は穴あき
- `q ∣ x`、`0 < x`、`Nat.Prime q` だけを入力

として、必要な bridge lemma を Comparator 自身に発見させる構成がよい。

一方、Mathlib の theorem-name retrieval ではなく純粋な proof synthesis を比較したい場合は、使用可能補題を明示した方が公平である。

## 次に読むべき宣言

次は

```lean
theorem padicValNat_clean_body_upper_bound
    {g y q : ℕ}
    (h : CleanGN5Channel g y q) :
    padicValNat q (g * GN5 g y) ≤ 1 := by
  ...
```

を読むべきである。

0413 が第五冪側の

$$
v_q(x^5)\ge5
$$

を与えたのに対し、次の theorem は clean GN5 channel の body に対して

$$
v_q(g\,GN_5(g,y))\le1
$$

を与える。

証明の核心は、もし付値が 2 以上なら

$$
q^2\mid g\,GN_5(g,y)
$$

となり、`CleanGN5Channel.not_sq_dvd_body` に反するというものになる。

これにより valuation route の上下境界が揃い始める。
