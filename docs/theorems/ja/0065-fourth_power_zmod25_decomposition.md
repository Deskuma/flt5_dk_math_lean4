# 0065 — `fourth_power_zmod25_decomposition`

## Lean の型

```lean
private theorem fourth_power_zmod25_decomposition
    {n : ℕ} (h5n : ¬ 5 ∣ n) :
    ∃ q : ℕ, (n : ZMod 25) ^ 4 = 1 + 5 * (q : ZMod 25) := by
  let q : ℕ := n ^ 4 / 5
  have hmod : n ^ 4 % 5 = 1 := fourth_power_mod_five_eq_one h5n
  have hsplit := Nat.mod_add_div (n ^ 4) 5
  have hdecomp : n ^ 4 = 1 + 5 * q := by
    dsimp [q]
    omega
  refine ⟨q, ?_⟩
  have hcast := congrArg (fun t : ℕ => (t : ZMod 25)) hdecomp
  simpa using hcast
```

この宣言は `private` であり、`SignedFiveAdic.lean` 内部で使う局所補題である。

## 数学的主張

自然数 `n` が 5 の倍数でないとき、前号 0064 により

$$
n^4 \equiv 1 \pmod 5
$$

である。したがってある自然数 $q$ が存在して

$$
n^4 = 1 + 5q
$$

と書ける。本補題はこの整数分解を `ZMod 25` へ写し、

$$
(n : \mathrm{ZMod}\ 25)^4 = 1 + 5(q : \mathrm{ZMod}\ 25)
$$

という形で与える。

重要なのは、ここでは $q$ を法 5 で一意に決める必要がないことである。後段の法 25 計算では「第四冪が $1+5q$ の形を持つ」という一次の 5-adic 情報だけが必要になる。

## 証明全体での役割

この補題は、法 5 の非零第四冪情報を法 25 の計算に利用可能な形へ持ち上げる bridge である。

直後の `GN5_cast_mod25_eq_five` は `5 ∣ g` と `5 ∤ y` のもとで本補題を `y` に適用し、`GN5 g y` を `ZMod 25` 上で展開して最終的に 5 に簡約する。また `SumGN5_cast_mod25_eq_five` も `u` または `v` に本補題を適用する。

依存の流れは概略

```text
5 ∤ n
  ↓ 0064
n^4 % 5 = 1
  ↓ 0065
n^4 = 1 + 5q
  ↓ cast
(n : ZMod 25)^4 = 1 + 5q
  ↓
GN5 / SumGN5 の mod 25 計算
```

となる。

## 直接依存する定義・補題

- `fourth_power_mod_five_eq_one` — 前号 0064
- `Nat.mod_add_div`
- 自然数除算 `/`
- `omega`
- `congrArg`
- `ZMod 25` への自然数 cast
- `simpa`

直接の本質的依存は 0064 である。`Nat.mod_add_div` は除法アルゴリズム、`omega` はその等式と剰余値を組み合わせて自然数上の分解を再構成するために使われる。

## 証明の流れ

1. `q := n ^ 4 / 5` と定義する。
2. 0064 から `hmod : n ^ 4 % 5 = 1` を得る。
3. `Nat.mod_add_div (n ^ 4) 5` で、剰余と商による標準分解を得る。
4. `hmod` と除法分解から `omega` により `n ^ 4 = 1 + 5 * q` を導く。
5. 存在量化された witness としてその `q` を選ぶ。
6. `congrArg` で自然数等式を `ZMod 25` へ cast する。
7. `simpa` で cast 後の式を目標の形へ整える。

## Lean 固有の処理

数学では「$n^4 \equiv 1 \pmod 5$ だから $n^4-1$ は 5 の倍数」と一言で済む。しかし自然数上では減算を直接使うより、商 `n^4 / 5` と `Nat.mod_add_div` を用いる方が truncated subtraction を避けられる。

`hmod` は `hdecomp` の証明中に明示的に参照されていないように見えるが、`omega` がローカルコンテキスト中の `hmod` と `hsplit` の双方を利用している。これは tactic に依存したデータフローなので、読み手にはやや見えにくい。

`congrArg (fun t : ℕ => (t : ZMod 25)) hdecomp` は、自然数で確立した等式を環 `ZMod 25` に運ぶ標準的な方法である。

## 冗長・重複箇所

`hmod` と `hsplit` は最終式に直接現れず、`omega` の入力コンテキストとしてのみ使われる。このため証明の意図が tactic の内部探索に隠れている。

また、まず自然数等式 `hdecomp` を作ってから `congrArg` で cast しており、法 25 の結論だけが必要なら、より直接的な modular/divisibility API で書ける可能性はある。ただし現行形は「整数分解 → cast」という数学的構造が明瞭である。

## 最適化候補

第一候補は `Nat.mod_add_div` から `hdecomp` を `calc` で明示的に組み立て、`omega` への暗黙依存を減らすことである。例えば剰余が 1 であることを rewrite してから商分解を正規化すれば、証明のデータフローがより透明になる可能性がある。

第二候補は `5 ∣ n ^ 4 - 1` 相当の divisibility statement から witness を取り出す方法だが、`Nat.sub` の条件管理が増えるので必ずしも改善ではない。

第三候補として `ZMod 5` から直接 lift する抽象補題を用意すれば、同種の「mod $p$ の剰余情報を mod $p^2$ の $a+pq$ 表現へ持ち上げる」処理を一般化できる。ただし本証明では 5 と 25 が固定なので、現行の短さも強みである。

## 必要 Mathlib import と import 最適化候補

生成済み standalone artifact は `import Mathlib` を前提にしており、manifest では本補題の元モジュールが `DkMath/FLT/Five/SignedFiveAdic.lean` であることを確認できる。

この補題単独で必要になる機能は、少なくとも `ZMod`、自然数除算と剰余、`omega` tactic、基本的な cast/simplification である。分割元 `SignedFiveAdic.lean` の正確な import 行は今回直接確認できていないため、最小 import の具体的モジュール名は推測として扱う。

import 最適化は、分割元ファイルを直接取得し、`Mathlib` 全体ではなく `ZMod`・Nat mod/div・Omega に絞った import でビルド確認して初めて確定できる。

## Comparator challenge 化の可否

適している。主張が短い一方で、証明戦略に差が出る。

- 現行: `Nat.mod_add_div` + `omega` + `congrArg`
- 候補 A: divisibility witness を明示的に取り出す
- 候補 B: `calc` と rewrite で `omega` 依存を弱める
- 候補 C: `ZMod 5` / `ZMod 25` の一般 lifting 補題を使う

比較軸は、証明の透明性、tactic 依存度、一般化可能性、import の軽さ、後段の rewrite のしやすさである。

## 根拠と推測

定理名・型・証明本体、および直後に `GN5_cast_mod25_eq_five` が本補題を使用することは `Flt5DkMath/FLT5StandAlone.lean` で確認した。standalone manifest から `SignedFiveAdic.lean` が ordered source modules に含まれることも確認した。

既存の日英 PDF における本補題の具体的ページ対応は今回確認できていないため、PDF 固有の説明やページ番号は推測で補っていない。最小 Mathlib import も分割元の import 行を直接取得できていないため推測である。

## 次に読むべき定理

```lean
private theorem GN5_cast_mod25_eq_five
    {g y : ℕ} (h5g : 5 ∣ g) (h5y : ¬ 5 ∣ y) :
    (GN5 g y : ZMod 25) = 5
```

`fourth_power_zmod25_decomposition` を最初に直接消費する補題であり、difference orientation の `GN5` residual が法 25 でちょうど 5 になることを示す。依存順では `SumGN5_cast_mod25_eq_five` より先に読むべきである。
