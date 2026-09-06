# 0331 — `fifth_mod_eleven_cases`

## 宣言種別

この宣言は **`theorem`** である。

自然数の第五冪を 11 で割った剰余が、必ず `0`, `1`, `10` のいずれかになることを示す有限剰余分類である。

## Lean の型

```lean
/-- Fifth powers modulo eleven are `0`, `1`, or `-1`. -/
theorem fifth_mod_eleven_cases (n : ℕ) :
    n ^ 5 % 11 = 0 ∨ n ^ 5 % 11 = 1 ∨ n ^ 5 % 11 = 10 := by
  rw [Nat.pow_mod]
  generalize hr : n % 11 = r
  have hlt : r < 11 := by rw [← hr]; omega
  interval_cases r <;> norm_num
```

## 数学的主張

任意の自然数 $n$ に対して、

$$
n^5 \bmod 11 \in \{0,1,10\}
$$

である。

11 を法とすれば $10\equiv -1\pmod{11}$ なので、通常の整数合同式では

$$
n^5\equiv 0,1,-1\pmod{11}
$$

と書ける。

これは 11 が素数であり、非零剰余類の乗法群が位数 10 を持つこととも整合する。非零 $n$ に対して Fermat の小定理から $n^{10}\equiv1\pmod{11}$ であり、したがって $(n^5)^2\equiv1\pmod{11}$ なので $n^5\equiv\pm1\pmod{11}$ となる。$11\mid n$ の場合だけ剰余は 0 である。

ただしこの Lean 証明は群論や Fermat の小定理を使わず、剰余 $r=n\bmod11$ の 11 通りを直接有限検査している。

## 証明全体での役割

この補題は、零セクター factorization phase に現れる mod 11 obstruction の入口である。

直後の

```lean
theorem eleven_dvd_d_of_fifth_add_four_fifth
    {e d f : ℕ} (h : e ^ 5 + 4 * d ^ 5 = f ^ 5) : 11 ∣ d := by
```

では、`e^5`, `d^5`, `f^5` の各剰余をこの theorem によって

$$
0,1,-1
$$

の三値へ制限する。

そのうえで

$$
e^5+4d^5=f^5
$$

を mod 11 で比較すると、$11\nmid d$ を仮定した場合の有限な剰余組合せを排除できる。したがって今回の theorem は、後続で

$$
11\mid d
$$

を強制するための **剰余状態空間圧縮 lemma** として働く。

FLT5 証明全体の中では、前段までの二進因子分解・coprimality 解析から、具体的な奇素数 11 を用いる局所合同式 obstruction へ移る境界に位置する。

## 直接依存する定義・補題

この theorem は FLT5 固有の structure や packet field には依存しない。完全に一般的な自然数剰余補題である。

直接使う主な Mathlib 要素は次の通り。

### `Nat.pow_mod`

```lean
rw [Nat.pow_mod]
```

により `n^5 % 11` を `(n % 11)^5 % 11` の形へ変える。

これにより元の無限に大きくなり得る `n` ではなく、有限範囲の剰余だけを調べればよくなる。

### `generalize`

```lean
generalize hr : n % 11 = r
```

で `n % 11` に新しい変数 `r` を導入する。

### `omega`

```lean
have hlt : r < 11 := by rw [← hr]; omega
```

自然数の剰余の基本範囲

$$
0\le r<11
$$

のうち上界を Lean に認識させる。

### `interval_cases`

```lean
interval_cases r
```

により `r<11` から

$$
r=0,1,2,\ldots,10
$$

の 11 case に分解する。

### `norm_num`

各 case における具体的な第五冪と mod 11 の計算を閉じる。

## 証明または構築の流れ

### 1. 冪の剰余を剰余の冪へ落とす

最初に

```lean
rw [Nat.pow_mod]
```

を使う。

これによって目標は本質的に

$$
(n\bmod11)^5\bmod11\in\{0,1,10\}
$$

となる。

### 2. 剰余を独立変数 `r` に置き換える

```lean
generalize hr : n % 11 = r
```

により、以後は `r` だけを追えばよい。

### 3. `r<11` を得る

```lean
have hlt : r < 11 := by
  rw [← hr]
  omega
```

ここで `r` が 0 から 10 までの有限範囲にあることが確定する。

### 4. 11 case を完全列挙する

```lean
interval_cases r
```

で 11 通りに分岐する。

各 case では例えば

$$
2^5=32\equiv10\pmod{11},
$$

$$
3^5=243\equiv1\pmod{11}
$$

のような具体計算だけが残る。

### 5. `norm_num` で全 case を閉じる

```lean
<;> norm_num
```

により 11 個の目標を一括して解消する。

証明は数学的には「剰余類 11 個の表を計算する」という直截な有限検査である。

## Lean 固有の処理

### `Nat.pow_mod` で探索空間を有限化する

`interval_cases` を直接 `n` に使うことはできないため、先に `n % 11` へ射影する必要がある。

この一行が、無限領域の自然数問題を有限状態問題へ変換する核心である。

### `generalize hr : n % 11 = r`

`generalize` は、複雑な式を名前付き変数へ置き換え、その対応関係を等式 `hr` として保存する。

ここでは `interval_cases` が扱いやすい単純な自然数変数 `r` を作るために使われている。

### `hlt` は `interval_cases` のための境界情報

`have hlt : r < 11` はその後コード上で明示的に参照されないが、local context に存在することで `interval_cases r` が有限範囲を認識できる。

Lean の tactic 指向証明では、このように後続 tactic が context から自動利用する補助事実を先に置くことがある。

## 冗長・重複箇所

証明は非常に短く、実質的な冗長性は少ない。

可能性としては、`generalize` と `hlt` を使わずに剰余に対する別形式の finite tactic を組むこともできるが、現在の形は

1. mod へ落とす
2. 有限区間を得る
3. 全 case を計算する

という構造が明瞭である。

また数学的には Fermat の小定理や有限体の乗法群を用いれば概念的証明も可能だが、この補題単体では現在の brute-force proof の方が依存が軽く、Lean 上でも短い。

## 最適化候補

### 1. 現行の有限検査を維持する

11 は十分小さいため、`interval_cases` + `norm_num` は堅牢で読みやすい。

一般理論を導入して短く見せても、必要 import や補題探索が増える可能性がある。

### 2. 一般化した素数合同式 lemma への置換

もし今後 $p$ を法とする

$$
x^{(p-1)/2}\in\{0,\pm1\}
$$

型の補題を繰り返し使うなら、有限体または Fermat の小定理に基づく一般 lemma を用意する価値がある。

しかし現段階で mod 11 専用に一度使うだけなら過剰抽象化となる可能性が高い。

### 3. theorem 名の一般性

`fifth_mod_eleven_cases` は内容を正確に表しており、後続 theorem からも検索しやすい。命名の変更余地は小さい。

## 必要 Mathlib import と import 最適化候補

standalone 正本全体は

```lean
import Mathlib
```

を使用している。

この theorem 単体で必要な機能は主に

- `Nat.pow_mod`
- `omega`
- `interval_cases`
- `norm_num`

である。

したがって `Mathlib` 全体より小さい import に縮小できる可能性は高い。

ただし今回 Lean ビルドは行わないため、 **最小 import 集合は確認していない** 。特に `interval_cases`, `omega`, `norm_num` の tactic import をすべて満たす最小組合せは別途検証が必要である。

## Comparator challenge 化の可否

**非常に適している。**

短い theorem でありながら、複数の証明戦略を明確に比較できる。

例えば次の 3 系統が Comparator 候補になる。

1. 現行の `interval_cases` + `norm_num` による全剰余有限検査
2. Fermat の小定理から $(n^5)^2\equiv1$ を使う概念証明
3. `Fin 11` や `ZMod 11` に移して有限体演算として処理する証明

challenge の評価軸としては、証明長、必要 import、tactic 依存度、一般化可能性、可読性を比較できる。

特に現行証明は 5 行程度で閉じるため、一般理論を使う版が本当に保守性や再利用性で勝るかを測る良い小型課題である。

## 次に読むべき宣言

次は

```lean
theorem eleven_dvd_d_of_fifth_add_four_fifth
    {e d f : ℕ} (h : e ^ 5 + 4 * d ^ 5 = f ^ 5) : 11 ∣ d := by
```

である。

したがって次の連番は **0332 `eleven_dvd_d_of_fifth_add_four_fifth`** となる。

今回の `fifth_mod_eleven_cases` が第五冪の剰余を `0,1,10` に限定し、次の theorem がその三値分類を実際の factor equation

$$
e^5+4d^5=f^5
$$

へ適用して $11\mid d$ を強制する。