# 0332 — `eleven_dvd_d_of_fifth_add_four_fifth`

## 宣言種別

この宣言は **`theorem`** である。

第五冪方程式

$$
e^5 + 4d^5 = f^5
$$

が自然数上で成立するなら、中央の変数 $d$ は必ず 11 で割り切れることを示す局所合同式補題である。

## Lean の型

```lean
/-- The odd factor branch forces its fifth-power offset into the prime eleven. -/
theorem eleven_dvd_d_of_fifth_add_four_fifth
    {e d f : ℕ} (h : e ^ 5 + 4 * d ^ 5 = f ^ 5) : 11 ∣ d := by
  by_contra hd
  have he := fifth_mod_eleven_cases e
  have hd' := fifth_mod_eleven_cases d
  have hf := fifth_mod_eleven_cases f
  have hdmod : d ^ 5 % 11 ≠ 0 := by
    intro hz
    apply hd
    apply (by norm_num : Nat.Prime 11).dvd_of_dvd_pow
    exact Nat.dvd_of_mod_eq_zero hz
  have hm := congrArg (fun n : ℕ => n % 11) h
  omega
```

## 数学的主張

任意の自然数 $e,d,f$ について、

$$
e^5 + 4d^5 = f^5
$$

ならば

$$
11 \mid d
$$

である。

証明の核心は mod 11 における第五冪剰余である。直前の `fifth_mod_eleven_cases` により、任意の自然数 $n$ について

$$
n^5 \bmod 11 \in \{0,1,10\}
$$

すなわち

$$
n^5 \equiv 0,\pm1 \pmod{11}
$$

である。

もし $11\nmid d$ なら $d^5\not\equiv0\pmod{11}$ なので、

$$
d^5\equiv\pm1\pmod{11}
$$

である。一方 $e^5,f^5$ も $0,\pm1$ のいずれかである。

したがって

$$
e^5+4d^5\equiv f^5\pmod{11}
$$

において、$4d^5$ は $4$ または $-4$ に合同となる。そこへ $e^5\in\{0,\pm1\}$ を加えても、右辺の可能値 $f^5\in\{0,\pm1\}$ と一致しない。ゆえに $11\nmid d$ は不可能であり、$11\mid d$ が強制される。

## 証明全体での役割

この theorem は零セクター factorization の **odd branch に対する mod 11 obstruction** を供給する。

前段では `GoldenZeroSectorInversionPacket.odd_factor_halves` により奇数 `c` の branch で

$$
A_0 = 2e^5,
\qquad
B_0 = 2f^5
$$

型の第五冪因子化が作られ、その差分から

$$
e^5 + 4d^5 = f^5
$$

が得られる。

今回の theorem はその方程式だけを入力として

$$
11\mid d
$$

を抽出する。後続の `GoldenZeroSectorFactorData.odd_eleven_channel` では、これを `coprime_c_d` と組み合わせて

$$
11\nmid c
$$

を得て、さらに factor ownership と coprimality を使って $e,f,e f$ からも 11 を排除する。

つまりこの theorem は、抽象的な factor packet に具体的な奇素数 11 を注入する **局所素数チャネル生成器** として働く。

## 直接依存する定義・補題

### `fifth_mod_eleven_cases`

直前の theorem であり、`e`, `d`, `f` の第五冪剰余をそれぞれ

$$
0,1,10
$$

の三値へ制限する。

```lean
have he := fifth_mod_eleven_cases e
have hd' := fifth_mod_eleven_cases d
have hf := fifth_mod_eleven_cases f
```

### `Nat.Prime.dvd_of_dvd_pow`

11 が素数であることを使い、

$$
11\mid d^5
$$

から

$$
11\mid d
$$

へ戻す。

### `Nat.dvd_of_mod_eq_zero`

`d ^ 5 % 11 = 0` を

$$
11\mid d^5
$$

へ変換する。

### `congrArg`

元の等式 `h` の両辺へ `% 11` を作用させる。

```lean
have hm := congrArg (fun n : ℕ => n % 11) h
```

これにより Lean の context に mod 11 版の等式が入る。

### `omega`

剰余値が有限集合 `0,1,10` に限定されている事実と `hdmod`、`hm` をまとめて処理し、残る有限な算術矛盾を閉じる。

## 証明または構築の流れ

### 1. 結論を否定する

```lean
by_contra hd
```

により

$$
11\nmid d
$$

を仮定する。

### 2. 三つの第五冪剰余を分類する

```lean
have he := fifth_mod_eleven_cases e
have hd' := fifth_mod_eleven_cases d
have hf := fifth_mod_eleven_cases f
```

これで

$$
e^5,d^5,f^5 \pmod{11}
$$

はすべて `0`, `1`, `10` のいずれかに限定される。

### 3. `d^5 % 11 = 0` を排除する

```lean
have hdmod : d ^ 5 % 11 ≠ 0 := by
  intro hz
  apply hd
  apply (by norm_num : Nat.Prime 11).dvd_of_dvd_pow
  exact Nat.dvd_of_mod_eq_zero hz
```

もし `d^5 % 11 = 0` なら $11\mid d^5$ であり、11 の素数性から $11\mid d$ となって `hd` に矛盾する。

したがって `hd'` の三値のうち 0 branch は消え、$d^5$ は mod 11 で $\pm1$ に限定される。

### 4. 元の等式を mod 11 へ写す

```lean
have hm := congrArg (fun n : ℕ => n % 11) h
```

により

$$
(e^5 + 4d^5)\bmod11 = f^5\bmod11
$$

が得られる。

### 5. `omega` で有限矛盾を閉じる

この時点で `he`, `hd'`, `hf` はそれぞれ三値 disjunction、`hdmod` により `d^5 % 11 = 0` は排除済み、`hm` が剰余等式である。

`omega` はこれらを展開して、残る有限な線形整数算術ケースがすべて不可能であることを確認する。

結果として否定仮定 `hd` が崩れ、`11 ∣ d` が得られる。

## Lean 固有の処理

### `by_contra` による divisibility の否定処理

直接 `11 ∣ d` の witness を構築するのではなく、`¬ 11 ∣ d` を仮定して mod 11 の非零性へ変換する方が簡潔である。

### 素数性の型を `norm_num` で供給する

```lean
(by norm_num : Nat.Prime 11)
```

は 11 の素数性を Mathlib の一般定理へ渡すための proof term である。

### `congrArg` で等式全体に `% 11` を適用する

自然数の等式に対して `% 11` を双方へ作用させる処理を、手動 rewrite ではなく関数合同性として行っている。

### `omega` が disjunction と剰余制約を統合する

この theorem では `he`, `hd'`, `hf` を明示的に `rcases` して 27 case に分けていない。`omega` が context 中の disjunction を利用し、有限算術をまとめて閉じている。

これは Lean 上で非常に短いが、数学的には「第五冪剰余表を用いた有限ケース排除」を自動化したものと理解するとよい。

## 冗長・重複箇所

証明自体は短く、明白な重複は少ない。

ただし

```lean
have he := fifth_mod_eleven_cases e
have hd' := fifth_mod_eleven_cases d
have hf := fifth_mod_eleven_cases f
```

は同一 theorem の三回適用であり、将来同型の mod-$p$ obstruction が増えるなら、三変数をまとめた residue packet のような補助定義へ抽象化する余地はある。

一方で現在の 3 行は極めて読みやすく、単発用途なら抽象化しない方が保守的である。

また `hdmod` は `Nat.Prime.dvd_of_dvd_pow` を介しているが、`Nat.Prime.dvd_pow` 系 API でより直接的な書き方が可能かもしれない。これは Mathlib の現行 API を確認して比較する余地がある。

## 最適化候補

### 1. 明示 case split 版との比較

`omega` に依存せず、`rcases he` / `rcases hd'` / `rcases hf` で有限 case を明示し `norm_num` で閉じる版が考えられる。

現行版の方が短いが、明示版は「なぜ mod 11 が効くか」を proof term 上でも可視化できる。

### 2. `ZMod 11` を使う概念化

自然数 `%` ではなく `ZMod 11` に移せば

$$
x^5\in\{0,1,-1\}
$$

を環の等式として扱える。合同算術としては概念的だが、この theorem 単体では coercion と import が増える可能性がある。

### 3. mod 11 obstruction の専用 lemma 化

より一般に

$$
a^5 + k b^5 = c^5
$$

の係数 $k$ ごとの局所 obstruction を探索する場合、剰余集合と係数をパラメータ化した finite checker へ一般化できる。

ただし現行 FLT5 証明では係数 4 と素数 11 の組が目的に直結しており、現状の専用 theorem は意図が明確である。

## 必要 Mathlib import と import 最適化候補

standalone 正本全体は

```lean
import Mathlib
```

を使用している。

この theorem 自体で直接必要になる主な機能は

- `Nat.Prime`
- `Nat.Prime.dvd_of_dvd_pow`
- `Nat.dvd_of_mod_eq_zero`
- `norm_num`
- `omega`
- 前段の `fifth_mod_eleven_cases`

である。

したがって `Mathlib` 全体からより小さい import へ縮小できる可能性は高い。ただし今回は Lean ビルドを行わないため、 **最小 import 集合は確認していない** 。特に `omega` と `norm_num`、自然数素数・剰余 API を同時に満たす最小組合せは別途検証が必要である。

## Comparator challenge 化の可否

**非常に適している。**

比較候補として少なくとも次がある。

1. 現行の `fifth_mod_eleven_cases` + `omega`
2. 三変数の剰余を明示 `rcases` し `norm_num` で閉じる完全列挙版
3. `ZMod 11` へ移して環演算として示す版
4. 第五冪剰余集合を一般 lemma として抽象化し、その一般 lemma から導く版

評価軸としては証明長、剰余論の可視性、tactic 依存度、import サイズ、一般化可能性が有効である。

特に現行証明は `omega` がかなり多くを肩代わりしているため、Comparator challenge では「短さ」と「数学的説明可能性」の差がよく現れる。

## 次に読むべき宣言

正本上で次の宣言は

```lean
inductive GoldenZeroSectorFactorBranch
  | odd
  | evenLeftLow
  | evenRightLow
  deriving DecidableEq
```

である。

したがって次の連番は **0333 `GoldenZeroSectorFactorBranch`** となる。

これは theorem ではなく **`inductive`** 宣言であり、零セクター factorization の二進分岐を

- `odd`
- `evenLeftLow`
- `evenRightLow`

の三 branch として型レベルで固定する。今回の mod 11 theorem が odd branch の局所 obstruction を完成させた直後に、以後の factor data を分類する branch label が導入される。