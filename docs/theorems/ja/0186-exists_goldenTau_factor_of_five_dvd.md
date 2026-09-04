# 0186 — `exists_goldenTau_factor_of_five_dvd`

## Lean の型

```lean
theorem exists_goldenTau_factor_of_five_dvd
    {M N : ℤ} (h : (5 : ℤ) ∣ 2 * M + N) :
    ∃ k : ℤ, ∃ beta : GoldenInt,
      2 * M + N = 5 * k ∧
      beta = ⟨M - k, 2 * k - M⟩ ∧
      (⟨M, N⟩ : GoldenInt) = goldenMul goldenTau beta := by
  rcases h with ⟨k, hk⟩
  refine ⟨k, ⟨M - k, 2 * k - M⟩, hk, rfl, ?_⟩
  ext <;> simp [goldenMul, goldenTau]
  · ring
  · omega
```

これは `theorem` であり、整数座標 `M,N` が満たす線形条件

$$
5\mid 2M+N
$$

から、黄金整数

$$
\alpha=M+N\varphi
$$

の中に distinguished ramifier

$$
\tau=2+\varphi
$$

を実際の因子として構成的に抽出する。

## 数学的主張

仮定 `h : (5 : ℤ) ∣ 2 * M + N` から、ある整数 `k` が存在して

$$
2M+N=5k
$$

と書ける。

このとき theorem は

$$
\beta=(M-k)+(2k-M)\varphi
$$

を明示的に構成し、

$$
M+N\varphi=\tau\beta
$$

を証明する。

実際、`goldenTau = ⟨2,1⟩` なので、黄金整数の乗法公式

$$
(a+b\varphi)(c+d\varphi)
=(ac+bd)+(ad+bc+bd)\varphi
$$

へ

$$
(a,b)=(2,1),\qquad(c,d)=(M-k,2k-M)
$$

を代入すると、第一座標は

$$
2(M-k)+(2k-M)=M,
$$

第二座標は

$$
2(2k-M)+(M-k)+(2k-M)=5k-2M=N
$$

となる。最後の等号は `2*M + N = 5*k` の書き換えそのものである。

したがって本 theorem は、単なる「5 が norm に現れる」という数値的情報ではなく、座標合同条件から黄金整数環内部の具体的な `τ`-factorization を復元する。

## 証明全体での役割

0177–0185 では、5 の ramification を表す二つの具体元

- `goldenSqrtFive = 2φ - 1`
- `goldenTau = 2 + φ`

を導入し、

$$
N(\tau)=5,
$$

$$
\tau\overline{\tau}=5
$$

まで確立した。

0186 はそこから一段進み、整数座標上の条件

$$
5\mid 2M+N
$$

を、黄金整数環での

$$
\tau\mid(M+N\varphi)
$$

へ具体的に変換する。

これは後続の exceptional five-adic branch で極めて重要である。実際、後段の ramifier stripping では、ある黄金整数 `alpha = ⟨M,N⟩` に対して discriminant 条件から `5 ∣ 2*M+N` を導き、本 theoremを呼び出して

```lean
rcases exists_goldenTau_factor_of_five_dvd h5A with
    ⟨k, beta, hk, hbeta, halpha⟩
```

とし、`alpha = goldenMul goldenTau beta` を取り出している。

すなわち 0186 は、整数側で観測される 5-adic divisibility を、黄金整数側の可視 ramified factor へ変換する **抽出器** である。

## 直接依存する定義・補題

直接依存する主なものは次である。

- `GoldenInt`
- 0178 `goldenTau`
- 0124 `goldenMul`
- `Int` 上の整除 `∣`
- `GoldenInt.ext`

証明 tactic としては、

- `rcases`
- `refine`
- `ext`
- `simp`
- `ring`
- `omega`

を用いる。

0184 `goldenNorm_tau` や 0185 `golden_tau_mul_conj` は数学的背景として重要だが、Lean proof の直接依存ではない。本 theorem はそれらを呼ばず、整除仮定から直接座標因子を構成する。

## 証明の流れ

証明は四段階に分かれる。

### 1. 整除仮定から商 `k` を取り出す

```lean
rcases h with ⟨k, hk⟩
```

`(5 : ℤ) ∣ 2*M+N` を展開し、

```lean
k : ℤ
hk : 2 * M + N = 5 * k
```

を得る。

### 2. 因子候補 `beta` を明示的に構成する

```lean
refine ⟨k, ⟨M - k, 2 * k - M⟩, hk, rfl, ?_⟩
```

ここで theorem の existential witness を一気に与える。

$$
\beta=\langle M-k,\;2k-M\rangle.
$$

`hk` が第一 conjunct を、`rfl` が `beta` の座標定義を閉じる。

### 3. 黄金整数の等式を座標等式へ落とす

```lean
ext <;> simp [goldenMul, goldenTau]
```

`GoldenInt.ext` を用いて

$$
\langle M,N\rangle=\tau\beta
$$

を first / second coordinate の二目標へ分解し、`goldenMul` と `goldenTau` を展開する。

### 4. 第一座標は環計算、第二座標は `hk` を含む線形算術で閉じる

```lean
· ring
· omega
```

第一座標は純粋な多項式恒等式なので `ring` で閉じる。

第二座標は

$$
N=5k-2M
$$

を必要とし、これは `hk : 2M+N=5k` から得られるため `omega` が処理する。

## Lean 固有の処理

### `rcases h with ⟨k, hk⟩`

`Int` の整除は existential witness を持つ命題として表されるため、商 `k` を直接抽出できる。ここで `hk` の向きが theorem 本文の `2*M+N = 5*k` と一致しているので、そのまま existential package へ再利用できる。

### nested existential の `refine`

結論は

```lean
∃ k : ℤ, ∃ beta : GoldenInt, ...
```

という二重 existential なので、`refine ⟨k, beta, ...⟩` により witness と複数 conjunct をまとめて構築している。

### `ext`

`GoldenInt` は二座標 structure であり、structure equality を直接扱うより、`GoldenInt.ext` で `.fst` と `.snd` に分解した方が、後続の算術 tactic が使いやすい。

### `simp [goldenMul, goldenTau]`

ここでは abstraction を一度外し、具体座標式に戻す。0185 が theorem-level API を再利用する構造的 proof だったのに対し、0186 は「因子 witness を本当に構成する」ために raw coordinate algebra を直接使っている。

### `ring` と `omega` の役割分担

第一座標は仮定を必要としない恒等式なので `ring`、第二座標は整除 witness の線形関係 `hk` を必要とするので `omega` という明確な分担になっている。

## 冗長・重複箇所

本 theorem は数学的には、線形変換

$$
(c,d)\mapsto(2c+d,\;c+3d)
$$

の逆を、条件 `5 ∣ 2M+N` のもとで解いていると見ることができる。

現行 proof ではその逆行列構造を一般化せず、`beta = ⟨M-k,2*k-M⟩` を直接埋め込んでいる。このため局所的には最短だが、同様の ramifier factor extraction が別の元でも必要になれば、座標逆変換のロジックが重複する可能性がある。

また、0185 の `τ * conj τ = 5` と本 theorem は ramification を異なる方向から表す。

- 0185: `5` の内部 factorization
- 0186: 線形合同条件から `τ` 因子を抽出

論理的には別物なので重複ではないが、将来 ramification API を bundle するなら同じ cluster にまとめる価値がある。

## 最適化候補

### 1. 現行の explicit witness proof を維持する

最も直接的で、証明対象となる `beta` の座標がソース上で完全に見える。監査性が高い。

### 2. `GoldenDivides` 導入後へ theorem を移し、整除として表現する

後続 module には

```lean
def GoldenDivides (d x : GoldenInt) : Prop :=
  ∃ q : GoldenInt, x = goldenMul d q
```

がある。概念的には本 theorem を

```lean
(5 : ℤ) ∣ 2 * M + N →
GoldenDivides goldenTau (⟨M,N⟩ : GoldenInt)
```

という API に包むと、downstream の意味はより直接的になる。

ただし現行配置は `GoldenOrder.lean` の中で完結させるため、後続 `GoldenDivisibility.lean` に依存しないという利点がある。

### 3. 線形代数的 inverse map を抽象化する

`τ` 乗法は整数格子上の線形写像として行列化できる。一般化すれば「determinant 5 の格子写像」として整除条件と像の特徴付けを証明できる。

これは理論的には美しいが、現 theorem 一個のためには抽象化コストが高い。

### 4. `simp` 後の二座標を `omega` 一本で閉じられるか比較する

現行は first coordinate を `ring`、second を `omega` に分ける。簡約後の式形によっては両方を `omega` または `ring_nf` 系で統一できる可能性があるが、Lean build を行っていないため未検証である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem 自身が直接必要とする主要機能は、

- integer divisibility
- structure extensionality
- `simp`
- `ring`
- `omega`

である。

したがって modular import を最小化する場合、整数環・整除・ring normalization・Omega tactic 周辺が候補になる。ただし `GoldenOrder.lean` 全体では既に `norm_num`、`ring`、`omega` などを多数使用しているため、本 theorem 単独の最小 import と module 全体の最小 import は一致しない可能性が高い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、ここは最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。本 theorem は **構成的因子抽出** を複数のスタイルで比較できる。

候補は次の通り。

- A: 現行の explicit witness + `ext` + `ring` / `omega`
- B: 行列・線形変換として `τ` 乗法の像を特徴付ける proof
- C: `GoldenDivides` を先に導入して divisibility API として証明
- D: 0185 `τ * conj τ = 5` を経由して factorization を導く proof
- E: quotient / `AdjoinRoot` / quadratic-algebra 上の ideal-theoretic ramification から導く proof

比較軸は、

- witness の可視性
- proof term の短さ
- dependency depth
- mathematical provenance
- downstream の使いやすさ
- 一般化可能性
- tactic 依存度

である。

特に A と B は、「座標式を直接解く」方法と「determinant 5 の格子写像として理解する」方法の差を比較する良い題材になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenOrder.lean` generated section である。

正本 source では 0185 の直後に本 theorem が置かれ、その直後で `GoldenOrder.lean` が終了し、次 module `GoldenDivisibility.lean` が始まる。

```lean
theorem golden_tau_mul_conj : ...

/-- Divisibility by five of `2*M+N` explicitly extracts a factor of `tau`. -/
theorem exists_goldenTau_factor_of_five_dvd ...

end DkMath.FLT.Five

/-! ===== END GENERATED SOURCE: DkMath/FLT/Five/GoldenOrder.lean ===== -/
/-! ===== BEGIN GENERATED SOURCE: DkMath/FLT/Five/GoldenDivisibility.lean ===== -/
```

対象ブランチには `FLT5-main-ja-v0-r1.pdf` と `FLT5-main-en-v0-r1.pdf` が存在する。今回、この theorem に対応する具体的 PDF ページ・節番号は特定していないため推測しない。

## 次に読むべき宣言

依存順の次は、次 module `GoldenDivisibility.lean` の先頭宣言 **0187 `GoldenDivides`** である。

```lean
def GoldenDivides (d x : GoldenInt) : Prop :=
  ∃ q : GoldenInt, x = goldenMul d q
```

0186 が「`τ` 因子を具体的に抽出する」 theorem だったのに対し、0187 はそのような黄金整数環内部の整除を一般概念として名前付けする。

ここから、

$$
\text{explicit factor witness}
\longrightarrow
\text{golden divisibility API}
\longrightarrow
\text{norm divisibility / units / relative primality}
$$

という次の層へ進む。
