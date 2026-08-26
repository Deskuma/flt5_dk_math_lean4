# 0184 — `goldenNorm_tau`

## Lean の型

```lean
theorem goldenNorm_tau : goldenNorm goldenTau = 5 := by
  norm_num [goldenNorm, goldenTau]
```

これは `theorem` であり、0178 で定義された distinguished ramifier `goldenTau` の黄金ノルムが `5` であることを確定する。

## 数学的主張

定義は

```lean
def goldenTau : GoldenInt := ⟨2, 1⟩

def goldenNorm (x : GoldenInt) : ℤ :=
  x.fst ^ 2 + x.fst * x.snd - x.snd ^ 2
```

である。したがって

$$
\tau=2+\varphi
$$

に対して

$$
N(\tau)=N(2+\varphi)=2^2+2\cdot1-1^2=4+2-1=5
$$

となる。

0183 では

$$
\tau=\varphi\sqrt5
$$

が確立されている。また既に

$$
N(\varphi)=-1,
\qquad
N(\sqrt5)=-5,
\qquad
N(xy)=N(x)N(y)
$$

も証明済みなので、構造的には

$$
N(\tau)=N(\varphi)N(\sqrt5)=(-1)(-5)=5
$$

とも理解できる。

## 証明全体での役割

0177–0184 では、5 の ramification を担う具体的元を `GoldenInt` 上で整理している。

- `goldenSqrtFive = 2φ - 1` は平方が `5`、ノルムが `-5`。
- `goldenTau = 2 + φ` は `φ * goldenSqrtFive` と一致する。
- 本 theorem により `goldenTau` のノルムが正の `5` と確定する。

これで `goldenTau` は単なる便利な座標代表 `⟨2,1⟩` ではなく、明示的な **norm-five ramifier** として使える。

直後の theorem

```lean
theorem golden_tau_mul_conj :
    goldenMul goldenTau (goldenConj goldenTau) = goldenOfInt 5 := by
  rw [golden_mul_conj, goldenNorm_tau]
```

は本 theorem を直接使用し、

$$
\tau\overline{\tau}=5
$$

を得る。その次の `exists_goldenTau_factor_of_five_dvd` では、整数条件 `5 ∣ 2*M+N` から `goldenTau` 因子を具体的に抽出する。したがって本 theorem は「5 の整数 divisibility」と「黄金整数環内の ramified factor」を結ぶ直前の数値証明である。

## 直接依存する定義・補題

実際の Lean proof が直接依存するのは主に次である。

- 0164 `goldenNorm`
- 0178 `goldenTau`
- `norm_num`

現行 proof は 0183 `goldenTau_eq_phi_mul_sqrtFive`、0167 `goldenNorm_phi`、0182 `goldenNorm_sqrtFive`、0174 `goldenNorm_mul` を使用しない。これらは数学的 provenance を与える間接的な背景である。

依存を実装上に書けば、

$$
\texttt{goldenNorm},\ \texttt{goldenTau}
\longrightarrow
\texttt{goldenNorm_tau}
$$

である。

一方、構造的導出としては

$$
\texttt{goldenTau\_eq\_phi\_mul\_sqrtFive},
\ \texttt{goldenNorm\_mul},
\ \texttt{goldenNorm\_phi},
\ \texttt{goldenNorm\_sqrtFive}
\longrightarrow
\texttt{goldenNorm_tau}
$$

という別経路も存在する。

## 証明の流れ

現行 proof は一行である。

```lean
by
  norm_num [goldenNorm, goldenTau]
```

1. `goldenTau` を `⟨2,1⟩` へ展開する。
2. `goldenNorm` を二次形式へ展開する。
3. 目標を整数計算

$$
2^2+2\cdot1-1^2=5
$$

へ落とす。
4. `norm_num` が閉じた数値式を正規化して証明を終了する。

抽象的な環論や ramification theorem は必要なく、具体座標の閉じた計算だけで完結している。

## Lean 固有の処理

`norm_num [goldenNorm, goldenTau]` では、角括弧内の定義を simp-style に展開した後、整数の冪・積・加減算を `norm_num` が正規化する。

この theorem は変数を持たない closed proposition なので、`decide` でも証明できる可能性が高い。また定義展開後の計算が kernel reduction だけで十分なら `rfl` まで縮む可能性もある。ただし今回 Lean build は行わないため、これらの代替 proof が実際に通るかは未検証である。

より数学的な proof としては、概念的に

```lean
rw [goldenTau_eq_phi_mul_sqrtFive, goldenNorm_mul,
    goldenNorm_phi, goldenNorm_sqrtFive]
norm_num
```

のような構成が考えられる。ただし `goldenNorm_mul` の左辺が raw `goldenMul` を取ることなど、実際の rewrite 形がそのまま通るかは build 未検証である。

## 冗長・重複箇所

数値結果 `N(τ)=5` は、二つの経路で得られる。

1. `τ = ⟨2,1⟩` を直接ノルムへ代入する座標計算。
2. `τ=φ√5` とノルム乗法性から導く構造計算。

現行 source は 1 を採用しており、0183・0167・0182・0174 で既に揃っている情報を再利用していない。この意味では数学的情報の重複がある。

ただし direct coordinate proof は依存が浅く、ramifier の具体座標が変わらない限り非常に頑健である。一方、structural proof は「なぜ符号が `+5` になるのか」を明示する利点がある。

また直後の `golden_tau_mul_conj` は `golden_mul_conj` と本 theoremを組み合わせるだけなので、API としては `goldenNorm_tau` を独立 theorem にしておく価値が高い。

## 最適化候補

候補は次の四系統である。

1. **現行の direct coordinate proof を維持する**
   - 最短で局所依存が小さい。
   - explicit coordinate model の方針と一致する。

2. **structural proof に置き換える**
   - `τ=φ√5`、ノルム乗法性、既知の二つのノルムを再利用する。
   - 数学的 provenance が明瞭になる。

3. **両方を残す**
   - 現行 theorem は direct certificate として維持する。
   - 別の補助 theorem やコメントで structural derivation を示す。

4. **ramified element API を bundle する**
   - `element : GoldenInt`
   - `norm_eq_five : goldenNorm element = 5`
   - conjugate product、factor extraction などを一つの構造にまとめる。
   - 後続の exceptional branch で「norm-five ramifier」という意味を型として保持できる。

現時点では theorem が小さいため、過度な抽象化よりも現行の一行 proof の透明性に利がある。ただし ramification API が増えるなら bundle 化の価値が上がる。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 単独の実装に必要なのは概ね次である。

- `GoldenInt`
- `goldenNorm`
- `goldenTau`
- 整数算術
- `norm_num` tactic

高度な解析や数論 API は直接使用しない。

structural proof へ変更する場合は、さらに `goldenTau_eq_phi_mul_sqrtFive`、`goldenNorm_mul`、`goldenNorm_phi`、`goldenNorm_sqrtFive` が必要になるが、これらは同じ `GoldenOrder` module 内の上流宣言である。

正確な最小 Mathlib import 集合は今回 Lean build を行わないため未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。特に proof style の違いが明瞭である。

比較候補は次の通り。

- A: 現行 `norm_num [goldenNorm, goldenTau]`
- B: closed equality を `decide` で処理
- C: `ext` / 座標計算を明示する proof
- D: `τ=φ√5` とノルム乗法性を使う structural proof

比較軸は、

- proof term の短さ
- 直接依存の少なさ
- 数学的 provenance の見えやすさ
- upstream 定義変更への頑健性
- tactic 依存度
- 後続 ramification theorem との意味的一貫性

である。

特に A と D の比較は、「計算証明」と「構造証明」のどちらを theorem museum の正本 style とするかを測るよい小課題になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` 内、`DkMath/FLT/Five/GoldenOrder.lean` generated section である。source では次の順序が確認できる。

```lean
theorem goldenTau_eq_phi_mul_sqrtFive :
    goldenTau = goldenMul goldenPhi goldenSqrtFive := by
  decide

theorem goldenNorm_tau : goldenNorm goldenTau = 5 := by
  norm_num [goldenNorm, goldenTau]

theorem golden_tau_mul_conj :
    goldenMul goldenTau (goldenConj goldenTau) = goldenOfInt 5 := by
  rw [golden_mul_conj, goldenNorm_tau]
```

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は

```lean
theorem golden_tau_mul_conj :
    goldenMul goldenTau (goldenConj goldenTau) = goldenOfInt 5 := by
  rw [golden_mul_conj, goldenNorm_tau]
```

すなわち **0185 `golden_tau_mul_conj`** である。

0184 が

$$
N(\tau)=5
$$

を確定したので、0185 は一般公式

$$
x\overline{x}=N(x)
$$

へ `x=τ` を代入して

$$
\tau\overline{\tau}=5
$$

を黄金整数環内部の積等式として公開する。これが次の factor extraction theorem への最後の橋になる。