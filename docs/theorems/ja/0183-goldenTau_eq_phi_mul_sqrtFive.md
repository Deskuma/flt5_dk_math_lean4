# 0183 — `goldenTau_eq_phi_mul_sqrtFive`

## Lean の型

```lean
theorem goldenTau_eq_phi_mul_sqrtFive :
    goldenTau = goldenMul goldenPhi goldenSqrtFive := by
  decide
```

これは `theorem` であり、0178 で定義された ramified element `goldenTau` を、0161 `goldenPhi` と 0177 `goldenSqrtFive` の積として同定する。

## 数学的主張

各定義は

```lean
def goldenPhi : GoldenInt := ⟨0, 1⟩
def goldenSqrtFive : GoldenInt := ⟨-1, 2⟩
def goldenTau : GoldenInt := ⟨2, 1⟩
```

であり、数学的には

$$
\varphi=\frac{1+\sqrt5}{2},\qquad
\sqrt5=2\varphi-1,\qquad
\tau=2+\varphi
$$

を表している。本 theorem は

$$
\tau=\varphi\sqrt5
$$

すなわち

$$
2+\varphi=\varphi(2\varphi-1)
$$

を主張する。

黄金比の基本関係

$$
\varphi^2=\varphi+1
$$

を用いれば、右辺は

$$
\varphi(2\varphi-1)=2\varphi^2-\varphi
=2(\varphi+1)-\varphi
=\varphi+2
$$

となる。

## 証明全体での役割

0177–0182 では、5 の ramification を担う二つの具体的元が準備された。

- `goldenSqrtFive = 2φ - 1` は平方が `5`、ノルムが `-5`。
- `goldenTau = 2 + φ` は後続でノルム `5` を持つ distinguished ramifier として使われる。

0183 はこの二つが独立の別物ではなく、単元候補 `φ` を掛けることで結ばれることを明示する。

$$
\tau=\varphi\sqrt5
$$

という関係は、同じ ramified prime over `5` の associate を二つの座標表示で扱っていることを示す橋である。後続の `goldenNorm_tau` と組み合わせると、`goldenTau` が norm-five element であることと `goldenSqrtFive` が norm `-5` を持つことが、`N(φ)=-1` を介して整合する。

FLT5 の exceptional branch では、その後 `exists_goldenTau_factor_of_five_dvd` が `5 ∣ 2*M+N` という整数条件から `goldenTau` 因子を実際に抽出する。したがって本 theorem は、その distinguished factor が平方根側の ramifier と同一 associate class に属することを示す構造的説明でもある。

## 直接依存する定義・補題

直接現れる依存は次である。

- 0161 `goldenPhi`
- 0177 `goldenSqrtFive`
- 0178 `goldenTau`
- 0124 `goldenMul`

数学的背景としては 0165 `golden_phi_sq` の

$$
\varphi^2=\varphi+1
$$

がこの等式を説明する。ただし実際の Lean proof は `golden_phi_sq` を rewrite しておらず、閉じた座標等式を `decide` で直接判定している。

依存を概念的に書けば、

$$
\texttt{goldenPhi},\ \texttt{goldenSqrtFive},\ \texttt{goldenTau},\ \texttt{goldenMul}
\longrightarrow
\texttt{goldenTau_eq_phi_mul_sqrtFive}
$$

となる。

## 証明の流れ

Lean proof は一行である。

```lean
by
  decide
```

定義を展開すると、右辺は座標乗法

```lean
goldenMul ⟨0, 1⟩ ⟨-1, 2⟩
```

である。`goldenMul` の定義

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

へ代入すると、

$$
(0,1)(-1,2)
=
(0\cdot(-1)+1\cdot2,
 0\cdot2+1\cdot(-1)+1\cdot2)
=(2,1)
$$

となり、これは `goldenTau = ⟨2,1⟩` と一致する。

したがって proof kernel が確認している内容は、抽象的な algebraic-number argument ではなく完全に閉じた整数座標等式である。

## Lean 固有の処理

`decide` が使えるのは、この proposition が具体的な `GoldenInt` 値同士の equality まで閉じており、その equality が decidable だからである。

ここでは変数も仮定も存在しないため、定義展開後の整数計算を decision procedure に任せられる。

別証明としては、例えば

```lean
  ext <;> norm_num [goldenTau, goldenPhi, goldenSqrtFive, goldenMul]
```

のような座標証明が考えられる。ただしこれは今回 Lean build を行っていないため、実際にそのまま通るかは未検証である。

また、標準 `*` notation と 0165 `golden_phi_sq` を使い

```lean
  -- 概念例
  rw [goldenTau, ...]
```

のように数学的由来を前面に出す証明も設計候補だが、現行 proof は explicit coordinate model の強みを活かして最小化されている。

## 冗長・重複箇所

`goldenTau` と `goldenSqrtFive` はすでに具体座標で定義されているため、本 theorem は計算上は新情報をほとんど追加しない。座標だけを見れば `decide` 可能な定数等式である。

一方、数学的 API としては重要である。二つの ramifier representation が associate であることを名前付き theorem として公開するため、単なる定義展開より意味が明瞭になる。

潜在的な重複としては、`goldenTau` を最初から

```lean
def goldenTau : GoldenInt := goldenMul goldenPhi goldenSqrtFive
```

と定義すれば本 theorem は `rfl` 相当になる。ただしその場合、`goldenTau = ⟨2,1⟩` という明示座標を得る側に別 theorem が必要になる。

現行設計は、ramifier factorization で頻繁に使う `⟨2,1⟩` を定義として保持し、数学的由来を theorem で別に記録する方を選んでいる。

## 最適化候補

候補は次の三系統である。

1. **現行方式を維持する**
   - `goldenTau := ⟨2,1⟩`
   - 本 theorem で `τ = φ√5` を証明する。
   - 後続の整数座標計算が単純になる。

2. **代数的定義を正本にする**
   - `goldenTau := goldenPhi * goldenSqrtFive`
   - 座標 `⟨2,1⟩` を補題として証明する。
   - 数学的 provenance は強くなるが、factor extraction の座標計算では展開が一段増える。

3. **ramified prime associate を抽象化する**
   - `φ` が unit であることを利用して `goldenTau` と `goldenSqrtFive` の `Associated` 関係を公開する。
   - divisibility / valuation 層から見ると、単なる equality より associate class が本質的である可能性がある。

特に後続で `goldenUnit_phi` が整備された後には、

$$
\mathrm{Associated}(\tau,\sqrt5)
$$

という theorem を追加すると、ramification の構造をより Mathlib 標準的に表現できる可能性がある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自体が直接必要とする機能は小さい。

- `GoldenInt` とその `DecidableEq`
- `goldenMul`
- `goldenPhi`
- `goldenSqrtFive`
- `goldenTau`
- `decide`

高度な解析・数論ライブラリは theorem 単独では不要と考えられる。

ただし実際の `GoldenOrder` module は環構造、`Zsqrtd`、`omega`、`ring`、`norm_num` など多数の機能を同時に使用している。Lean build を行わない条件のため、正確な最小 import 集合は未検証であり、import 最適化は候補としてのみ記録する。

## Comparator challenge 化の可否

適している。小さな closed theorem なので実装方式を明確に比較できる。

比較候補は次の通り。

- A: 現行 `by decide`
- B: `ext` + `norm_num` による明示座標証明
- C: `φ²=φ+1` を使った標準 algebra notation の証明
- D: `goldenTau` 自体を `φ * sqrtFive` で定義して `rfl` 化

比較軸は、

- proof term の単純さ
- 数学的 provenance の見えやすさ
- 定義変更への頑健性
- downstream coordinate computation の簡潔さ
- `simp` / `ring` / `decide` への依存度

である。

現行 `decide` は最短で非常に頑健だが、「なぜ `τ=φ√5` なのか」という数学的説明は source の定義と theorem 名に委ねられている。

## PDF・Lean source との対応

形式的な正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` 内、`DkMath/FLT/Five/GoldenOrder.lean` generated section である。そこで

```lean
theorem goldenTau_eq_phi_mul_sqrtFive :
    goldenTau = goldenMul goldenPhi goldenSqrtFive := by
  decide

theorem goldenNorm_tau : goldenNorm goldenTau = 5 := by
  norm_num [goldenNorm, goldenTau]
```

という順序が確認できる。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は

```lean
theorem goldenNorm_tau : goldenNorm goldenTau = 5 := by
  norm_num [goldenNorm, goldenTau]
```

すなわち **0184 `goldenNorm_tau`** である。

0183 で

$$
\tau=\varphi\sqrt5
$$

という ramifier 間の関係を確定したので、次は distinguished ramifier `τ` 自身が

$$
N(\tau)=5
$$

を持つことを明示する。これにより `goldenTau` が「norm-five element」として後続の divisibility / ramification machinery へ入る。
