# 0250 — `branchB_false_of_goldenConjugateCoprimeCore`

## Lean の型

```lean
theorem branchB_false_of_goldenConjugateCoprimeCore
    (hCore : SignedGoldenConjugateCoprimeCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) : False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_goldenConjugateCoprimeCore hCore) hPack hBranch
```

これは `theorem` である。0248 `SignedGoldenConjugateCoprimeCore` として与えられた contradiction receiver を、既存の Branch-B routing theorem へ接続し、`CounterexamplePack` と Branch-B 条件から `False` を得る。

## 数学的主張

本 theorem の論理構造は、概略

$$
\mathrm{SignedGoldenConjugateCoprimeCore}
\Longrightarrow
\mathrm{SignedBranchARefuter}
\Longrightarrow
\mathrm{BranchB\ counterexample}\to\bot
$$

である。

仮定 `hCore` は、任意の `SignedGoldenConjugateCoprimePacket` が存在すれば矛盾する、という contract である。0249 `signedBranchARefuter_of_goldenConjugateCoprimeCore` によって、この局所的な黄金整数 contradiction core は signed Branch-A normal form 全体を否定する `SignedBranchARefuter` へ持ち上げられる。

その refuter を既存の `branchB_false_of_signedBranchARefuter` に渡すと、FLT5 の counterexample data `hPack : CounterexamplePack x y z` と Branch-B 条件

$$
5\nmid(z-y)
$$

から `False` が得られる。

したがって 0250 自身は、新しい整除計算・ノルム計算・共役計算を含まない。これまでに構築された conjugate-coprime contradiction を、元の Branch-B 問題へ返す routing theorem である。

## 証明全体での役割

0241–0244 では、ramifier を除去した `beta` とその共役について

$$
\operatorname{GoldenRelPrime}(\beta,\overline\beta)
$$

が証明された。0245–0247 はその certificate を packet に束ね、normal form から certified packet を構成できるようにした。0248 は、その certified packet を受け取れば `False` を返す receiver contract を定義し、0249 はその receiver を `SignedBranchARefuter` へ持ち上げた。

0250 は、その 0249 の出力を既存の Branch-B routing theorem に渡す最終 facade である。したがってこの小ブロックの依存関係は

$$
\text{conjugate coprimality}
\to
\text{certified packet}
\to
\text{local contradiction core}
\to
\text{signed Branch-A refuter}
\to
\text{Branch-B contradiction}
$$

となる。

この theorem があることで、downstream consumer は normal-form packet の生成過程や `beta_relPrime_conj` の内部証明を意識せず、`SignedGoldenConjugateCoprimeCore` さえ与えれば Branch-B を閉じられる。

## 直接依存する定義・補題

proof が直接使う named theorem は二つである。

- 0249 `signedBranchARefuter_of_goldenConjugateCoprimeCore`
- `branchB_false_of_signedBranchARefuter`

statement 側では次の型・命題に依存する。

- 0248 `SignedGoldenConjugateCoprimeCore`
- `CounterexamplePack`
- `SignedBranchARefuter`
- 自然数整除 `5 ∣ z - y`
- `False`

直接の proof dependency は非常に浅く、

$$
\texttt{hCore}
\xrightarrow{\texttt{signedBranchARefuter\_of\_goldenConjugateCoprimeCore}}
\texttt{SignedBranchARefuter}
\xrightarrow{\texttt{branchB\_false\_of\_signedBranchARefuter}}
\bot
$$

という関数合成そのものである。

## 証明の流れ

proof は一つの `exact` だけで閉じる。

```lean
by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_goldenConjugateCoprimeCore hCore) hPack hBranch
```

1. `hCore` を 0249 に渡し、`SignedBranchARefuter` を得る。
2. 得られた refuter、`hPack`、`hBranch` を `branchB_false_of_signedBranchARefuter` に渡す。
3. 戻り値がちょうど `False` なので goal が閉じる。

途中で witness の展開、`rw`、`simp`、算術 tactic は不要である。

## Lean 固有の処理

`{x y z : ℕ}` は implicit parameter なので、`hPack : CounterexamplePack x y z` と `hBranch` から Lean が `x y z` を推論する。

また、

```lean
signedBranchARefuter_of_goldenConjugateCoprimeCore hCore
```

は theorem を関数として適用して `SignedBranchARefuter` 型の値を生成している。その値を次の theorem の第一引数へそのまま渡しているため、proof term はネストした関数適用として読める。

`exact` は生成した式の型が goal `False` と一致することを要求するだけであり、ここでは definitional reduction 以外の tactic automation を必要としない。

## 冗長・重複箇所

論理的には、0250 は 0249 と `branchB_false_of_signedBranchARefuter` の単純合成なので、新しい数学情報は追加していない。downstream で毎回

```lean
exact branchB_false_of_signedBranchARefuter
  (signedBranchARefuter_of_goldenConjugateCoprimeCore hCore) hPack hBranch
```

と書けば、この named theorem 自体を省略することもできる。

一方で facade theorem として残す価値は高い。

- contradiction core から Branch-B closure までを一つの名前で参照できる。
- routing の内部段階 `SignedBranchARefuter` を consumer から隠せる。
- upstream の packet/refuter 構成が変更されても Branch-B 側 API を保ちやすい。
- proof dependency graph 上で「この core が Branch-B を閉じる」という事実が明示される。

したがって、これは論理的重複ではあるが architectural API として意図的な冗長性と評価できる。

## 最適化候補

1. **現行 theorem を維持する**
   - proof は最短級で、routing の意味も theorem 名から明確である。

2. **term-style にする**

```lean
:= branchB_false_of_signedBranchARefuter
  (signedBranchARefuter_of_goldenConjugateCoprimeCore hCore) hPack hBranch
```

   `by exact` を省ける可能性がある。意味は変わらない。

3. **共通 routing helper を抽象化する**
   - `Core → SignedBranchARefuter → BranchB false` という形が複数 module で繰り返されるなら、generic lifting helper を置く余地がある。

4. **facade theorem を削除して直接 composition に統一する**
   - コード量は減るが、domain-specific な proof graph の読みやすさは落ちる。

現行 proof は既に十分小さいので、局所的な短縮より API の明瞭さを優先するのが自然である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自体が直接要求する Mathlib 表面は非常に小さく、主に

- 関数適用
- implicit arguments
- `False`
- 自然数と整除記法

だけである。専用 tactic も使わない。

ただし、この declaration が属する `SignedGoldenConjugateCoprime.lean` 全体では、黄金整数の整除・ノルム・共役・`Nat.Coprime`・整数/自然数 cast などを使うため、module 全体の最小 import は 0250 単独よりはるかに広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

可能だが、数学 proof の比較というより API architecture の比較に向いている。

候補は次の通り。

- A: 現行 named facade theorem
- B: downstream で 0249 と Branch-B routing theorem を直接 composition
- C: generic `Core → Refuter → BranchB false` helper を導入
- D: `SignedBranchARefuter` intermediate layer を隠す higher-level structure/API

比較軸は、proof term の短さよりも、依存関係の可視性、consumer 側の単純さ、refactor 耐性、theorem search のしやすさ、module 境界の明確さである。

この意味で、0250 は「短い theorem を残す価値」を測る Comparator challenge に適している。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenConjugateCoprime.lean` generated section である。

source では 0249 の直後に本 theorem があり、本 theorem の直後で `SignedGoldenConjugateCoprime.lean` が終了する。その次から `SignedGoldenFifthPower.lean` が始まる。

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし、本 theorem に対応する具体的 PDF ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

依存順の次は、次 module `SignedGoldenFifthPower.lean` の先頭にある **0251 `goldenOfInt_pow_five`** である。

```lean
@[simp] theorem goldenOfInt_pow_five (b : ℤ) :
    goldenOfInt (b ^ 5) = goldenPow (goldenOfInt b) 5 := by
  apply GoldenInt.ext
  · simp [goldenOfInt, goldenPow, goldenMul, goldenOne]
    ring
  · simp [goldenOfInt, goldenPow, goldenMul, goldenOne]
```

0250 までで conjugate-coprime packet から Branch-B contradiction へ戻す routing block が閉じる。0251 からは再び algebraic content に入り、整数埋め込みが第五冪を保存することを explicit golden API 上で確立し、`beta * conj(beta)` を埋め込み第五冪として表す準備へ進む。