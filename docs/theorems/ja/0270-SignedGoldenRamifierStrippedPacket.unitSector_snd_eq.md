# 0270 — `SignedGoldenRamifierStrippedPacket.unitSector_snd_eq`

## 宣言種別

これは `theorem` である。

名前空間付きの宣言名は `SignedGoldenRamifierStrippedPacket.unitSector_snd_eq` であり、`SignedGoldenRamifierStrippedPacket` に対する packet-level theorem として配置されている。

## Lean の型

```lean
theorem SignedGoldenRamifierStrippedPacket.unitSector_snd_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {i : Fin 5} {gamma : GoldenInt}
    (hbeta : p.beta =
      goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)) :
    (goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)).snd =
      -(5 : ℤ) ^ 7 * (p.exceptional.powerSplit.a : ℤ) ^ 10 := by
  rw [← hbeta, p.beta_snd]
```

型としては、`p.beta` が有限 unit sector の代表 `goldenPhi ^ i` と第五冪 `gamma ^ 5` の積で表されるなら、その積の第二座標は packet がすでに保持している exact five-adic coordinate

$$
-5^7 a^{10}
$$

に等しい、と主張している。ここで

```lean
p.exceptional.powerSplit.a
```

が式中の $a$ である。

`i : Fin 5` なので sector index は $0,1,2,3,4$ のいずれかに限定されるが、本 theorem 自身は sector ごとの具体座標計算を行わない。`hbeta` を通じて `p.beta` と sector expression が同一であることだけを使う。

## 数学的主張

`GoldenInt` の元 `beta` が

$$
\beta=\varphi^i\gamma^5,
\qquad i\in\{0,1,2,3,4\}
$$

という unit-sector 表現を持つとする。

一方、`SignedGoldenRamifierStrippedPacket` の構築段階ですでに

$$
\operatorname{snd}(\beta)
=-5^7a^{10}
$$

という exact coordinate が保存されている。

したがって等しい元の第二座標を取れば、ただちに

$$
\operatorname{snd}(\varphi^i\gamma^5)
=-5^7a^{10}
$$

を得る。

本 theorem の数学的内容は新しい多項式恒等式ではない。核心は、前段で構築済みの packet invariant を、後段の finite unit-sector representation に **搬送すること** にある。

## 証明全体での役割

0264–0268 では、`gamma^5 = A + Bφ` と書いたとき、正の五 sector

$$
1,\varphi,\varphi^2,\varphi^3,\varphi^4
$$

に対する第二座標を

$$
B,\quad A+B,\quad A+2B,\quad 2A+3B,\quad 3A+5B
$$

として具体化した。

0269 `golden_neg_unit_mul_fifth_snd` は負の unit representative を正の representative の符号反転へ還元した。

0270 で初めて、その finite-sector arithmetic と `SignedGoldenRamifierStrippedPacket` が保持する five-adic packet invariant が直接接続される。

packet 側には

$$
\operatorname{snd}(\beta)=-5^7a^{10}
$$

という強い five-adic 情報があり、sector 側には `beta = φ^i γ^5` という表現がある。本 theorem はこの二つを同じ式へ重ねる橋である。

後続の nonzero-sector 排除では、各 sector の explicit coordinate formula と本 theorem の右辺を比較することで、$5$ 可除性を `goldenFifthFstPoly` / `goldenFifthSndPoly` の組合せへ押し込み、最終的に norm 側の条件と衝突させる。その意味で 0270 は「座標計算」と「packet の five-adic 不変量」の接着点である。

## 直接依存する定義・補題

証明で直接使われるものは非常に少ない。

- `SignedGoldenRamifierStrippedPacket`
  - ramifier `tau` を一度除去した exceptional packet。
  - `beta : GoldenInt`、`exceptional`、および exact coordinate field `beta_snd` を保持する。
- `SignedGoldenRamifierStrippedPacket.beta_snd`
  - 実際には structure field として保存されている。
  - 正本では

```lean
beta_snd : beta.snd =
  -(5 : ℤ) ^ 7 * (exceptional.powerSplit.a : ℤ) ^ 10
```

  という形である。
- `GoldenInt`
  - 黄金整数 $a+b\varphi$ の座標モデル。
- `goldenPhi`
  - 黄金比元 $\varphi$ の `GoldenInt` 表現。
- `goldenPow`
  - `GoldenInt` の自然数冪 API。
- `goldenMul`
  - `GoldenInt` の乗法 API。
- `Fin 5`
  - sector index を $0$ から $4$ に制限する有限型。
- 仮定 `hbeta`
  - packet の `beta` と unit-sector fifth-power expression を同一視する bridge hypothesis。

なお、本 theorem は 0259–0269 の個別 theorem を証明スクリプト中では直接呼ばない。それらは後段で `i` を具体化して sector formula を展開するときに効く。0270 自身は packet invariant の搬送だけを担当する。

## 証明または構築の流れ

証明は一行である。

```lean
rw [← hbeta, p.beta_snd]
```

最初の rewrite

```lean
rw [← hbeta]
```

では、goal 左辺

```lean
(goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)).snd
```

を `p.beta.snd` に置き換える。

仮定は

```lean
hbeta : p.beta = sectorExpression
```

という向きなので、左辺の `sectorExpression` を `p.beta` に戻すために `← hbeta` と逆向き rewrite を使う。

これで goal は本質的に

```lean
p.beta.snd =
  -(5 : ℤ) ^ 7 * (p.exceptional.powerSplit.a : ℤ) ^ 10
```

になる。

次の

```lean
rw [p.beta_snd]
```

で packet field の exact coordinate equation を適用し、goal が閉じる。

証明中に `ring`、`omega`、`norm_num`、case split、sector enumeration は一切不要である。

## Lean 固有の処理

Lean 的に重要なのは rewrite の **向き** である。

`hbeta` は packet 内部の `beta` から sector expression への等式だが、goal は sector expression の `.snd` について述べる。したがって `rw [hbeta]` ではなく `rw [← hbeta]` が必要になる。

また、等式の両辺へ明示的に `congrArg (fun x => x.snd)` を適用していない点も特徴である。Lean の rewriting は部分式の内部まで作用するため、

```lean
sectorExpression.snd
```

の `sectorExpression` 自体を `p.beta` へ書き換えれば、そのまま `p.beta.snd` が得られる。

その後は structure field `p.beta_snd` が goal と完全に一致する。つまり theorem の強さは tactic の複雑さではなく、前段で packet の field として invariant を正確な型で保存しておいた設計に由来する。

## 冗長・重複箇所

本 theorem 自体に実質的な冗長性はない。二つの rewrite がそれぞれ別の役割を持つ。

1. `← hbeta` が representation から packet object へ戻す。
2. `p.beta_snd` が packet object から exact five-adic coordinate を読む。

一見すると後続 theorem の中で毎回

```lean
rw [← hbeta, p.beta_snd]
```

と直接書いてもよさそうに見える。しかし `unitSector_snd_eq` という名前を与えることで、後続の sector arithmetic は `SignedGoldenRamifierStrippedPacket` の内部構築を知らずに「sector expression の第二座標は固定された five-adic 値」という API として利用できる。

したがって theorem 化には重複除去以上に abstraction boundary を作る意味がある。

## 最適化候補

証明コードはすでにほぼ最小であり、短縮の利益は小さい。

例えば理論上は

```lean
simpa [hbeta] using p.beta_snd
```

あるいは等式の向きを調整した `simpa` 系の proof を試す余地はある。しかし `hbeta` の rewrite direction と simplifier の挙動に依存するため、現行

```lean
rw [← hbeta, p.beta_snd]
```

の方が意図が明示的で安定している。

設計上の一般化候補として、任意の expression `x : GoldenInt` に対し `p.beta = x` なら `x.snd = ...` を返す generic transport lemma を作ることもできる。しかし本 theorem の目的は `Fin 5` sector representation を API として固定することにあるため、一般化すると後続の文脈情報を失う。

よって現状は「これ以上短くする」よりも、sector-specific bridge として名前を保持する方が良い。

## 必要 Mathlib import と import 最適化候補

確認できた standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

本 theorem 自体が必要とする Lean / Mathlib 機能は非常に軽く、主として

- equality rewriting (`rw`)
- `Fin 5`
- `Nat`, `Int`
- 既存の project-side `GoldenInt` / packet definitions

である。

`ring` や `omega` などの tactic は本 theorem では使用しない。

一方、正本 standalone は多数の生成 module を一つへ連結した artifact であり、元の `SignedGoldenSectorArithmetic.lean` の個別 import 宣言そのものは今回のリポジトリ内容から確認できなかった。そのため「最小 Mathlib import はこれ」と断定はできない。

import 最適化を行うなら、`SignedGoldenRamifierStrippedPacket` と golden unit/fifth-power API を供給する直前の project modules、および基本的な algebra / finite type infrastructure まで絞れる可能性が高い。ただし実際の最小集合は Lean build なしには確認できない。

## Comparator challenge 化の可否

可能である。難度は低いが、proof engineering の比較題材として有用である。

challenge goal としてそのまま

```lean
theorem SignedGoldenRamifierStrippedPacket.unitSector_snd_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {i : Fin 5} {gamma : GoldenInt}
    (hbeta : p.beta =
      goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)) :
    (goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5)).snd =
      -(5 : ℤ) ^ 7 * (p.exceptional.powerSplit.a : ℤ) ^ 10 := by
  ...
```

を与えた場合、比較点は次になる。

1. `congrArg` で `.snd` 等式を明示的に作ってから `p.beta_snd` と連結する proof。
2. `simpa` で等式 transport を自動化する proof。
3. 現行の `rw [← hbeta, p.beta_snd]` という二段 rewrite。

特に「仮定の等式をどちら向きに rewrite すべきか」「structure field に invariant が既に保存されていることを認識できるか」が Comparator の良い評価点になる。

大規模数学 challenge ではないが、proof search が不要な展開計算へ迷走するか、既存 invariant を即座に再利用できるかを見るには適している。

## PDF との対応

対象ブランチには次の PDF が存在することを確認した。

- `docs/pdf/FLT5-main-ja-v0-r1.pdf`
- `docs/pdf/FLT5-main-en-v0-r1.pdf`

ただし今回の環境では GitHub 上の PDF 本文を解析可能な形で取得できず、0270 に対応する具体的ページ・節番号や記述との一対一照合は確認できなかった。そのため PDF の内容を推測して補ってはいない。

本稿の技術的主張、Lean 型、依存関係、証明フローについては、対象ブランチ上の `Flt5DkMath/FLT5StandAlone.lean` を正本としている。

## 次に読むべき宣言

次は `SignedGoldenUnitFifthPowerExclusion` である。

宣言種別は `abbrev` で、正本では

```lean
abbrev SignedGoldenUnitFifthPowerExclusion : Prop :=
  ∀ {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    (epsilon gamma : GoldenInt),
    GoldenUnit epsilon →
    p.beta = goldenMul epsilon (goldenPow gamma 5) →
    False
```

と定義されている。

意味は「どの ramifier-stripped packet の `beta` も、unit × fifth power ではありえない」という再利用可能な contradiction contract である。

0270 で packet の exact second coordinate を finite sector expression へ搬送できるようになったので、次はその sector arithmetic をまとめて `beta = ε γ^5` 全体を排除する proposition interface へ進む。