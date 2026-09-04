# 0275 — `SignedGoldenRamifierStrippedPacket.zeroSector_snd_factor_eq`

## 宣言種別

これは **`theorem`** である。

`DkMath.FLT.Five.SignedGoldenZeroSector` に置かれた zero-sector の座標算術補題であり、packet の `beta` が pure fifth power `gamma^5` であるとき、その第二座標を `gamma.snd` と quartic factor `goldenFifthSndFactor` の積へ分解し、packet が保持する five-adic power-split data と正確に接続する。

## Lean の型

```lean
/-- Exact signed second-coordinate equation in the zero sector. -/
theorem SignedGoldenRamifierStrippedPacket.zeroSector_snd_factor_eq
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w)
    {gamma : GoldenInt} (hbeta : p.beta = goldenPow gamma 5) :
    gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd =
      -(5 : ℤ) ^ 6 * (p.exceptional.powerSplit.a : ℤ) ^ 10 := by
  have hsnd := congrArg (fun x : GoldenInt => x.snd) hbeta
  change p.beta.snd = (goldenPow gamma 5).snd at hsnd
  rw [p.beta_snd, goldenPow_five_snd, goldenFifthSndPoly_eq] at hsnd
  nlinarith
```

型を数学的に読む。`gamma = (r,s)` と書き、

$$
H(r,s)=\operatorname{goldenFifthSndFactor}(r,s)
$$

と置くと、仮定

$$
\beta=\gamma^5
$$

から

$$
s\,H(r,s)=-5^6 a^{10}
$$

を得る。ここで $a$ は `p.exceptional.powerSplit.a` である。

したがってこれは単なる可除性ではなく、符号・5 の指数・10 乗部分をすべて保持した **exact signed product equation** である。

## 数学的主張の意味

zero sector では unit factor が消えており、`beta` はそのまま fifth power

$$
\beta=\gamma^5
$$

である。一方、packet 自身は `beta.snd` に関する exact five-adic data を field `p.beta_snd` として保持している。

本 theorem はこの二つの記述を第二座標で比較する。

一方では packet 側の既知量、他方では fifth power の第二座標公式を使うことで、`gamma = (r,s)` の第二座標 $s$ と quartic factor $H(r,s)$ の積が、packet の power-split parameter $a$ の 10 乗と $5^6$ に一致することを得る。

この形が重要なのは、後段で絶対値を取れば自然数の積

$$
|s|\,|H(r,s)|=5^6 a^{10}
$$

へ移せるからである。そこから互いに素性を組み合わせることで、5 の全寄与を $|s|$ 側へ押し込み、残りをそれぞれ 10 乗へ分離する descent 用 normal form が得られる。

## 証明全体での役割

0273 は zero-sector base の norm を packet の `b` へ、0274 はその norm の 5 非可除性を zero-sector API へ移した。

0275 は初めて zero-sector fifth power の **第二座標そのものを積へ分解する**。

正本 source では直後に

```lean
theorem five_dvd_goldenFifthSndFactor_sub_norm_sq ...
```

が続き、その次の `zeroSector_five_not_dvd_sndFactor` で quartic factor $H$ の 5 非可除性を示す。さらに `zeroSector_natAbs_product_eq` は本 theorem に `Int.natAbs` を作用させて

$$
|s|\,|H|=5^6 a^{10}
$$

を得る。

したがって 0275 は、packet-level five-adic invariant を coordinate-level coprime factorization へ送り込む **主要な接続点** である。

## 直接依存する定義・補題

### `SignedGoldenRamifierStrippedPacket`

packet structure。ここでは特に `beta`, `exceptional.powerSplit.a`, および `beta_snd` を利用する。

### `p.beta_snd`

packet の `beta.snd` に対する exact formula を供給する field / theorem である。本 theorem はこの既知の第二座標値と `gamma^5` の第二座標を比較する。

正確な field の由来は前段 `SignedGoldenRamifierStripped.lean` にある。0275 自身はそれを再証明しない。

### `goldenPow_five_snd`

`GoldenInt` の fifth power の第二座標を polynomial expression に展開する theorem。

```lean
rw [..., goldenPow_five_snd, ...] at hsnd
```

で fifth-power coordinate を project-side polynomial へ落とす。

### `goldenFifthSndPoly_eq`

第二座標 polynomial を `gamma.snd * goldenFifthSndFactor ...` を含む factorized form へ移す補題である。

これにより downstream で重要な二因子

$$
s,
\qquad H(r,s)
$$

が明示される。

### `goldenFifthSndFactor`

fifth power の第二座標に現れる quartic factor。後続では norm の平方との mod 5 関係、`s` との互いに素性、そして 10 乗分離の対象になる。

### `congrArg`

等式 `hbeta : p.beta = goldenPow gamma 5` に第二座標射影 `(fun x => x.snd)` を適用するために使う Lean の一般合同原理。

## 証明または構築の流れ

### 1. `hbeta` を第二座標へ射影する

```lean
have hsnd := congrArg (fun x : GoldenInt => x.snd) hbeta
```

元の等式は `GoldenInt` 全体の等式である。本 theorem が必要とするのは第二座標だけなので、まず projection を掛ける。

数学的には

$$
\beta=\gamma^5
\Longrightarrow
\beta_2=(\gamma^5)_2
$$

である。

### 2. 型を期待する表記へ整える

```lean
change p.beta.snd = (goldenPow gamma 5).snd at hsnd
```

`congrArg` が生成した proposition を、後続 rewrite が素直に作用する syntactic form へ整える。

これは数学的変形ではなく Lean の表現調整である。

### 3. 両辺を既知の exact formula へ rewrite する

```lean
rw [p.beta_snd, goldenPow_five_snd, goldenFifthSndPoly_eq] at hsnd
```

左辺では packet invariant、右辺では fifth-power coordinate formula とその factorization を使う。

これにより `hsnd` は `gamma.snd`, `goldenFifthSndFactor`, `5`, `powerSplit.a` だけからなる整数多項式等式へ変わる。

### 4. `nlinarith` で係数整理を閉じる

```lean
nlinarith
```

残った仕事は整数環上の polynomial arithmetic と固定係数の整理であり、`nlinarith` が最終形

$$
sH=-5^6a^{10}
$$

へ正規化する。

この最後の一行には新しい数論的入力はない。

## Lean 固有の処理

### `congrArg` による射影

structure equality を `ext` で分解するのではなく、必要な coordinate だけを関数適用の合同性で取り出している。証明目的に対して非常に直接的である。

### `change ... at hsnd`

definitional equality の範囲で hypothesis の見た目を調整し、`rw` の matcher が依存補題を適用しやすい形にする。

### dot notation の `p.beta_snd`

packet parameter `p` を明示引数として書く代わりに theorem / field を method のように使用している。

### `nlinarith`

指数を含む式がすでに polynomial atom として現れているため、最終的な scalar rearrangement を自動化できる。ここで `ring` ではなく `nlinarith` を使うのは、rewrite 後の等式 `hsnd` を仮定として利用して目的等式を導くためである。

## 冗長・重複箇所

proof は 4 行であり、局所的な重複はほぼない。

ただし `congrArg` の直後の

```lean
change p.beta.snd = (goldenPow gamma 5).snd at hsnd
```

は、project definitions や simplifier attribute が十分整備されれば不要になる可能性がある。

また、`goldenPow_five_snd` と `goldenFifthSndPoly_eq` を連続 rewrite する形は、zero-sector 専用に直接

```lean
(goldenPow gamma 5).snd = 5 * gamma.snd * goldenFifthSndFactor ...
```

のような factorized coordinate lemma が存在すれば一段に畳める。しかし、その helper を追加する価値があるかは同じ二段 rewrite の再出現数次第である。

## 最適化候補

### 1. factorized fifth-coordinate API の直接化

`goldenPow_five_snd` と `goldenFifthSndPoly_eq` の組を頻繁に使うなら、fifth power の第二座標を直接 factorized form へ出す theorem を公開 API にすると downstream proof が短くなる。

### 2. 最終 arithmetic の明示化

Comparator や教育用途では `nlinarith` を残すより、rewrite 後の exact equation を `have` で命名し、`ring_nf` あるいは明示的な cancel lemma で $5^7$ から $5^6$ へ移る構造を見せる方が説明性は高い可能性がある。

ただし現行 proof の堅牢性と短さは優れているので、これは可読性との trade-off である。

### 3. `change` の除去可能性を検証

`simpa` または `change` 無しの `rw` が現行 Mathlib / project definitions で通るかは、Lean build を行っていないため **未確認** である。

## 必要 Mathlib import と import 最適化候補

対象ブランチの standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用している。

standalone manifest では本 theorem の元 module は `DkMath/FLT/Five/SignedGoldenZeroSector.lean` であり、その前に少なくとも `SignedGoldenRamifierStripped`, `SignedGoldenFifthPower`, `GoldenFifthPowerCoordinates`, `SignedGoldenSectorArithmetic` などが並ぶ。

0275 自身が直接必要とする Lean / Mathlib 機構は、structure projection、`congrArg`, rewriting、整数 polynomial arithmetic、`nlinarith` である。

ただし元 module の **最小 Mathlib import 集合は standalone artifact だけからは確定できない**。特に `nlinarith` と project-side golden arithmetic の import chain を分離して検証する必要がある。本実行では Lean build を行わないため、`import Mathlib` の具体的縮小案は候補に留める。

## 既存 PDF との対応

対象ブランチ `docs/pdf` には

- `FLT5-main-ja-v0-r1.pdf`
- `FLT5-main-en-v0-r1.pdf`

が存在することを確認した。

ただし今回の取得経路では PDF binary 本文を解析可能な形で取得できず、0275 の具体的ページ番号・節番号・本文中での同一式の表記は **未確認** である。したがって本稿では PDF の具体的位置を推測せず、技術内容はリポジトリ内 Lean 正本を第一根拠とする。

## Comparator challenge 化の可否

**可能。難度は低〜中程度。**

challenge としては次を与えるのがよい。

- `hbeta : p.beta = goldenPow gamma 5`
- `p.beta_snd`
- `goldenPow_five_snd`
- `goldenFifthSndPoly_eq`

そして goal を

```lean
gamma.snd * goldenFifthSndFactor gamma.fst gamma.snd =
  -(5 : ℤ) ^ 6 * (p.exceptional.powerSplit.a : ℤ) ^ 10
```

とする。

評価点は、

1. full `GoldenInt` equality から第二座標だけを適切に抽出できるか、
2. coordinate expansion と factorization lemma を正しい順で使えるか、
3. 最後の polynomial arithmetic を過剰な展開なしに閉じられるか、

の三点である。

`congrArg` を思いつく必要があるため、単なる `rw` challenge よりは一段良い Comparator 題材になる。

## 次に読むべき宣言

次は **0276 `five_dvd_goldenFifthSndFactor_sub_norm_sq`** を読むべきである。

```lean
theorem five_dvd_goldenFifthSndFactor_sub_norm_sq (gamma : GoldenInt) :
    (5 : ℤ) ∣
      goldenFifthSndFactor gamma.fst gamma.snd - goldenNorm gamma ^ 2 := by
  refine ⟨gamma.fst * gamma.snd ^ 2 * (gamma.fst + gamma.snd), ?_⟩
  simp only [goldenFifthSndFactor, goldenNorm]
  ring
```

0275 が exact product equation を作った後、0276 は quartic factor $H(r,s)$ と golden norm の平方が mod 5 で一致することを与える。これを 0274 の $5\nmid N(\gamma)$ と組み合わせることで、次段階の $5\nmid H(r,s)$ が導かれる。

このため依存順としては 0275 → 0276 → `zeroSector_five_not_dvd_sndFactor` が自然である。
