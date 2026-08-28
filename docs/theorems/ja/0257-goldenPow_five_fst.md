# 0257 — `goldenPow_five_fst`

## Lean の型

```lean
/-- Exact first coordinate of `gamma^5`. -/
theorem goldenPow_five_fst (gamma : GoldenInt) :
    (goldenPow gamma 5).fst = goldenFifthFstPoly gamma.fst gamma.snd := by
  simp [goldenPow, goldenMul, goldenOne, goldenFifthFstPoly]
  ring
```

これは `theorem` であり、黄金整数 `gamma` の第五冪を explicit raw API `goldenPow` で計算したとき、その第一座標が 0255 `goldenFifthFstPoly` と厳密に一致することを示す。

## 数学的主張

`gamma = p + qφ` と書くと、黄金整数では

$$
\varphi^2=\varphi+1
$$

なので、第五冪は

$$
\gamma^5=(p+q\varphi)^5=A(p,q)+B(p,q)\varphi
$$

と `1,φ` 基底へ還元できる。

0255 で第一座標多項式

$$
A(p,q)=p^5+10p^3q^2+10p^2q^3+10pq^4+3q^5
$$

を `goldenFifthFstPoly p q` と定義した。本 theorem は、それが単なる候補式ではなく、実際の raw fifth power `goldenPow gamma 5` の `.fst` と一致することを証明する。

すなわち

$$
(\gamma^5)_{\mathrm{fst}}
=
\mathrm{goldenFifthFstPoly}(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}})
$$

である。

## 証明全体での役割

0255・0256 は第五冪の二座標を整数多項式として名前付けしたが、それだけでは `goldenPow gamma 5` との意味的接続はまだない。0257 と次の 0258 `goldenPow_five_snd` が、その bridge を完成させる。

本 theorem によって、以後の proof は複雑な raw recursion `goldenPow` を毎回展開せず、第一座標については `goldenFifthFstPoly` へ rewrite して整数多項式算術へ落とせる。

後続の unit-sector block では、例えば `φ * gamma^5`、`φ^2 * gamma^5` などの第二座標が、第一座標多項式 `A` と第二座標多項式 `B` の線形結合として現れる。その際、

```lean
rw [goldenPow_five_fst, goldenPow_five_snd]
```

によって raw fifth power の座標を完全に named polynomial API へ移す。

さらに後段では modulo 5 の議論において `goldenFifthFstPoly` が

$$
A(p,q)\equiv p^5+3q^5 \pmod 5
$$

型の線形情報へ落とされ、非零 unit sector を排除する材料になる。本 theorem はその算術側へ入る正式な入口である。

## 直接依存する定義・補題

Lean proof が直接参照するものは次の通りである。

- `GoldenInt`
- `goldenPow`
- `goldenMul`
- `goldenOne`
- 0255 `goldenFifthFstPoly`
- `simp`
- `ring`

数学的背景としては 0165 `golden_phi_sq` の

$$
\varphi^2=\varphi+1
$$

が本質にあるが、proof では named theorem を rewrite しているわけではない。`goldenMul` の座標定義自体がすでにこの還元関係を組み込んでいるため、`goldenPow` を展開すると最初から `1,φ` 座標の整数多項式へ落ちる。

## 証明の流れ

proof は二段階だけである。

```lean
by
  simp [goldenPow, goldenMul, goldenOne, goldenFifthFstPoly]
  ring
```

1. `simp` で `goldenPow gamma 5` の再帰を固定指数 5 について展開する。
2. 各乗法を `goldenMul` の明示座標式へ展開する。
3. `goldenOne` と `goldenFifthFstPoly` も展開する。
4. 残った目標は `gamma.fst`, `gamma.snd` に関する整数多項式恒等式になる。
5. `ring` が両辺を正規形へ変換して等式を閉じる。

つまり証明の数学的内容は、第五冪を explicit coordinate ring で展開して係数比較することそのものである。

## Lean 固有の処理

`goldenPow` は通常の `^` ではなく、この development が用意した raw recursion である。そのため指数 5 を固定した本 theorem では、`simp [goldenPow]` が再帰を有限回ほどいてくれる。

また `goldenMul` は

$$
(a+b\varphi)(c+d\varphi)
=(ac+bd)+(ad+bc+bd)\varphi
$$

という二座標積を定義している。これを repeated power に展開すると expression は大きくなるが、すべて整数多項式なので `ring` に渡せる。

重要なのは、proof が `GoldenInt.ext` を使っていない点である。statement 自体が `.fst` の scalar equality なので、最初から第一座標だけを扱えばよい。

また 0160 `golden_pow_eq` により `goldenPow gamma 5 = gamma ^ 5` は既知だが、本 theorem は raw coordinate API のまま展開する設計を選んでいる。これにより typeclass elaboration を介さず、座標定義との対応が監査しやすい。

## 冗長・重複箇所

0257 と次の 0258 `goldenPow_five_snd` はほぼ同型の theorem である。

- 0257: 第一肖像 `.fst`
- 0258: 第二座標 `.snd`

どちらも

```lean
simp [goldenPow, goldenMul, goldenOne, ...]
ring
```

で閉じるため、proof pattern は重複している。

理論上は、例えば

```lean
theorem goldenPow_five_coords (gamma : GoldenInt) :
    goldenPow gamma 5 =
      ⟨goldenFifthFstPoly gamma.fst gamma.snd,
        goldenFifthSndPoly gamma.fst gamma.snd⟩ := by
  ext <;> simp [...] <;> ring
```

という pair theorem を一つ置き、0257・0258 を projection corollary として導く設計も可能である。

一方、現行の scalar theorem 分離には、downstream が第一座標・第二座標を別々に rewrite しやすいという利点がある。特に unit-sector arithmetic では第二座標の式に第一座標多項式が部分的に現れるため、scalar rewrite theorem は実用的である。

## 最適化候補

1. **二座標をまとめた theorem を追加する**
   - `goldenPow_five_coords` を canonical theorem とし、0257・0258 を `rfl` / `simpa` 的な projection theorem にする。

2. **標準冪 `gamma ^ 5` 版を追加する**
   - 0160 `golden_pow_eq` を介して

```lean
(gamma ^ 5).fst = goldenFifthFstPoly gamma.fst gamma.snd
```

   を公開すれば、Mathlib 標準 notation 側の theorem として downstream が使いやすくなる可能性がある。

3. **一般 recurrence から導く**
   - `(p+qφ)^n` の二座標 recurrence を定義し、`n=5` を特殊化する方法もある。
   - 再利用性は増えるが、FLT5 専用 proof では現行の explicit polynomial の方が読みやすい。

4. **`ring` 前の `simp` 展開量を削減する**
   - 補助 lemma で `goldenPow gamma 5` の座標を少しずつ計算すれば proof term の局所性は上がる可能性がある。
   - ただし現行 theorem は短く、保守性も高い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem 自身で必要な外部機能は主に

- integer ring arithmetic
- `simp`
- `ring`

である。したがって宣言単独なら `Mathlib` 全体よりかなり狭い import で足りる可能性が高い。

ただし `GoldenFifthPowerCoordinates.lean` 全体では後続に整除、`Prime`、`Fin 5`、`fin_cases`、`omega`、`grind` などが現れるため、module 単位の最小 import は本 theorem 単独より広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 `simp` + `ring`
- B: 二座標 theorem を `ext` で一括証明し projection する
- C: 0160 `golden_pow_eq` を使い標準 `^` へ移してから証明する
- D: 再帰 recurrence から `n=5` を導く
- E: `norm_num` / `ring_nf` を中心に explicit expansion を制御する

比較軸は、proof term の短さ、raw API 依存度、標準 algebra API との親和性、展開式の監査性、0258 との重複量、downstream rewrite usability である。

特に A と B の比較は、「座標ごとの consumer-friendly theorem を個別に持つ設計」と「pair theorem を canonical source of truth にする設計」の違いを測るよい課題になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenFifthPowerCoordinates.lean` generated section である。

source では 0255 `goldenFifthFstPoly`、0256 `goldenFifthSndPoly` の直後に本 theorem が置かれ、その次に 0258 `goldenPow_five_snd` が続く。

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的な PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0258 `goldenPow_five_snd`** である。

```lean
theorem goldenPow_five_snd (gamma : GoldenInt) :
    (goldenPow gamma 5).snd = goldenFifthSndPoly gamma.fst gamma.snd := by
  simp [goldenPow, goldenMul, goldenOne, goldenFifthSndPoly]
  ring
```

0257 が第五冪の第一座標を named polynomial API と接続したので、0258 では第二座標について同じ bridge を完成させる。これにより `gamma^5` の二座標が完全に 0255・0256 の explicit polynomial pair へ落ちる。