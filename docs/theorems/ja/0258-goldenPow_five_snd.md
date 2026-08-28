# 0258 — `goldenPow_five_snd`

## Lean の型

```lean
/-- Exact second coordinate of `gamma^5`; it contains the visible factor `5*q`. -/
theorem goldenPow_five_snd (gamma : GoldenInt) :
    (goldenPow gamma 5).snd = goldenFifthSndPoly gamma.fst gamma.snd := by
  simp [goldenPow, goldenMul, goldenOne, goldenFifthSndPoly]
  ring
```

これは `theorem` であり、黄金整数 `gamma` の第五冪を raw API `goldenPow` で計算したとき、その第二座標が 0256 `goldenFifthSndPoly` と厳密に一致することを示す。

## 数学的主張

`gamma = p + qφ` と書く。黄金整数では

$$
\varphi^2=\varphi+1
$$

なので、第五冪は

$$
\gamma^5=(p+q\varphi)^5=A(p,q)+B(p,q)\varphi
$$

と `1,φ` 基底へ還元できる。

0256 では第二座標多項式を

$$
B(p,q)=5q\left(p^4+2p^3q+4p^2q^2+3pq^3+q^4\right)
$$

として `goldenFifthSndPoly p q` と定義した。本 theorem は、それが実際の raw fifth power `goldenPow gamma 5` の `.snd` と一致することを証明する。

すなわち

$$
(\gamma^5)_{\mathrm{snd}}
=
\mathrm{goldenFifthSndPoly}(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}})
$$

である。

特に右辺は定義上 `5 * q * (...)` の形なので、第五冪の第二座標には常に可視な因子 `5` が含まれる。

## 証明全体での役割

0255・0256 は第五冪の二座標多項式を定義し、0257・0258 がそれらを実際の `goldenPow gamma 5` と接続する。0257 が第一座標、今回の 0258 が第二座標を担当するため、ここで

$$
\gamma^5
\longleftrightarrow
\bigl(A(p,q),B(p,q)\bigr)
$$

という explicit polynomial representation が完全に成立する。

このうち第二座標は特に重要である。`goldenFifthSndPoly` は最初から

$$
5q
$$

を因子として持つため、five-adic sector arithmetic では `gamma^5` の第二座標から直接 5 の整除性を読み取れる。

正本 source の後続では、`golden_unit_zero_mul_fifth_snd`、`golden_unit_one_mul_fifth_snd`、`golden_unit_two_mul_fifth_snd`、`golden_unit_three_mul_fifth_snd`、`golden_unit_four_mul_fifth_snd` が `goldenPow_five_fst` と本 theorem を rewrite に使い、`φ^i * gamma^5` の第二座標を第一・第二座標多項式の線形結合へ落とす。

さらに後段では `five_dvd_goldenFifthSndPoly` により

$$
5\mid B(p,q)
$$

を公開し、非零 unit sector の排除や zero-sector factorization の入力として使う。

## 直接依存する定義・補題

Lean proof が直接参照するものは次の通りである。

- `GoldenInt`
- `goldenPow`
- `goldenMul`
- `goldenOne`
- 0256 `goldenFifthSndPoly`
- `simp`
- `ring`

数学的背景には 0165 `golden_phi_sq` の

$$
\varphi^2=\varphi+1
$$

がある。ただし proof はこの theorem を明示的に rewrite せず、`goldenMul` の座標定義に埋め込まれた還元則を直接展開している。

## 証明の流れ

proof は 0257 と同型である。

```lean
by
  simp [goldenPow, goldenMul, goldenOne, goldenFifthSndPoly]
  ring
```

1. `simp [goldenPow]` で指数 5 の再帰を有限回展開する。
2. `goldenMul` を二座標乗法へ展開する。
3. `goldenOne` と `goldenFifthSndPoly` を展開する。
4. 目標を `gamma.fst`, `gamma.snd` に関する整数多項式恒等式へ落とす。
5. `ring` が両辺を正規化して等式を閉じる。

したがって証明の数学的内容は、黄金基底における `(p+qφ)^5` の第二座標係数計算そのものである。

## Lean 固有の処理

`goldenPow` は Mathlib 標準の `^` ではなく、この development 固有の raw recursion である。固定指数 5 なので `simp [goldenPow]` による完全展開が実用的である。

statement は `.snd` の scalar equality なので `GoldenInt.ext` は不要であり、第二座標だけを直接証明している。

また 0160 `golden_pow_eq` により `goldenPow gamma 5 = gamma ^ 5` は既知だが、本 theorem は raw coordinate API のまま計算する。これは explicit coordinate formula の監査性を高く保つ設計である。

`ring` が使えるのは、展開後に現れるすべての量が `ℤ` 上の多項式だからである。

## 冗長・重複箇所

0257 `goldenPow_five_fst` と本 theorem は proof pattern がほぼ完全に重複している。

- 0257: `.fst` と `goldenFifthFstPoly`
- 0258: `.snd` と `goldenFifthSndPoly`

理論上は二座標を一つにまとめて

```lean
theorem goldenPow_five_coords (gamma : GoldenInt) :
    goldenPow gamma 5 =
      ⟨goldenFifthFstPoly gamma.fst gamma.snd,
        goldenFifthSndPoly gamma.fst gamma.snd⟩ := by
  ext <;> simp [goldenPow, goldenMul, goldenOne,
    goldenFifthFstPoly, goldenFifthSndPoly] <;> ring
```

のような canonical theorem を置き、0257・0258 を projection corollary にする設計も可能である。

一方、現行の scalar theorem 分離は downstream で `.fst` / `.snd` を個別に rewrite しやすい。特に unit-sector arithmetic は第二座標だけを頻繁に読むため、本 theorem の独立 API は有用である。

## 最適化候補

1. **二座標 theorem を canonical source にする**
   - proof 重複を減らし、0257・0258 を薄い projection theorem にできる。

2. **標準冪 `gamma ^ 5` 版を公開する**
   - 0160 `golden_pow_eq` を介して標準 algebra notation 側から使いやすくする。

3. **visible factor 5 を直接 API 化する**
   - 後続の `five_dvd_goldenFifthSndPoly` と合わせ、`5 ∣ (goldenPow gamma 5).snd` を直接公開すれば consumer proof が短くなる可能性がある。

4. **一般指数 recurrence へ抽象化する**
   - `n` 乗の二座標 recurrence を作り `n=5` を特殊化する設計も可能だが、FLT5 専用では現行 explicit formula の方が読みやすい。

5. **raw / standard API 境界を整理する**
   - `goldenPow` / `goldenMul` と `^` / `*` の双方を持つ現在の設計を、bridge theorem 群でさらに明示的に整理できる。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。

本 theorem 自身で必要な外部機能は主に

- 整数環の多項式算術
- `simp`
- `ring`

である。宣言単独なら `Mathlib` 全体よりかなり小さい import で足りる可能性が高い。

ただし `GoldenFifthPowerCoordinates.lean` 全体では後続に整除、`Fin 5`、`fin_cases`、`omega`、`grind` などが現れるため、module 単位の最小 import は本 theorem 単独より広い。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は次の通り。

- A: 現行 `simp` + `ring`
- B: 二座標 theorem を `ext` で一括証明して projection する
- C: 0160 `golden_pow_eq` を使い標準 `^` へ移してから証明する
- D: 一般 recurrence から `n=5` を導く
- E: `ring_nf` 等で explicit expansion の正規化方法を比較する

比較軸は proof 長、展開量、raw API 依存度、標準 algebra API との親和性、0257 との重複量、downstream rewrite usability である。

特に A と B の比較は、consumer-friendly な座標別 theorem と pair theorem を source of truth にする設計の差を測るよい課題になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/GoldenFifthPowerCoordinates.lean` generated section である。

正本 source では 0257 `goldenPow_five_fst` の直後に本 theorem が置かれ、その直後は `goldenPhi_pow_zero` である。

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的な PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0259 `goldenPhi_pow_zero`** である。

```lean
theorem goldenPhi_pow_zero : goldenPow goldenPhi 0 = ⟨1, 0⟩ := rfl
```

0257・0258 で `gamma^5` の二座標が explicit polynomial pair に落ちたので、0259 からは unit class `1,φ,φ^2,φ^3,φ^4` の具体的代表を準備する block に入る。まず指数 0 の代表 `1` を確定し、その後各 `φ^i * gamma^5` の第二座標を sector ごとに展開していく。