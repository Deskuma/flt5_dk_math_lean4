# 0251 — `goldenOfInt_pow_five`

## Lean の型

```lean
/-- Integer embedding respects fifth powers in the explicit golden API. -/
theorem goldenOfInt_pow_five (b : ℤ) :
    goldenOfInt (b ^ 5) = goldenPow (goldenOfInt b) 5 := by
  apply GoldenInt.ext
  · simp [goldenOfInt, goldenPow, goldenMul, goldenOne]
    ring
  · simp [goldenOfInt, goldenPow, goldenMul, goldenOne]
```

これは `theorem` であり、整数埋め込み `goldenOfInt : ℤ → GoldenInt` が第五冪を保存することを、raw 黄金整数 API `goldenPow` の形で示す。

## 数学的主張

`goldenOfInt b` は整数 $b$ を黄金整数環へ

$$
b \longmapsto b+0\varphi
$$

と埋め込む。したがって通常の環論では当然

$$
(b^5)+0\varphi=(b+0\varphi)^5
$$

であり、本 theorem はこの事実を Lean の明示座標モデルで公開する。

すなわち

$$
\operatorname{goldenOfInt}(b^5)
=
\operatorname{goldenPow}(\operatorname{goldenOfInt}(b),5).
$$

左辺は座標 $(b^5,0)$、右辺も `goldenMul` を五回反復すると第二座標が常に $0$ のまま、第一座標だけが整数の第五冪となる。

## 証明全体での役割

0241–0250 では `beta` とその共役の相対素性を certified state として構築し、contradiction routing まで整理した。0251 から始まる `SignedGoldenFifthPower.lean` では、その相対素性を fifth-power factor extraction へ接続する。

stripped packet はすでに

$$
N(\beta)=b^5
$$

を保持している。また一般公式

$$
\beta\overline{\beta}=N(\beta)
$$

があるので、環内部では

$$
\beta\overline{\beta}=\operatorname{goldenOfInt}(b^5)
$$

となる。本 theorem により右辺を

$$
\operatorname{goldenOfInt}(b)^5
$$

へ書き換えられる。これにより直後の 0252 で

$$
\beta\overline{\beta}=z^5
$$

という「相対素な二因子の積が第五冪」という標準的な因子分解問題へ正確に落とせる。

したがって 0251 は、整数ノルム側の第五冪と黄金整数環内部の第五冪を接続する representation bridge である。

## 直接依存する定義・補題

直接依存する主な宣言は次の通り。

- `GoldenInt`
- `GoldenInt.ext`
- 0162 `goldenOfInt`
- raw power `goldenPow`
- raw multiplication `goldenMul`
- `goldenOne`
- `simp`
- `ring`

証明自体は、既存の抽象的な cast theorem や `map_pow` を使わず、座標定義を直接展開している。

概念的には

$$
\text{integer embedding}
+
\text{explicit golden multiplication}
\Longrightarrow
\text{fifth-power preservation}
$$

という非常に局所的な bridge である。

## 証明の流れ

証明は `GoldenInt.ext` によって二座標へ分解する。

```lean
apply GoldenInt.ext
```

### 第一座標

```lean
· simp [goldenOfInt, goldenPow, goldenMul, goldenOne]
  ring
```

`goldenPow` と `goldenMul` を展開すると、第二座標が $0$ であるため混合項が消え、第一座標に整数乗法だけが残る。`simp` で定義展開した後、最終的な整数多項式恒等式を `ring` が閉じる。

### 第二座標

```lean
· simp [goldenOfInt, goldenPow, goldenMul, goldenOne]
```

整数埋め込みは第二座標が常に $0$ なので、第五冪を取っても第二座標は $0$ のままである。こちらは `ring` すら不要で `simp` のみで閉じる。

## Lean 固有の処理

`goldenPow` は標準 `Pow.pow` とは別の raw 再帰関数である。ただし 0160 `golden_pow_eq` により標準冪と定義的に接続されている。

同様に `goldenOfInt` は raw coordinate embedding であり、`AddGroupWithOne GoldenInt` の `intCast` も同じ座標規則 $(b,0)$ を持つ。

本 proof はこの二つの標準 API bridge を使わず、`goldenOfInt` / `goldenPow` / `goldenMul` を直接展開する。そのため依存は局所的で監査しやすい一方、標準環 API との重複が表面化している。

`GoldenInt.ext` を使うことで structure equality を二つの整数等式へ還元し、第一座標だけ `ring` を必要としている。

## 冗長・重複箇所

数学的には、本 theorem は標準整数 cast が冪を保存する一般則と重複している。

既に

```lean
goldenOfInt b = (b : GoldenInt)
```

に相当する bridge を用意できれば、標準環上では

$$
((b^5 : \mathbb Z) : GoldenInt)=((b : GoldenInt))^5
$$

は cast / power の一般 API からほぼ自動的に得られる可能性が高い。

また 0160 `golden_pow_eq` により `goldenPow x 5 = x ^ 5` へ移せるので、raw power を直接展開する現在の proof はやや低レベルである。

ただし standalone 証明の監査性という観点では、整数軸上で黄金乗法が通常の整数乗法へ退化することを座標で明示する現行証明にも価値がある。

## 最適化候補

1. `goldenOfInt_eq_intCast` のような bridge theorem を追加し、標準 cast API から証明する。
2. 0160 `golden_pow_eq` を利用して `goldenPow` の直接展開を避ける。
3. より一般に、任意の `n : ℕ` について

```lean
goldenOfInt (b ^ n) = goldenPow (goldenOfInt b) n
```

を証明し、0251 を `n=5` の特殊化とする。
4. `goldenOfInt` を `RingHom ℤ GoldenInt` として bundle し、`map_pow` を利用する。

FLT5 では指数 5 しか downstream に必要ないため、現行 theorem は依存を小さく保つ pragmatic な設計でもある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 自身が直接必要とする Mathlib 表面は主に

- structure extensionality
- `simp`
- `ring`
- 整数環の基本演算

である。

高度な数論 API は不要である。宣言単独なら `Mathlib` 全体よりかなり小さい import で足りる可能性が高いが、実際の `SignedGoldenFifthPower.lean` は周辺の golden-order API を import して使うため、最小 import は module 単位で測る必要がある。

今回は Lean build を行わないため、正確な最小 import 集合は未検証であり、最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。比較候補は明瞭である。

- A: 現行 `ext + simp + ring` の明示座標 proof
- B: `golden_pow_eq` と標準 cast を使う proof
- C: `goldenOfInt` を `RingHom` 化して `map_pow` で証明
- D: 任意指数版を先に証明して `n=5` に特殊化

比較軸は、proof 長、依存深度、raw API の可視性、Mathlib 標準 API の再利用率、将来の一般化可能性、standalone 監査性である。

特に A と C の比較は、「明示座標で一点を証明する設計」と「環準同型として抽象化する設計」の差を測る良い Comparator challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenFifthPower.lean` generated section である。

正本 source では 0250 の後に module が `SignedGoldenFifthPower.lean` へ移り、その先頭 theorem として本宣言が置かれていることを確認した。

対象ブランチには `docs/pdf/FLT5-main-ja-v0-r1.pdf` と `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし本 theorem に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0252 `SignedGoldenRamifierStrippedPacket.beta_mul_conj_eq_fifth`** である。

```lean
theorem SignedGoldenRamifierStrippedPacket.beta_mul_conj_eq_fifth
    {u v w : ℕ} (p : SignedGoldenRamifierStrippedPacket u v w) :
    goldenMul p.beta (goldenConj p.beta) =
      goldenPow (goldenOfInt (p.exceptional.powerSplit.b : ℤ)) 5 := by
  rw [golden_mul_conj, p.beta_norm, goldenOfInt_pow_five]
```

0251 で整数埋め込みと第五冪の互換性が得られたので、0252 は

$$
\beta\overline{\beta}=N(\beta)=b^5
$$

を黄金整数環内部の genuine fifth-power factorization

$$
\beta\overline{\beta}=(\operatorname{goldenOfInt} b)^5
$$

へ昇格する。これが coprime-factor theorem に渡す直接の入力になる。