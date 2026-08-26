# 0171 — `goldenConj_mul`

## Lean の型

```lean
/-- Conjugation respects multiplication. -/
theorem goldenConj_mul (x y : GoldenInt) :
    goldenConj (goldenMul x y) =
      goldenMul (goldenConj x) (goldenConj y) := by
  ext <;> simp [goldenConj, goldenMul] <;> ring
```

これは `theorem` であり、黄金整数の共役 `goldenConj` が乗法 `goldenMul` を保存することを示す。

## 数学的主張または宣言の意味

`GoldenInt` の元を

$$
x=a+b\varphi,\qquad y=c+d\varphi
$$

と読む。上流では

$$
\varphi^2=\varphi+1
$$

を使った座標乗法が

$$
(a,b)(c,d)=(ac+bd,\ ad+bc+bd)
$$

として `goldenMul` に実装され、共役は

$$
(a,b)\mapsto(a+b,-b)
$$

すなわち $\varphi\mapsto1-\varphi$ として `goldenConj` に実装されている。

本 theorem の主張は

$$
\overline{xy}=\overline{x}\,\overline{y}
$$

である。これは二次環の共役が単なる集合上の involution ではなく、乗法構造と両立することを意味する。

座標で確認すると、$xy=(A,B)$ とおけば

$$
A=ac+bd,\qquad B=ad+bc+bd.
$$

したがって左辺の第一座標は

$$
A+B=ac+ad+bc+2bd,
$$

第二座標は

$$
-B=-ad-bc-bd.
$$

一方、

$$
\overline{x}=(a+b,-b),\qquad \overline{y}=(c+d,-d)
$$

を `goldenMul` すると、同じ二座標

$$
(ac+ad+bc+2bd,\ -ad-bc-bd)
$$

が得られる。

## 証明全体での役割

0170 `goldenConj_invol` は

$$
\overline{\overline{x}}=x
$$

を証明し、共役が自己逆であることを確立した。本 theorem はその直後に

$$
\overline{xy}=\overline{x}\,\overline{y}
$$

を確立する。

この二つを合わせると、`goldenConj` は二次環の乗法的な自己対称としてかなり明瞭になる。後続では `goldenNorm_mul`、`goldenNorm_conj`、`golden_mul_conj` によってノルムとの関係が展開される。

さらに、後の `GoldenDivisibility` generated section では

```lean
theorem goldenConj_pow (x : GoldenInt) (n : ℕ) :
    goldenConj (x ^ n) = goldenConj x ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ]
      change goldenConj (goldenMul (x ^ n) x) = _
      rw [goldenConj_mul, ih]
      rw [pow_succ, ← golden_mul_eq]
```

と、本 theorem が直接 rewrite に使われる。したがって 0171 は単なる構造説明ではなく、第五冪を含む後続の共役計算を支える実用的な乗法 API でもある。

## 直接依存する定義・補題

直接依存は次である。

- `GoldenInt`
- `goldenMul`
- 0163 `goldenConj`
- `GoldenInt.ext`
- `GoldenInt` の `fst` / `snd` 座標
- 整数環上の `simp` と `ring` tactic infrastructure

0170 `goldenConj_invol` は数学的には直前の重要性質だが、本 theorem の Lean proof はそれを使用しない。両辺を直接座標展開して証明している。

概念的な依存は

$$
\texttt{goldenMul},\ \texttt{goldenConj},\ \texttt{GoldenInt.ext}
\longrightarrow
\texttt{goldenConj_mul}
$$

である。

## 証明または構築の流れ

証明は一行である。

```lean
by
  ext <;> simp [goldenConj, goldenMul] <;> ring
```

処理は次の三段階に分けられる。

1. `ext` で `GoldenInt` の等式を第一・第二座標の整数等式へ分解する。
2. `simp [goldenConj, goldenMul]` で共役と乗法を座標式へ展開する。
3. 残った可換環上の多項式恒等式を `ring` で正規化して閉じる。

つまり proof flow は

```text
goldenConj (goldenMul x y)
  = goldenMul (goldenConj x) (goldenConj y)
→ GoldenInt.ext で fst / snd に分解
→ goldenConj / goldenMul を展開
→ ℤ 上の多項式等式
→ ring 正規化
```

である。

## Lean 固有の処理

`ext` は `[ext] theorem GoldenInt.ext` を利用して structure equality を座標 equality へ落とす。これにより `cases x`、`cases y` を手動で行う必要がない。

`<;>` は直前の tactic が生成したすべての goal に後続 tactic を適用する。本 proof では第一・第二座標の両方に同じ

```lean
simp [goldenConj, goldenMul]
```

と `ring` を適用する。

`simp` の役割は定義展開と軽い整数式の正規化であり、非自明な多項式展開そのものは `ring` が担当する。ここで `nlinarith` ではなく `ring` が適切なのは、不等式や仮定を使わず、純粋な可換環恒等式を証明しているためである。

また theorem の statement は標準 `*` ではなく raw API の `goldenMul` を使っている。0159 `golden_mul_eq` により標準記法へ接続できるが、本 theorem は coordinate layer の構造保存則として raw API 上に置かれている。

## 冗長・重複箇所

証明内部では `goldenConj` と `goldenMul` を双方とも完全展開するため、数学的には「共役が環準同型である」という抽象法則を毎回座標計算で確認する設計である。

後続の `GoldenDivisibility` section にはさらに

- `goldenConj_add`
- `goldenConj_neg`
- `goldenConj_sub`
- `goldenConj_pow`

が置かれている。このため、共役の構造保存則が複数 theorem として分散している。

これは明示座標 API としては読みやすい一方、抽象 algebra API の観点では、加法保存・乗法保存・`1` の保存などを一つの `RingHom`、さらに 0170 の involution 性まで含めて `RingEquiv` に bundle できる余地がある。

ただし現行順序では `goldenConj_add` が後続 module に置かれているため、0171 の時点で直ちに完全な ring equivalence を構成するには、宣言順または module 境界の再編が必要になる。

## 最適化候補

候補は次である。

1. 現行の `ext <;> simp [...] <;> ring` を維持する。
2. statement を標準記法 `goldenConj (x * y) = goldenConj x * goldenConj y` に寄せる。
3. raw 版と標準記法版の bridge theorem を併設する。
4. `goldenConj_add` を同じ module へ移し、`goldenConj` を `GoldenInt →+* GoldenInt` として bundle する。
5. 0170 の involution 性を使って最終的に `GoldenInt ≃+* GoldenInt` を構成する。
6. 一般二次環の共役写像を抽象化し、黄金整数をその特殊化として扱う。

現行 proof 自体は既に非常に短いため、局所的な tactic 短縮には大きな利益はない。より大きな改善候補は、共役の複数の保存則を標準 homomorphism API に統合し、後続の `goldenConj_pow` などを一般 theorem から得ることである。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本 theorem 単独で見ると、必要なのは上流の `GoldenInt`、`goldenMul`、`goldenConj`、`GoldenInt.ext` に加え、整数式を扱う simplifier と `ring` tactic である。

したがって `Mathlib` 全体は theorem 単独では過剰である可能性が高い。少なくとも tactic 側では `ring` を提供する import が必要になる。一方、`GoldenOrder` module 全体では `Zsqrtd`、`CommRing`、`omega`、`norm_num` なども使うため、実際の最小 import 集合は module 単位で検証すべきである。

今回は Lean build を行わないため、具体的な最小 import リストは確定せず、import 削減は最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。

比較候補は、

- 現行の raw coordinate proof
- 標準 `*` notation を使う statement
- `RingHom` として bundle した共役から `map_mul` を得る方式
- `RingEquiv` として bundle した共役から構造保存を得る方式
- 一般 quadratic-order conjugation の特殊化として得る方式

である。

比較軸は、

- proof-term の短さ
- definition 展開量
- `simp` normal form
- `goldenConj_pow` などの downstream theorem の簡潔さ
- module dependency の循環有無
- 一般二次環への再利用性
- explicit coordinate transparency

である。

特に「短い座標証明を多数保持する設計」と「最初に homomorphism structure を作り、一般 algebra theorem を再利用する設計」のどちらが FLT5 全体で保守しやすいかを測る、良い Comparator challenge になる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に含まれる `DkMath/FLT/Five/GoldenOrder.lean` generated section である。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在することを確認した。ただし、本 theorem に対応する具体的な PDF ページ・節番号は今回直接特定していないため推測しない。

## 次に読むべき宣言

Lean source 上で直後に置かれている宣言は

```lean
/-- The structure norm is the previously exposed binary golden norm. -/
theorem goldenNorm_eq_GoldenNorm (x : GoldenInt) :
    goldenNorm x = GoldenNorm x.fst x.snd := rfl
```

である。

したがって依存順の次は **0172 `goldenNorm_eq_GoldenNorm`** とする。0171 で共役の乗法保存を確立した後、次は `GoldenInt` structure 上の `goldenNorm` と、より前段で使われていた二変数二次形式 `GoldenNorm` を定義的に接続し、既存の黄金ノルム API と新しい structure API を橋渡しする。