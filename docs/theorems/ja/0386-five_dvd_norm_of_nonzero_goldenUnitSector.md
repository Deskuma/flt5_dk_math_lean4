# 0386 `five_dvd_norm_of_nonzero_goldenUnitSector`

## 宣言種別

`theorem`

`GoldenZeroSectorDescentPacket` namespace の外に置かれた packet-independent な unit-sector 算術補題である。

## Lean コード

```lean
/--
A nonzero unit sector cannot have second coordinate divisible by five while
the fifth-power base has norm prime to five.  This is the packet-independent
form of the sector calculation used by the original zero-sector reduction.
-/
theorem five_dvd_norm_of_nonzero_goldenUnitSector
    {alpha gamma : GoldenInt} {i : Fin 5}
    (hi : i ≠ 0)
    (hAlpha : alpha =
      goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5))
    (hFive : (5 : ℤ) ∣ alpha.snd) :
    (5 : ℤ) ∣ goldenNorm gamma := by
  have hS := five_dvd_goldenFifthSndPoly gamma.fst gamma.snd
  apply five_dvd_goldenNorm_of_five_dvd_fifthFst
  fin_cases i
  · exact (hi rfl).elim
  · rw [hAlpha, golden_unit_one_mul_fifth_snd] at hFive
    have h := dvd_sub hFive hS
    ring_nf at h
    exact h
  · rw [hAlpha, golden_unit_two_mul_fifth_snd] at hFive
    have h := dvd_sub hFive (dvd_mul_of_dvd_right hS 2)
    ring_nf at h
    exact h
  · rw [hAlpha, golden_unit_three_mul_fifth_snd] at hFive
    have h2F : (5 : ℤ) ∣
        2 * goldenFifthFstPoly gamma.fst gamma.snd := by
      have h := dvd_sub hFive (dvd_mul_of_dvd_right hS 3)
      ring_nf at h ⊢
      exact h
    rcases (show Prime (5 : ℤ) by norm_num).dvd_mul.mp h2F with h52 | hF
    · norm_num at h52
    · exact hF
  · rw [hAlpha, golden_unit_four_mul_fifth_snd] at hFive
    have h3F : (5 : ℤ) ∣
        3 * goldenFifthFstPoly gamma.fst gamma.snd := by
      have h := dvd_sub hFive (dvd_mul_of_dvd_right hS 5)
      ring_nf at h ⊢
      exact h
    rcases (show Prime (5 : ℤ) by norm_num).dvd_mul.mp h3F with h53 | hF
    · norm_num at h53
    · exact hF
```

## Lean の型

概念的な完全型は

```lean
five_dvd_norm_of_nonzero_goldenUnitSector :
  {alpha gamma : GoldenInt} → {i : Fin 5} →
  i ≠ 0 →
  alpha = goldenMul (goldenPow goldenPhi i.val) (goldenPow gamma 5) →
  (5 : ℤ) ∣ alpha.snd →
  (5 : ℤ) ∣ goldenNorm gamma
```

である。

入力は黄金整数 `alpha`, `gamma` と unit-sector index `i : Fin 5` であり、仮定は次の三つである。

1. `hi : i ≠ 0`
2. `hAlpha : alpha = goldenPhi^i * gamma^5`
3. `hFive : 5 ∣ alpha.snd`

結論は

```lean
(5 : ℤ) ∣ goldenNorm gamma
```

である。

## 数学的主張

黄金整数を

$$
\alpha = \varphi^i\gamma^5,
\qquad i\in\{0,1,2,3,4\}
$$

という fifth-power unit sector に置く。

今回の theorem は、非零 sector

$$
i\neq0
$$

で第二座標が

$$
5\mid \alpha_{\mathrm{snd}}
$$

を満たすなら、第五冪部分の底 `gamma` の norm に必ず 5 が入ること、すなわち

$$
5\mid N(\gamma)
$$

を主張する。

証明の中心は、`gamma^5` の二つの座標多項式を

$$
F=\operatorname{goldenFifthFstPoly}(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}}),
$$

$$
S=\operatorname{goldenFifthSndPoly}(\gamma_{\mathrm{fst}},\gamma_{\mathrm{snd}})
$$

と見たとき、既知の

$$
5\mid S
$$

と各 unit sector における `alpha.snd` の座標公式を組み合わせ、非零 sector では必ず

$$
5\mid F
$$

を抽出できることにある。

最後に既存 bridge

$$
5\mid F \Longrightarrow 5\mid N(\gamma)
$$

を適用して結論する。

## 証明全体での役割

0385 `lift_relPrime_conj` までで、quadratic re-entry element とその共役が黄金整数環で相対素であることが確立した。そのため後続 `exists_lift_eq_fifthPower` では `goldenCoprimeFactorOfFifthPower` を用いて re-entry element を

$$
\alpha=\varepsilon\gamma^5
$$

と分解できる。

さらに `goldenUnitClassesModFifth` によって unit `epsilon` を fifth powers modulo の 5 sector に分類すると、別の fifth-power factor を吸収した後で

$$
\alpha=\varphi^i\theta^5,
\qquad i\in\operatorname{Fin}5
$$

という形になる。

zero-sector lift の第二座標は元の第二座標の平方なので、packet の

$$
s=\pm5t^5
$$

から

$$
5\mid \alpha_{\mathrm{snd}}
$$

が得られる。

ここで `i ≠ 0` なら今回の theorem により

$$
5\mid N(\theta)
$$

が強制される。一方 packet 側では quartic/norm が 5-adically clean であるため、後続証明はこれを矛盾として非零 sector をすべて排除する。したがって残るのは

$$
i=0,
$$

すなわち

$$
\alpha=\theta^5
$$

という honest fifth power sector だけである。

よって 0386 は、`unit × fifth power` までしか与えない一般 factorization を、zero-sector descent に必要な **純粋な fifth power** へ強化するための sector-exclusion kernel である。

## 直接依存する定義・補題

プロジェクト内でこの theorem が直接使う主な宣言は次である。

- `GoldenInt`
- `goldenMul`
- `goldenPow`
- `goldenPhi`
- `goldenNorm`
- `goldenFifthFstPoly`
- `goldenFifthSndPoly`
- `five_dvd_goldenFifthSndPoly`
- `five_dvd_goldenNorm_of_five_dvd_fifthFst`
- `golden_unit_one_mul_fifth_snd`
- `golden_unit_two_mul_fifth_snd`
- `golden_unit_three_mul_fifth_snd`
- `golden_unit_four_mul_fifth_snd`

Mathlib 側で証明本文から直接確認できる主な機能は次である。

- `Fin 5`
- `fin_cases`
- `dvd_sub`
- `dvd_mul_of_dvd_right`
- `Prime.dvd_mul`
- `ring_nf`
- `norm_num`

## 証明・構築の流れ

1. `gamma^5` の第二座標多項式について、常に

   ```lean
   hS : (5 : ℤ) ∣ goldenFifthSndPoly gamma.fst gamma.snd
   ```

   を得る。

   ```lean
   have hS := five_dvd_goldenFifthSndPoly gamma.fst gamma.snd
   ```

2. 最終目標 `5 ∣ goldenNorm gamma` を、第一座標 fifth-power polynomial の可除性へ還元する。

   ```lean
   apply five_dvd_goldenNorm_of_five_dvd_fifthFst
   ```

   以降の目標は概念的に

   $$
   5\mid F
   $$

   である。

3. `i : Fin 5` を `fin_cases i` で 0,1,2,3,4 の五つに完全分解する。

4. `i=0` は仮定 `hi : i ≠ 0` と即座に矛盾する。

   ```lean
   exact (hi rfl).elim
   ```

5. `i=1` では `golden_unit_one_mul_fifth_snd` で `alpha.snd` を座標多項式へ展開する。`hFive` から `hS` を引き、`ring_nf` で整理すると直接 `5 ∣ F` が残る。

6. `i=2` でも同様だが、第二座標公式に現れる `S` の係数に合わせて `2*S` の可除性を作り、差を取る。

   ```lean
   dvd_sub hFive (dvd_mul_of_dvd_right hS 2)
   ```

7. `i=3` では差から

   $$
   5\mid 2F
   $$

   を得る。5 は素数なので

   $$
   5\mid2 \quad\text{または}\quad 5\mid F.
   $$

   前者を `norm_num` で排除し、後者だけを残す。

8. `i=4` も同様に

   $$
   5\mid3F
   $$

   を得て、`5 ∤ 3` を使って `5 ∣ F` を得る。

9. すべての非零 sector で `5 ∣ F` が得られたので、冒頭の `apply five_dvd_goldenNorm_of_five_dvd_fifthFst` により

   $$
   5\mid N(\gamma)
   $$

   が確定する。

## Lean 固有の処理

### `Fin 5` と `fin_cases`

sector index を自然数と範囲条件の組として手作業で扱わず、有限型 `Fin 5` として保持している。そのため

```lean
fin_cases i
```

だけで五つのケースが exhaustive に生成される。

これは数学的な「modulo fifth powers で unit class は 5 sector」という有限分類を Lean の有限型へ直接写した形である。

### `rw [...] at hFive`

各 sector の座標公式は目標側ではなく仮定

```lean
hFive : (5 : ℤ) ∣ alpha.snd
```

の内部にある `alpha.snd` を具体化するために使われる。

```lean
rw [hAlpha, golden_unit_three_mul_fifth_snd] at hFive
```

のように、factorization と sector-specific coordinate theorem を連続して仮定へ rewrite している。

### 可除性の線形結合

`dvd_sub` と `dvd_mul_of_dvd_right` を使って、5 で割れる二つの式の差も 5 で割れるという初等整数算術を明示する。

例えば `i=2` では

```lean
have h := dvd_sub hFive (dvd_mul_of_dvd_right hS 2)
```

とし、不要な `S` 成分を消去する。

### `ring_nf at h ⊢`

sector 座標公式から得られる差は syntactic には欲しい `F` または `2*F`, `3*F` と一致しない。そのため `ring_nf` で整数多項式を正規化する。

### `Prime.dvd_mul`

`i=3,4` では係数付き `F` しか得られないため、

```lean
(show Prime (5 : ℤ) by norm_num).dvd_mul.mp h2F
```

の形で Euclid's lemma を使う。係数 2 または 3 が 5 で割れないことを `norm_num` で閉じることで `5 ∣ F` を選び出している。

## 冗長・重複箇所

4つの非零 sector は同じ構造を持つ。

- `hAlpha` と sector-specific snd formula を `hFive` に rewrite
- `hS` の適切な整数倍を引く
- `ring_nf`
- 必要なら小係数との積から `5 ∣ F` を抽出

したがって tactic レベルではかなり反復している。

ただし、この反復は `Fin 5` の各 sector で実際に何が起きるかを監査しやすくする利点もある。特に 3,4 sector では `2*F`, `3*F` から prime cancellation が必要であり、1,2 sector と完全には同形でない。

このため現状の明示的 case split は、証明 museum の観点では有用な冗長性である。

## 最適化候補

1. **sector coefficient table の抽象化**

   4本の `golden_unit_*_mul_fifth_snd` を、`i : Fin 5` に対して係数を返す一つの一般公式へまとめられるなら、`fin_cases` 後の反復を縮められる。

   ただし一般公式の導入コストがこの単一 theorem より大きくなる可能性があり、現時点では必ずしも改善とは限らない。

2. **5 と小係数の cancellation helper**

   `5 ∣ 2*F` / `5 ∣ 3*F` から `5 ∣ F` を得る処理は共通化可能である。例えば `Nat/Int.Coprime` を使った cancellation lemma に寄せれば、`Prime.dvd_mul` の枝分岐を隠せる。

3. **第一座標 divisibility までを別 lemma 化**

   今回の本質を

   ```lean
   nonzero_sector_five_dvd_fifthFst
   ```

   のような lemma として切り出し、norm bridge を別段にする設計も可能である。後続で `5 ∣ F` 自体を再利用するなら価値があるが、現在確認できる主要用途は norm divisibility なので現 theorem の直結形が簡潔である。

4. **case proof の自動化**

   `fin_cases i <;> simp_all [...]` に近い圧縮は理論上可能性がある。ただし `Prime.dvd_mul` を要する 3,4 sector があるため、単純な一括 `simp` だけで同じ可読性を保てるかは未確認である。

## 必要 Mathlib import と import 最適化候補

現在の stand-alone 正本は冒頭で

```lean
import Mathlib
```

を使用しており、この theorem もその環境で記述されている。

この theorem 自身から直接見える Mathlib 依存は、主に有限場合分け `fin_cases`、整数可除性、prime divisibility、`ring_nf`、`norm_num` である。

より細い import 候補としては、少なくとも以下の機能を提供するモジュール群へ分解できる可能性がある。

- `Fin` の有限場合分けを提供する tactic
- `ring_nf`
- `norm_num`
- 整数の prime/divisibility API

ただし、このリポジトリの stand-alone artifact は前段の全プロジェクト定義も同一ファイルへ結合しているため、この theorem 単体の **厳密な最小 Mathlib import 集合** はソース閲覧だけでは確定できない。Lean build を行わない条件のため、import 縮小案は未検証候補として扱う。

実務上は、museum 解説の対象コードをそのまま再現するなら `import Mathlib` が確認済みの必要十分な入口である。

## Comparator challenge 化の可否

**可。しかも比較的良い challenge 候補である。**

理由は、statement が局所的で、有限 sector classification と elementary divisibility に証明負荷が集中しているからである。

challenge 化する場合は次の二段階が考えられる。

### 軽量版

依存 theorem

- `five_dvd_goldenFifthSndPoly`
- `five_dvd_goldenNorm_of_five_dvd_fifthFst`
- 4本の `golden_unit_*_mul_fifth_snd`

を既知 lemma として与え、今回の theorem 本体だけを穴にする。

これは `Fin 5` case split、divisibility linear combination、prime cancellation、ring normalization を適切に選べるかを測る challenge になる。

### 強化版

4本の sector-specific coordinate formula のうち一部も challenge 側へ含める。すると単なる API 選択だけでなく、黄金整数の multiplication/power coordinate arithmetic まで含むため難度が大きく上がる。

Comparator で「数学的枝切り能力」を見るなら軽量版が適している。ケースは有限だが、sector ごとに cancellation の形が微妙に違い、単純 brute-force tactic だけではなく構造を読む必要がある。

## 次に読むべき宣言

次は `GoldenZeroSectorDescentPacket` namespace に戻り、

```lean
/-- The re-entry element is an honest fifth power; all nonzero unit sectors die mod five. -/
theorem exists_lift_eq_fifthPower (p : GoldenZeroSectorDescentPacket) :
    ∃ gamma : GoldenInt,
      goldenZeroSectorLift p.base = goldenPow gamma 5 ∧
      goldenNorm gamma = (p.D : ℤ) := by
  ...
```

を読むべきである。

宣言種別は `theorem`。

0385 で得た relative-prime factorization と、今回 0386 の nonzero-sector obstruction を初めて一つに束ね、

$$
\operatorname{goldenZeroSectorLift}(p.base)=\gamma^5
$$

という honest fifth-power re-entry を構成する theorem である。

さらに norm まで

$$
N(\gamma)=D
$$

と固定するため、ここから新しい descent packet の座標構成へ進む。
