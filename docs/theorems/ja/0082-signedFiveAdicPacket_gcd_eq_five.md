# 0082 — `signedFiveAdicPacket_gcd_eq_five`

## Lean の型

```lean
theorem signedFiveAdicPacket_gcd_eq_five
    {u v w : ℕ} (p : SignedFiveAdicPacket u v w) :
    Nat.gcd p.carrier p.residual = 5 := by
  apply Nat.dvd_antisymm
  · cases p.source with
    | difference hcarrier hresidual _ =>
        rw [hcarrier, hresidual]
        have hgapV : Nat.Coprime (w - v) v :=
          coprime_gap_y_of_counterexamplePack p.normal.pack
        have hDcopV : Nat.Coprime (Nat.gcd (w - v) (GN5 (w - v) v)) v :=
          Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left _ _) hgapV
        have hDcopV4 := Nat.Coprime.pow_right 4 hDcopV
        apply hDcopV4.dvd_of_dvd_mul_right
        exact dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5
          (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    | sum hcarrier hresidual _ =>
        rw [hcarrier, hresidual]
        have hsumU : Nat.Coprime (u + v) u :=
          Nat.coprime_self_add_left.mpr p.normal.pack.hxy.symm
        have hDcopU : Nat.Coprime (Nat.gcd (u + v) (SumGN5 u v)) u :=
          Nat.Coprime.of_dvd_left (Nat.gcd_dvd_left _ _) hsumU
        have hDcopU4 := Nat.Coprime.pow_right 4 hDcopU
        apply hDcopU4.dvd_of_dvd_mul_right
        exact dvd_five_mul_left_pow_four_of_dvd_sum_of_dvd_sumGN5
          (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
  · have h5res : 5 ∣ p.residual := by
      rcases p.residual_shape with ⟨M, hM⟩
      use 1 + 5 * M
      omega
    exact Nat.dvd_gcd p.five_dvd_carrier h5res
```

## 数学的主張

任意の `SignedFiveAdicPacket u v w` について、その carrier と residual の最大公約数は正確に $5$ である。

$$
\gcd(p.carrier,p.residual)=5.
$$

証明は二つの可除性

$$
\gcd(p.carrier,p.residual)\mid5,
\qquad
5\mid\gcd(p.carrier,p.residual)
$$

を別々に示し、`Nat.dvd_antisymm` で等号にする。

## 証明全体での役割

0081 までで sum orientation にも difference orientation と同型の gcd-control 補題が揃った。本定理はそれらを `SignedFiveAdicSource` による provenance 分岐の下で統合し、packet の二因子が共有する five-adic 因子がちょうど一個であることを確定する。

後続の `SignedFiveAdicPowerSplit` 構築では carrier と residual をそれぞれ $5$ で割り、得られた商が互いに素であることを示す。その入口が本定理である。

## 直接依存する定義・補題

- `SignedFiveAdicPacket`
- `SignedFiveAdicSource`
- `coprime_gap_y_of_counterexamplePack`
- `dvd_five_mul_y_pow_four_of_dvd_gap_of_dvd_GN5`
- `dvd_five_mul_left_pow_four_of_dvd_sum_of_dvd_sumGN5`
- `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right`, `Nat.dvd_gcd`
- `Nat.Coprime.of_dvd_left`, `Nat.Coprime.pow_right`, `Nat.Coprime.dvd_of_dvd_mul_right`
- `Nat.coprime_self_add_left`
- `Nat.dvd_antisymm`

さらに packet field `p.normal.pack.hxy`, `p.five_dvd_carrier`, `p.residual_shape` を直接消費する。

## 証明の流れ

1. `Nat.dvd_antisymm` で目標を二方向の divisibility に分解する。
2. 上界 `gcd ∣ 5` では `p.source` を difference / sum に分岐する。
3. difference 側では carrier/residual を `w-v` と `GN5 (w-v) v` に書き戻す。
4. primitive counterexample から `Coprime (w-v) v` を得る。よって gcd も $v$、さらに $v^4$ と互いに素である。
5. 既存補題に gcd 自身を $q$ として渡すと、gcd は $5v^4$ を割る。$v^4$ との coprimality でそれを除去し、gcd が $5$ を割る。
6. sum 側では同様に `Coprime (u+v) u` を作り、0081 に gcd を渡して gcd が $5u^4$ を割ることを得る。$u^4$ を coprimality で除去して gcd が $5$ を割る。
7. 下界 `5 ∣ gcd` では `p.residual_shape : ∃ M, residual = 5 + 25*M` から `5 ∣ residual` を再構成する。
8. `p.five_dvd_carrier` と合わせて `Nat.dvd_gcd` を適用し、`5 ∣ gcd` を得る。
9. 二方向を `Nat.dvd_antisymm` で結び、gcd を正確に $5$ に固定する。

## Lean 固有の処理

`cases p.source` によって provenance を展開すると、各 constructor が持つ等式 `hcarrier`, `hresidual` を `rw` で使え、抽象 packet field が具体的な `GN5` / `SumGN5` へ戻る。

`Nat.Coprime.of_dvd_left` は gcd が carrier を割る事実を利用して、carrier と基底の coprimality を gcd と基底の coprimality へ降ろす。さらに `pow_right 4` で第四冪へ持ち上げる。

その後の `dvd_of_dvd_mul_right` が proof script の重要点である。gcd が $5x^4$ を割り、しかも gcd と $x^4$ が互いに素なら、gcd は $5$ を割る。

下界側では `residual_shape` から `5 ∣ residual` を `use 1 + 5 * M; omega` で再構成している。packet にはすでに `residual_padicValNat = 1` もあるが、ここではより直接的な shape field を利用している。

## 冗長・重複箇所

difference と sum の二 branch は高い対称性を持つ。異なるのは carrier/residual の具体形、基底側の coprimality の取り方、最後に呼ぶ gcd-control 補題だけである。

また `SignedFiveAdicPacket` には residual の mod 25、shape、valuation が重複して保存されている。本証明は `residual_shape` から `5 ∣ residual` を再構成しており、もし packet に `five_dvd_residual` を field として保持すれば下界側は一行短くなる。ただし record の冗長性は増える。

## 最適化候補

第一候補は difference/sum 共通の gcd-upper-bound helper を切り出すことじゃ。抽象的には

$$
D\mid5x^4,\quad \gcd(D,x)=1
\Longrightarrow D\mid5
$$

という部分は完全に共通化できる。

第二候補は `residual_shape` ではなく既存の five-adic field から `5 ∣ residual` を供給する projection theorem を用意すること。packet 内部の representation choice を後段から隠せる。

第三候補は source branch ごとの carrier/residual/coprimality/gcd-control を一つの orientation interface にまとめること。ただし abstraction cost が proof length の削減を上回る可能性があり、現時点では設計候補に留める。

## 必要 Mathlib import と import 最適化候補

対象ブランチの生成 standalone は `import Mathlib` を使用している。本定理が直接使う Mathlib 機能は `Nat.gcd`、`Nat.Coprime`、divisibility、`omega` である。

概念的には自然数 gcd/coprime と tactic `omega` 周辺に縮小できる可能性が高い。ただし分割元 `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` の正確な import graph は対象ブランチ上で個別確認できていないため、最小 import 集合は未検証である。

## 既存 PDF との関係

数学的には「二因子の共通因子は five-adic exceptional factor 5 のみで、しかも 5 は実際に両方へ入る」ことを確定する箇所に対応する。Lean の型と proof script の一次根拠はリポジトリ内の standalone source である。

既存日英 PDF で本 theorem と一対一対応する定理番号・ページは今回確定できなかったため、PDF 固有の番号や引用は推測で補っていない。

## Comparator challenge 化の可否

非常に適している。比較候補は次の通り。

- 現行の source case split + gcd-control 補題二本
- 共通 gcd-upper-bound helper を導入した証明
- valuation だけで `gcd = 5` を導く証明
- packet API を強化し `five_dvd_residual` を projection として供給する証明

評価軸は proof length だけでなく、difference/sum の対称性、packet 内部表現への依存度、後続 power split からの再利用性、エラー局所性である。

## 次に読むべき宣言

次は直後の

```lean
structure SignedFiveAdicPowerSplit
    (u v w : ℕ) : Type where
  fiveAdic : SignedFiveAdicPacket u v w
  a : ℕ
  b : ℕ
  ...
```

を読むべきである。本定理で得た

$$
\gcd(p.carrier,p.residual)=5
$$

を使い、carrier と residual から共通因子 $5$ を剥がした後の互いに素な因子と第五冪構造を一つの record にまとめる次段階へ進む。