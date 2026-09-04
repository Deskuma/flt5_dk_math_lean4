# 0080 — `branchB_false_of_fiveAdicCore`

## Lean の型

```lean
theorem branchB_false_of_fiveAdicCore
    (hCore : SignedFiveAdicCore)
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    False := by
  exact branchB_false_of_signedBranchARefuter
    (signedBranchARefuter_of_fiveAdicCore hCore) hPack hBranch
```

## 数学的主張

`CounterexamplePack x y z` と Branch B 条件 $5\nmid(z-y)$ のもとで、任意の exact five-adic packet を矛盾へ送る `SignedFiveAdicCore` があれば `False` が従う。

概念的には

$$
\mathrm{SignedFiveAdicCore}
\Longrightarrow\mathrm{SignedBranchARefuter}
\Longrightarrow\mathrm{BranchB\ candidate}
\Longrightarrow\bot.
$$

本定理は新しい合同式や付値計算を行わず、既存の five-adic core 層を Branch B closure へ接続する。

## 証明全体での役割

0075–0079 では signed normal form から common `SignedFiveAdicPacket` を構成し、その packet-level contradiction を `SignedBranchARefuter` へ昇格させた。本定理は 0058 `branchB_false_of_signedBranchARefuter` にその refuter を渡し、元の Branch B 反例候補を閉じる。

従って `DkMath/FLT/Five/SignedFiveAdic.lean` の closure theorem であり、five-adic 局所不変量の層を FLT5 の Branch-B contradiction へ戻す接続点である。

## 直接依存する定義・補題

- `SignedFiveAdicCore`
- `signedBranchARefuter_of_fiveAdicCore`
- `branchB_false_of_signedBranchARefuter`
- `CounterexamplePack`

`GN5`、`SumGN5`、`padicValNat`、`ZMod 25` は本定理から直接参照されない。これらは packet/core API の背後へ隠蔽されている。

## 証明の流れ

1. `hCore : SignedFiveAdicCore` を受け取る。
2. `signedBranchARefuter_of_fiveAdicCore hCore` で `SignedBranchARefuter` を得る。
3. その refuter と `hPack`, `hBranch` を `branchB_false_of_signedBranchARefuter` に渡す。
4. `False` が返る。

証明は既証明の二つの adapter の関数合成である。

## Lean 固有の処理

`{x y z : ℕ}` は implicit で、`hPack` から推論される。内側の theorem の戻り型 `SignedBranchARefuter` と外側 theorem の第一引数型が一致するため、一つの `exact` で終わる。途中の `have`、rewrite、cast、算術 tactic は不要であり、既存 API 境界が型レベルで正しく接続されていることが見える。

## 冗長・重複箇所

proof script 自体にほぼ冗長性はない。0079 をインライン化することは可能だが、そうすると packet-to-normal-form adapter の責務が Branch B theorem に漏れる。また 0058 と統合すると `SignedBranchARefuter` を別実装から供給する再利用経路を失う。現行 wrapper は architectural seam と見るのが自然である。

## 最適化候補

第一候補は変更しないことである。既に一行で役割も明確である。同型 closure theorem が増えた場合のみ generic composition helper を検討できる。0076–0077 の classical selection を constructive constructor に変えられれば、本定理の表面形を保ったまま間接的な `Classical.choice` 依存を減らせる可能性があるが、これは未検証の設計案である。

## 必要 Mathlib import と import 最適化候補

対象の生成 standalone `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用する。manifest コメントではこの定理は `DkMath/FLT/Five/SignedFiveAdic.lean` 部分に属する。本定理自身は Mathlib の個別数論 API を直接使わず、必要なのは主として上記ローカル宣言である。

従って分割モジュールではより小さい import で足りる可能性が高いが、博物館ブランチ上で分割元の正確な import graph を今回再検証していないため、最小 import は未確認である。

## 既存 PDF との関係

具体的な型と proof term の一次根拠は対象ブランチの Lean source である。既存の日英 PDF にこの短い architecture-level closure theorem と一対一対応するページは今回特定できなかったため、PDF 固有のページ番号や説明は推測で補っていない。

## Comparator challenge 化の可否

適している。ただし数論探索より proof architecture 比較向きである。現行の named two-stage adapter、0079 のインライン化、generic refuter composition、constructive packet constructor 化を比較できる。評価軸は短さ、依存境界、再利用性、error message、classical choice への間接依存である。

## 次に読むべき定理

Lean source 上では本定理で `SignedFiveAdic.lean` 部分が終わり、次に `SignedFiveAdicPowerSplit.lean` へ入る。次の宣言は

```lean
private theorem dvd_five_mul_left_pow_four_of_dvd_sum_of_dvd_sumGN5
    {u v q : ℕ} (hqsum : q ∣ u + v) (hqres : q ∣ SumGN5 u v) :
    q ∣ 5 * u ^ 4 := by
  ...
```

である。sum orientation で `q` が `u+v` と `SumGN5 u v` の双方を割るなら `5*u^4` も割ることを `ZMod q` 上で示し、後続の `signedFiveAdicPacket_gcd_eq_five` へつなぐ補題である。