# 0076 — `nonempty_signedFiveAdicPacket_of_normalForm`

## Lean の型

```lean
private theorem nonempty_signedFiveAdicPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    Nonempty (SignedFiveAdicPacket u v w) := by
  ...
```

この定理は `SignedBranchANormalForm u v w` が与えられれば、前号で定義した `SignedFiveAdicPacket u v w` の inhabitant が少なくとも一つ存在することを示す。定理自体は `private` であり、直後の canonical choice を構成する内部実装として使われる。

## 数学的主張

`SignedBranchANormalForm` は、指数 5 の反例候補を符号付き Branch A の二つの orientation に正規化する。各 orientation について、適切な `carrier`, `residual`, `distinguished` を選べば

$$
carrier\cdot residual=distinguished^5,
$$

かつ

$$
5\mid carrier,\qquad 5\mid distinguished,
$$

$$
residual\equiv5\pmod{25},
$$

$$
v_5(residual)=1,
$$

$$
v_5(carrier)=4+5m
$$

を同時に満たす packet が存在する、という主張である。

orientation ごとの具体化は次の通り。

- difference orientation:
  `carrier = w - v`, `residual = GN5 (w - v) v`, `distinguished = u`。
- sum orientation:
  `carrier = u + v`, `residual = SumGN5 u v`, `distinguished = w`。

したがってこの定理は、異なる二つの因数分解を同じ five-adic interface へ合流させる「packet constructor」である。

## 証明全体での役割

0075 `SignedFiveAdicPacket` は共通仕様を宣言しただけで、まだ値を持っていなかった。本定理は `SignedBranchANormalForm` を case split し、difference / sum の両枝でその仕様をすべて埋める。

直後の

```lean
noncomputable def signedFiveAdicPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedFiveAdicPacket u v w :=
  Classical.choice (nonempty_signedFiveAdicPacket_of_normalForm hNF)
```

が `Classical.choice` で canonical packet を取り出すため、本定理は「存在証明」と「選択可能な実データ」の境界に位置する。

## 直接依存する定義・補題

主要な直接依存は次の通り。

- `SignedBranchANormalForm`
- `SignedFiveAdicPacket`
- `SignedFiveAdicSource`
- `right_lt_of_fermat5Equation`
- `gap_pos_of_fermat5Equation`
- `Body5`
- `body5_eq_fifth_power_of_fermat`
- `GN5`
- `GN5_cast_mod25_eq_five`
- `SumGN5`
- `add_mul_sumGN5_eq_add_pow_five`
- `SumGN5_cast_mod25_eq_five`
- `mod_twentyFive_eq_five_of_zmod_eq_five`
- `eq_five_add_twentyFive_mul_of_mod_eq_five`
- `five_dvd_of_eq_five_add_twentyFive_mul`
- `not_twentyFive_dvd_of_mod_eq_five`
- `padicValNat_five_eq_one_of_dvd_not_sq`
- `sumGN5_pos`
- `padicValNat_carrier_shape_of_mul_eq_fifth`

difference branch ではさらに `CounterexamplePack.hxy` を用い、`5 ∣ u` と仮に `5 ∣ v` が同時に成り立てば coprime 性に反することから `¬ 5 ∣ v` を得ている。

## 証明の流れ

### difference orientation

`hNF` を `⟨hPack, hOrientation⟩` に分解し、`differenceGap h5u h5gap` の場合を処理する。

まず Fermat 方程式から $v\le w$ と $0<w-v$ を得る。次に `hPack.hxy` と `h5u : 5 ∣ u` を使って `¬ 5 ∣ v` を示す。

`body5_eq_fifth_power_of_fermat` から

$$
(w-v)\,GN5(w-v,v)=u^5
$$

を得る。`GN5_cast_mod25_eq_five h5gap h5v` により residual は `ZMod 25` で 5 に等しく、これを 0068–0071 の bridge 群で

$$
GN5(w-v,v)\bmod25=5,
$$

$$
GN5(w-v,v)=5+25M,
$$

$$
5\mid GN5(w-v,v),\qquad25\nmid GN5(w-v,v)
$$

へ順に変換する。0072 から residual の付値は 1、0073 から carrier の付値は $4+5m$ の形になる。

最後に `SignedFiveAdicPacket` の全フィールドを record literal で埋め、`Nonempty` の witness として返す。

### sum orientation

`sumGap h5w h5sum` では

$$
carrier=u+v,
$$

$$
residual=SumGN5(u,v),
$$

$$
distinguished=w
$$

を選ぶ。

`add_mul_sumGN5_eq_add_pow_five` と Fermat 方程式から

$$
(u+v)\,SumGN5(u,v)=w^5
$$

を得る。`SumGN5_cast_mod25_eq_five hPack.hxy h5sum` から residual を法 25 で 5 に固定し、その後は difference branch と同じ bridge 群を通る。

正値性は `Nat.add_pos_left hPack.hx v` と `sumGN5_pos hPack.hx hPack.hy` で与えられる。最後は同じ `SignedFiveAdicPacket` へ格納する。

## Lean 固有の処理

この証明で目立つ Lean 固有処理は次の通り。

1. `rcases hNF with ⟨hPack, hOrientation⟩` と `cases hOrientation` により、structure と inductive provenance を明示的に分解する。
2. difference 側の自然数差 `w - v` を安全に扱うため、先に `v ≤ w` と正値性を用意する。
3. `simpa [Body5] using ...` で既存の fifth-power factorization を packet が要求する exact shape へ合わせる。
4. `ZMod 25` の等式を `% 25` の自然数等式へ戻し、さらに witness 付きの `5 + 25*M` へ変換する。0068–0071 がこの representation shift を局所化している。
5. `hcarrierPos.ne'`, `hresPos.ne'`, `hPack.hx.ne'` のように正値性から非零性を projection して 0073 へ渡す。
6. 最後の `exact ⟨{ ... }⟩` は `Nonempty` と structure construction を二重に包む。

## 冗長・重複箇所

最大の重複は difference / sum の後半である。`hmod` を得た後は、

```text
hmod
→ hshape
→ h5res
→ h25res
→ hresVal
→ hcarrierShape
→ packet fields
```

という流れがほぼ同型で繰り返される。

また `residual_shape`, `five_dvd_residual` 相当の情報、`residual_padicValNat` は互いに導出可能な情報を複数保存している。これは 0075 で見た proof cache 設計の帰結であり、後段の使いやすさと constructor の長さの交換条件になっている。

## 最適化候補

最も自然な候補は、共通後半を helper に切り出すことである。たとえば

```lean
private theorem mkSignedFiveAdicPacket
    ...
    (hfactor : carrier * residual = distinguished ^ 5)
    (hmod : residual % 25 = 5)
    ... :
    SignedFiveAdicPacket u v w := ...
```

のような constructor helper を用意すれば、orientation ごとの証明は「carrier/residual/distinguished と factorization と mod-25 情報を作る」部分に集中できる。

さらに `SignedFiveAdicPacket` を core facts と derived facts に二層化すれば、constructor 自体を短くし、派生情報を theorem として後から供給できる可能性がある。

ただしこの最適化は Lean ビルド未実施の設計案であり、現行 API の downstream 利用頻度を確認してから判断すべきである。

## 必要 Mathlib import と import 最適化候補

博物館ブランチで確認できる standalone artifact は `import Mathlib` を使用している。また manifest は本領域の元モジュールを `DkMath/FLT/Five/SignedFiveAdic.lean` と記録している。

一方、その分割元ファイルはこのブランチ上の同パスでは取得できなかったため、本定理単独の正確な最小 import は未確認である。

証明本体から見える外部要素は主に自然数算術、可除性、`ZMod`、`padicValNat`、`omega`、`norm_num` である。最適化するなら、まず `SignedFiveAdic.lean` の実 import を復元・確認し、`Mathlib` 全体 import との差分を計測するのが安全である。

## 既存 PDF との関係

リポジトリ内の Lean source を最終根拠とした。今回の確認では、この private helper に一対一対応する既存日本語・英語 PDF の具体的ページは特定できていない。そのため PDF 固有の説明やページ番号は推測で補っていない。

## Comparator challenge 化の可否

**適している。** 特に二種類の challenge が考えられる。

第一は proof refactoring challenge で、現行の二枝重複を保った版と、共通 constructor helper を抽出した版を比較する。評価軸は LOC、依存補題数、proof state の局所性、将来の field 追加への耐性である。

第二は API challenge で、fat packet と thin packet + derived lemmas のどちらが downstream の proof term を簡潔にするかを比較できる。

数学そのものより「同じ five-adic invariant を二つの orientation からどう共通 API に畳み込むか」が比較対象として面白い。

## 次に読むべき宣言

次は

```lean
noncomputable def signedFiveAdicPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedFiveAdicPacket u v w :=
  Classical.choice (nonempty_signedFiveAdicPacket_of_normalForm hNF)
```

である。

本号が `Nonempty (SignedFiveAdicPacket u v w)` を証明し、次号は `Classical.choice` によってその存在証明から実際の packet を一つ選ぶ。ここで「存在する five-adic packet」から「後段が直接参照できる canonical packet」へ API が切り替わる。