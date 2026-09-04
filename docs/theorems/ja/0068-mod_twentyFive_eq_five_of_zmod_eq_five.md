# 0068 — `mod_twentyFive_eq_five_of_zmod_eq_five`

## Lean の型

```lean
private theorem mod_twentyFive_eq_five_of_zmod_eq_five
    {n : ℕ} (h : (n : ZMod 25) = 5) :
    n % 25 = 5 := by
  have hmod : n ≡ 5 [MOD 25] :=
    (ZMod.natCast_eq_natCast_iff n 5 25).mp (by simpa using h)
  simpa [Nat.ModEq] using hmod
```

この宣言は `private` であり、`SignedFiveAdic.lean` 内部で `ZMod 25` 上の等式を自然数の `% 25` 等式へ戻す変換補題である。

## 数学的主張

自然数 `n` を `ZMod 25` へ写した値が 5 なら、

$$
(n:\mathrm{ZMod}\ 25)=5
$$

から

$$
n\bmod25=5
$$

が従う。

数学的には同じ合同情報を二つの表現で書き換えているだけである。`ZMod 25` の等式は

$$
n\equiv5\pmod{25}
$$

を意味し、`5<25` なので右辺の標準剰余はそのまま 5 である。

## 証明全体での役割

0066 と 0067 は difference / sum の各 residual について

$$
(residual:\mathrm{ZMod}\ 25)=5
$$

を与える。しかし後段で必要なのは自然数の可除性・非可除性を取り出しやすい

$$
residual\bmod25=5
$$

という形である。本補題はこの表現層の境界を一箇所にまとめる。

後段 `nonempty_signedFiveAdicPacket_of_normalForm` では、difference branch で

```lean
have hmod : GN5 (w - v) v % 25 = 5 :=
  mod_twentyFive_eq_five_of_zmod_eq_five hcast
```

sum branch で

```lean
have hmod : SumGN5 u v % 25 = 5 :=
  mod_twentyFive_eq_five_of_zmod_eq_five hcast
```

として共通利用される。その後、この `hmod` から `n=5+25M`、`5∣n`、`25∤n` を導き、5-adic valuation 1 へ進む。

依存の流れは

```text
(residual : ZMod 25) = 5
             ↓
ZMod.natCast_eq_natCast_iff
             ↓
      residual ≡ 5 [MOD 25]
             ↓
          Nat.ModEq
             ↓
      residual % 25 = 5
             ↓
       n = 5 + 25M
             ↓
        5 ∣ n, 25 ∤ n
```

である。

## 直接依存する定義・補題

- `ZMod.natCast_eq_natCast_iff`
- `Nat.ModEq`
- `simpa`

本補題は 0066・0067 の内容そのものには依存せず、任意の自然数 `n` に使える一般 bridge である。0066・0067 は主要 consumer 側から本補題へ値を供給する。

## 証明の流れ

1. 仮定 `h : (n : ZMod 25) = 5` を受け取る。
2. `ZMod.natCast_eq_natCast_iff n 5 25` の順方向を使い、`Nat.ModEq 25 n 5`、すなわち `n ≡ 5 [MOD 25]` を得る。
3. `Nat.ModEq` を展開すると `% 25` の等式になる。
4. `simpa [Nat.ModEq]` で結論 `n % 25 = 5` を得る。

## Lean 固有の処理

ここで扱っているのは数学の新しい算術ではなく、Lean における二つの合同表現の変換である。

`ZMod 25` は quotient ring としての環計算に適している。一方 `Nat.ModEq` や `%` は自然数の可除性 witness を構成する後段処理に適している。本補題は両者を明示的に分離するため、後続証明が `ZMod` API と `Nat` API を混在させずに済む。

`by simpa using h` は右辺の `5` を `ZMod 25` の自然数 cast として整える小さな elaboration step である。

## 冗長・重複箇所

証明は二行であり、実質的な重複はない。

ただし `ZMod.natCast_eq_natCast_iff` を経由して `Nat.ModEq` を作り、直後に `[Nat.ModEq]` を展開するため、中間命題 `hmod` は論理的には省略可能である。現行形は「ZMod 等式 → 合同式 → 剰余式」という変換の意味を可視化しており、解説性は高い。

## 最適化候補

第一候補は theorem を一つの `simpa [Nat.ModEq]` へ圧縮できるか検討することである。ただし API の向きと cast 正規化が読みにくくなるなら、現行の二段階の方が保守しやすい。

第二候補は、modulus と residue を一般化して

```lean
(n : ZMod m) = r → n % m = r % m
```

型の共通 bridge を利用・作成することである。既存 Mathlib API に同等補題があるなら、本定理はその特殊化に置き換えられる可能性がある。

第三候補は後続が `Nat.ModEq` のまま処理できる場合、`% 25 = 5` へ展開せず合同式を共通インターフェースにする設計である。ただし現在の後続補題は `%` 等式を直接受け取るため、局所変更では済まない。

## 必要 Mathlib import と import 最適化候補

生成済み `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用している。本補題自身が必要とする主要 API は `ZMod` と自然数合同 `Nat.ModEq` であり、tactic 依存はほぼ `simpa` のみである。

したがって import 最適化の余地は比較的大きく、`ZMod` と Nat の modular arithmetic を提供する最小モジュールへ縮小できる可能性が高い。ただし対象ブランチ上で分割元 `SignedFiveAdic.lean` の正確な import 行を直接取得できていないため、具体的な最小 import 名は未確認であり推測である。

本回では Lean ビルドを行っていないため、import 縮小の可否は検証していない。

## Comparator challenge 化の可否

適しているが、challenge としては小粒である。数学的難度ではなく API 選択の比較に向く。

- 現行: `ZMod.natCast_eq_natCast_iff` → `Nat.ModEq` 展開
- 候補 A: より直接的な `ZMod` / `%` bridge API
- 候補 B: modulus/residue を一般化した helper
- 候補 C: 後段を `Nat.ModEq` のまま設計して `%` 展開自体を避ける

比較軸は行数より、API の明瞭さ、cast の安定性、Mathlib バージョン変更への耐性、一般化可能性である。

## 根拠と推測

定理名・型・完全な証明本体は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` で確認した。同ソースで difference / sum の双方の branch が本補題を直接使用していることも確認した。

GitHub コード検索は本回一時的に upstream error となったため、既知の standalone ソースを直接取得して確認した。既存の日英 PDF における具体的対応ページは確認できておらず、PDF 固有のページ番号・説明は推測で補っていない。

## 次に読むべき定理

```lean
private theorem eq_five_add_twentyFive_mul_of_mod_eq_five
    {n : ℕ} (hmod : n % 25 = 5) :
    ∃ M : ℕ, n = 5 + 25 * M
```

0068 で得た剰余式を、可除 witness を直接操作できる明示的な算術形 `n=5+25M` へ変換する次の bridge である。
