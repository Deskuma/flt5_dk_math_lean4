# 0069 — `eq_five_add_twentyFive_mul_of_mod_eq_five`

## Lean の型

```lean
private theorem eq_five_add_twentyFive_mul_of_mod_eq_five
    {n : ℕ} (hmod : n % 25 = 5) :
    ∃ M : ℕ, n = 5 + 25 * M := by
  refine ⟨n / 25, ?_⟩
  have hsplit := Nat.mod_add_div n 25
  omega
```

この宣言は `private` であり、`SignedFiveAdic.lean` 内部で剰余情報 `n % 25 = 5` を、後続の可除性証明で直接扱える明示的な商・余り分解へ変換する補題である。

## 数学的主張

自然数 `n` が 25 で割って余り 5 なら、ある自然数 `M` が存在して

$$
n=5+25M
$$

と書ける。

これは除法算法

$$
n=(n\bmod25)+25\left\lfloor\frac{n}{25}\right\rfloor
$$

に `n % 25 = 5` を代入したものにほかならない。証明中では witness として

$$
M=n/25
$$

を選ぶ。

## 証明全体での役割

0068 は `ZMod 25` 上の residual 等式を自然数の

$$
residual\bmod25=5
$$

へ戻した。本補題 0069 はその剰余式を

$$
residual=5+25M
$$

へ変換する。

この形になると後続補題 `five_dvd_of_eq_five_add_twentyFive_mul` が `5 ∣ residual` の witness を直接構成できる。difference branch と sum branch の双方で、本補題は `hmod` の直後に呼ばれている。

依存の流れは

```text
(residual : ZMod 25) = 5
             ↓ 0068
      residual % 25 = 5
             ↓ 0069
      residual = 5 + 25*M
             ↓
          5 ∣ residual
```

である。同時に元の `hmod` は別補題で `25 ∤ residual` を示すため保持され、最終的に residual の 5-adic valuation がちょうど 1 であることへ進む。

## 直接依存する定義・補題

- `Nat.mod_add_div`
- 自然数除算 `/` と剰余 `%`
- `omega`

本補題は 0068 自体を呼ばない。入力型を `n % 25 = 5` に限定した一般的な算術 bridge であり、0068 は主要 consumer 側からこの入力を供給する。

## 証明の流れ

1. 存在量 `M` の witness として `n / 25` を選ぶ。
2. `Nat.mod_add_div n 25` から、剰余と商による `n` の標準分解を取得する。
3. 仮定 `hmod : n % 25 = 5` とその標準分解を `omega` に渡す。
4. `n = 5 + 25 * (n / 25)` を得て存在証明を閉じる。

## Lean 固有の処理

`Nat.mod_add_div` の等式は人間が通常使う `n = n % 25 + 25 * (n / 25)` と向きや項順が一致しない場合がある。現行証明は `hsplit` を明示的に保持し、細かな加法・乗法の並べ替えを `omega` に任せている。

`refine ⟨n / 25, ?_⟩` によって存在量の選択を先に固定しているため、証明の構成的内容は明瞭である。ここで `M` は抽象的存在ではなく標準商そのものである。

## 冗長・重複箇所

証明は非常に短く、論理的重複はほぼない。ただし `have hsplit := ...` は一度しか使われず、`omega` の直前へ直接渡せる可能性がある。

また 25 と余り 5 が固定されているため、同型の補題が別 modulus/residue で必要になれば重複が生じる。一般形

```lean
n % m = r → ∃ q, n = r + m * q
```

を共通 bridge として持てば特殊化できる。

## 最適化候補

第一候補は `Nat.mod_add_div` を用いた `calc` で `omega` 依存を減らすことである。例えば標準分解を対称化し、`hmod` を rewrite して終える形にできれば、算術 tactic に隠れているデータフローがさらに明示的になる。

第二候補は modulus/residue を一般化した helper theorem への抽象化である。本補題の数学的内容は 25 や 5 に固有ではない。

第三候補は後続の `five_dvd_of_eq_five_add_twentyFive_mul` と一体化し、`n % 25 = 5` から直接 `5 ∣ n` を得る補題を作る案である。ただし現在の `n = 5 + 25M` という中間形は five-adic 構造を監査しやすくするため、教育・監査上は残す価値がある。

## 必要 Mathlib import と import 最適化候補

生成済み `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用している。本補題自身が必要とする主要 API は自然数の division/modulus と `Nat.mod_add_div`、および `omega` tactic である。

したがって最小 import 候補は Nat の除算・剰余 API と `Mathlib.Tactic.Omega` 相当であると考えられる。ただし対象ブランチ上で分割元 `DkMath/FLT/Five/SignedFiveAdic.lean` の正確な import 行を直接確認できていないため、具体的な最小 import 名は未確認の推測である。

本回では Lean ビルドを行っていないため、import 縮小案の検証はしていない。

## Comparator challenge 化の可否

適している。小さな補題なので、証明スタイル比較がしやすい。

- 現行: witness `n / 25` + `Nat.mod_add_div` + `omega`
- 候補 A: `calc` と `rw [hmod]` を中心にした tactic-light 証明
- 候補 B: 一般 modulus/residue helper の特殊化
- 候補 C: `% 25 = 5` から直接 `5 ∣ n` を得て中間存在量を省略

比較軸は行数だけでなく、除法算法の可視性、`omega` への依存度、一般化可能性、後続 consumer との接続の明瞭さである。

## 根拠と推測

定理名・型・完全な証明本体は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` で確認した。同ソースで difference branch と sum branch の双方が 0068 の直後に本補題を利用し、その結果を `five_dvd_of_eq_five_add_twentyFive_mul` へ渡していることも確認した。

GitHub コード検索は本回も一時的な upstream error を返したため、既知の standalone ソースを直接取得して確認した。既存の日英 PDF における具体的対応ページは確認できておらず、PDF 固有のページ番号・説明は推測で補っていない。

## 次に読むべき定理

```lean
private theorem five_dvd_of_eq_five_add_twentyFive_mul
    {n M : ℕ} (h : n = 5 + 25 * M) :
    5 ∣ n
```

0069 の明示的な形 `n=5+25M` から、residual に 5 が一度以上含まれることを witness 付きで取り出す次の bridge である。
