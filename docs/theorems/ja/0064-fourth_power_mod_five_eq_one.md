# 0064 — `fourth_power_mod_five_eq_one`

## Lean の型

```lean
private theorem fourth_power_mod_five_eq_one
    {n : ℕ} (h5n : ¬ 5 ∣ n) :
    n ^ 4 % 5 = 1 := by
  rw [Nat.pow_mod]
  have hnlt : n % 5 < 5 := Nat.mod_lt _ (by decide)
  have hn0 : n % 5 ≠ 0 := by
    intro hn0
    exact h5n (Nat.dvd_of_mod_eq_zero hn0)
  interval_cases h : n % 5
  · exact (hn0 rfl).elim
  · norm_num [h]
  · norm_num [h]
  · norm_num [h]
  · norm_num [h]
```

この宣言は `private` であり、`SignedFiveAdic.lean` 内部だけで使う局所補題である。

## 数学的主張

自然数 `n` が 5 の倍数でなければ、第四冪は法 5 で 1 になる。

$$
5\nmid n \Longrightarrow n^4\equiv 1\pmod 5.
$$

これは素数 5 に対するフェルマーの小定理の特殊形である。非零剰余類は $1,2,3,4$ のいずれかであり、どの場合も第四冪は 1 に戻る。

## 証明全体での役割

`SumGN5` の sum orientation を法 25 で解析するための基礎補題である。直後の `fourth_power_zmod25_decomposition` は本補題から `n^4 = 1 + 5q` という整数分解を作り、`ZMod 25` 上で

$$
(n: \mathrm{ZMod}\ 25)^4 = 1 + 5q
$$

という形へ持ち上げる。さらにその分解が `SumGN5_cast_mod25_eq_five` の計算に入る。

したがって本補題は、0062–0063 で得た `5 ∤ u`, `5 ∤ v` を、第四冪の剰余情報へ変換する橋である。

## 直接依存する定義・補題

- `Nat.pow_mod`
- `Nat.mod_lt`
- `Nat.dvd_of_mod_eq_zero`
- `interval_cases`
- `norm_num`

前号 0062・0063 には直接依存しない。ただし後続では、それらから得た `5 ∤ u`, `5 ∤ v` を本補題へ入力する。

## 証明の流れ

1. `Nat.pow_mod` で `n ^ 4 % 5` を `(n % 5) ^ 4 % 5` に落とす。
2. `Nat.mod_lt` から `n % 5 < 5` を得る。
3. `5 ∤ n` から `n % 5 ≠ 0` を導く。
4. `interval_cases h : n % 5` により剰余を `0,1,2,3,4` の五場合へ完全分解する。
5. `0` の枝は `hn0` と矛盾。
6. `1,2,3,4` の枝は `norm_num` で閉じる。

## Lean 固有の処理

数学的には「フェルマーの小定理」で一行だが、ここでは有限剰余分類を明示的に実行している。`interval_cases` は `hnlt : n % 5 < 5` を利用して有限個の自然数場合へ展開する。

また `Nat.dvd_of_mod_eq_zero` により、剰余 0 を divisibility へ戻して仮定 `h5n` と衝突させている。

## 冗長・重複箇所

4 本の `norm_num [h]` は完全に同型である。例えば最後の五枝は

```lean
interval_cases h : n % 5
· exact (hn0 rfl).elim
all_goals norm_num [h]
```

のようにまとめられる可能性がある。

また主張自体は一般のフェルマー小定理の特殊例なので、Mathlib に適切な既存補題があれば有限場合分け全体を置き換えられる。

## 最適化候補

第一候補は `Nat.Prime` に対するフェルマー小定理または `ZMod 5` の単元群を使うことである。ただし本補題は 5 固定で極めて小さく、現在の有限分類は監査しやすいという長所もある。

局所最適化としては `interval_cases` 後の 4 枝の統合が安全である。

## 必要 Mathlib import と import 最適化候補

生成済み standalone artifact は `import Mathlib` を使っていることを確認した。分割元 `DkMath/FLT/Five/SignedFiveAdic.lean` 自体はこの博物館ブランチから取得できなかったため、正確な最小 import は未確認である。

推測として必要なのは、自然数の modular arithmetic、`interval_cases` tactic、`norm_num` tactic を供給するモジュールである。最小 import 化は分割元ファイルを直接取得してビルド確認するまで確定できない。

## Comparator challenge 化の可否

適している。短く、入力と出力が明確で、複数の証明戦略を比較できる。

- 現行: `interval_cases` による有限全探索
- 候補 A: フェルマーの小定理
- 候補 B: `ZMod 5` での有限計算
- 候補 C: `decide` / `native_decide` を使った有限命題への再符号化

比較軸は証明行数、依存 import、kernel transparency、一般化可能性である。

## 根拠と推測

定理名・型・証明本体・直後の consumer は `Flt5DkMath/FLT5StandAlone.lean` で確認した。既存の日英 PDF の本補題に対応する具体的ページは今回確認できていないため、PDF 固有の説明は推測で補っていない。

## 次に読むべき定理

```lean
private theorem fourth_power_zmod25_decomposition
    {n : ℕ} (h5n : ¬ 5 ∣ n) :
    ∃ q : ℕ, (n : ZMod 25) ^ 4 = 1 + 5 * (q : ZMod 25)
```

本号で得た法 5 の第四冪合同を、法 25 の `ZMod` 上で扱える一次の 5-adic 分解へ持ち上げる補題である。
