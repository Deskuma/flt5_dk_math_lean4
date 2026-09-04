# 0154 — `instance : Nontrivial GoldenInt`

## Lean の型

```lean
instance : Nontrivial GoldenInt := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have := congrArg GoldenInt.fst h
  norm_num at this
```

これは theorem ではなく、`GoldenInt` に Mathlib 標準の型クラス `Nontrivial` を登録する匿名 `instance` である。

## 数学的主張・宣言の意味

`Nontrivial GoldenInt` は、`GoldenInt` に少なくとも二つの異なる元が存在することを表す。ここでは具体的に標準記法の `0` と `1` を選び、

$$
0 \neq 1
$$

を証明している。

`GoldenInt` は整数座標の対として実装され、標準零元と単位元はそれぞれ

$$
0=(0,0),\qquad 1=(1,0)
$$

に対応する。したがって第一座標を比較すれば `0 = 1` は整数上の `0 = 1` を強制し、矛盾する。

## 証明全体での役割

直前の 0153 では、0152 で得た零積分解を `NoZeroDivisors GoldenInt` として登録した。しかし `NoZeroDivisors` だけでは、環が一元環に退化していないことまでは保証しない。

0154 は `GoldenInt` が非自明であることを標準型クラスとして追加し、直後の

```lean
instance : IsDomain GoldenInt := NoZeroDivisors.to_isDomain _
```

へ進むための最後の構造条件を供給する。

したがって 0153–0155 の流れは概念的に

$$
\texttt{NoZeroDivisors GoldenInt}
+\texttt{Nontrivial GoldenInt}
\longrightarrow
\texttt{IsDomain GoldenInt}
$$

となる。0148 以降で具体的に証明した零因子排除を、ここで Mathlib の整域 hierarchy に接続するための短いが重要な橋である。

## 直接依存する定義・補題

直接依存は次の要素である。

- `GoldenInt`
- `Zero GoldenInt`
- `One GoldenInt`
- projection `GoldenInt.fst`
- 標準型クラス `Nontrivial`
- `congrArg`
- `norm_num`

0153 `NoZeroDivisors GoldenInt` は数学的には直後の `IsDomain` 構築で並んで使われるが、本 0154 の proof term 自体から直接参照されてはいない。

## 証明・構築の流れ

証明は非常に短い。

```lean
refine ⟨⟨0, 1, ?_⟩⟩
```

で `Nontrivial GoldenInt` の witness として `0` と `1` を選び、その相違を示す goal を残す。

次に

```lean
intro h
```

で反対仮定 `h : 0 = 1` を導入する。

その等式に第一座標射影を作用させるため、

```lean
have := congrArg GoldenInt.fst h
```

とする。これにより `GoldenInt` の等式は整数第一座標の等式へ移される。

最後に

```lean
norm_num at this
```

で第一座標の `0 = 1` を数値正規化し、矛盾から goal を閉じる。

数学的には

$$
(0,0)=(1,0)
\Longrightarrow
0=1
\Longrightarrow
\bot
$$

という一行の証明を Lean の structure witness と projection に分解したものである。

## Lean 固有の処理

`Nontrivial α` は「異なる二元が存在する」ことを保持する型クラスであり、`⟨⟨0, 1, ?_⟩⟩` はその内部の存在 witness を明示的に構築している。

`congrArg GoldenInt.fst h` は、複合 structure `GoldenInt` の等式を座標等式へ落とす標準的な Lean パターンである。`cases h` や `GoldenInt.ext` の逆向き利用ではなく、必要な座標だけを射影して矛盾を得るため proof state が小さい。

また `norm_num at this` は `GoldenInt` 全体を理解する必要がない。`Zero` / `One` instance の definitional reduction と `fst` projection によって整数の `0 = 1` まで落ちれば、数値 tactic が処理できる。

## 冗長・重複箇所

`GoldenInt` が `ℤ × ℤ` 型の明示座標を持つ以上、非自明性は構造的には自明である。そのため本 instance は数学的内容としては重い証明ではない。

また 0 と 1 を選ぶ以外に、`⟨0,0⟩` と `⟨1,0⟩` を直接 witness にしても同じ証明ができる。現行コードは既に登録済みの標準 `0` / `1` notation を使うことで algebra API に沿った形にしている。

0154 と直後の `IsDomain GoldenInt` を一つの大きな instance に埋め込むことも理論上は可能だが、`Nontrivial` を独立 instance として残す方が typeclass hierarchy の境界が明瞭である。

## 最適化候補

候補は次の通りである。

1. 現行のように `0` と `1` を witness とし、第一座標へ `congrArg` して矛盾を出す。
2. `exact ⟨0, 1, ...⟩` 型のより短い constructor syntax に整理する。
3. `GoldenInt` の基底型が product / structure として非自明であることから一般 instance を導けるなら、それを再利用する。
4. `zero_ne_one` が既存 instance 群から既に導出可能な段階なら、その theorem を直接使って `Nontrivial` を構築する。

ただし 3 や 4 は instance dependency の循環を生まないか確認が必要である。現行 proof は上流依存が少なく、bootstrap が明示的なので監査性が高い。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本宣言が直接利用する機能は `Nontrivial`、`congrArg`、整数上の `norm_num`、および上流で構築済みの `GoldenInt` の `Zero` / `One` instance である。

したがって 0154 単独のために `Mathlib` 全体を必要とするとは考えにくい。より細かい import では、基礎 typeclass 群と `norm_num` tactic を提供するモジュールが中心になるはずである。

ただし今回は Lean build を行っていないため、正確な最小 import 集合は未検証である。この点は import 最適化候補としての推測である。

## Comparator challenge 化の可否

適しているが、非常に小さな Comparator challenge になる。

比較候補としては、

- `congrArg GoldenInt.fst` + `norm_num`
- structure の constructor injectivity を直接利用
- product / subtype / `Equiv` などから一般 `Nontrivial` instance を継承
- `zero_ne_one` を使う algebra hierarchy 主導の構築

を試せる。

比較軸は、依存する既存 instance の数、bootstrap の循環可能性、コード量、proof state の透明性、後続 `IsDomain` 構築との結合度である。

この宣言単独の数学は簡単だが、「非自明性をどの階層で供給するか」という Lean typeclass design の比較には向いている。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `GoldenOrder` 部分である。そこでは 0153 の `NoZeroDivisors GoldenInt` の直後に本 `Nontrivial GoldenInt` instance があり、その次に `IsDomain GoldenInt` が置かれている。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` も存在する。ただし本 instance に対応する具体的 PDF ページ・節は今回直接特定していないため、推測しない。

## 次に読むべき宣言

依存順の次は

```lean
instance : IsDomain GoldenInt := NoZeroDivisors.to_isDomain _
```

である。

0153 の零因子なしと 0154 の非自明性が揃ったことで、次はそれらを標準 `IsDomain` hierarchy にまとめて登録する段階へ進む。