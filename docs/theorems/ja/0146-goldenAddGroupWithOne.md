# 0146 — `goldenAddGroupWithOne`

## Lean の型

```lean
instance goldenAddGroupWithOne : AddGroupWithOne GoldenInt :=
  { goldenAddCommGroup with
    natCast := fun n => ⟨n, 0⟩
    intCast := fun z => ⟨z, 0⟩ }
```

これは theorem ではなく、0145 で構築した `AddCommGroup GoldenInt` を土台として、自然数・整数から `GoldenInt` への標準 cast を追加し、`AddGroupWithOne GoldenInt` を与える named `instance` である。

## 数学的主張・宣言の意味

`GoldenInt` は $a+b\varphi$ を整数座標 `(a,b)` で表す。自然数 $n$ と整数 $z$ は、黄金整数ではそれぞれ

$$
n \longmapsto n+0\varphi,
$$

$$
z \longmapsto z+0\varphi
$$

として埋め込まれる。本 instance の

```lean
natCast := fun n => ⟨n, 0⟩
intCast := fun z => ⟨z, 0⟩
```

は、この標準的な基底 `1` 方向の埋め込みを直接実装している。

数学的には、新しい演算を導入する宣言ではない。0145 までに完成している可換加法群に対して、整数環 $\mathbb Z$ の通常の数を `GoldenInt` の定数項として解釈できるようにする interface declaration である。

## 証明全体での役割

0145 `goldenAddCommGroup` により、`GoldenInt` はすでに可換加法群として Mathlib の algebra hierarchy に参加している。しかし、この段階だけでは自然数リテラル・整数 cast と加法構造の標準的な接続がまだ完全ではない。

本宣言は、

$$
\texttt{AddCommGroup GoldenInt}
\longrightarrow
\texttt{AddGroupWithOne GoldenInt}
$$

という橋を作る。

この橋が重要なのは、直後の 0147 `goldenCommRing` が `goldenAddGroupWithOne` を基礎 structure として再利用して `CommRing GoldenInt` を構築するからである。したがって本宣言は、加法群から完全な環構造へ進む途中の cast / numeral layer を閉じる。

FLT5 全体では、黄金整数上で `0`、`1`、自然数、整数係数を通常の Lean 記法で扱えることが、ノルム恒等式、共役、整除、Euclidean-domain 構造、第五冪分解などの後続議論に不可欠である。

## 直接依存する定義・補題

直接依存は次の通りである。

- `GoldenInt`
- 0145 `goldenAddCommGroup`
- `AddGroupWithOne`
- 自然数から整数への cast `(n : ℤ)`
- `GoldenInt` の constructor `⟨_, _⟩`

明示的な theorem dependency はほとんどなく、0145 で得た加法群 structure を再利用し、`natCast` と `intCast` の実装だけを追加する。

依存関係は概念的に

$$
\texttt{goldenAddCommGroup}
\longrightarrow
\texttt{goldenAddGroupWithOne}
\longrightarrow
\texttt{goldenCommRing}
$$

となる。

## 証明・構築の流れ

proof script は存在しない。structure update 構文

```lean
{ goldenAddCommGroup with
  natCast := fun n => ⟨n, 0⟩
  intCast := fun z => ⟨z, 0⟩ }
```

を使い、0145 の `goldenAddCommGroup` が持つ加法構造を引き継ぎつつ、`AddGroupWithOne` に必要な cast 実装を追加している。

自然数については `n : ℕ` を第一座標へ整数として入れ、第二座標を `0` に固定する。整数についても同様に第一座標へそのまま入れる。

したがって、

$$
(n : \texttt{GoldenInt})=(n,0),
$$

$$
(z : \texttt{GoldenInt})=(z,0)
$$

という表現が標準 cast machinery から利用可能になる。

## Lean 固有の処理

重要なのは `{ goldenAddCommGroup with ... }` という structure update である。これは 0145 で明示的に構築した加法群 structure の field を再利用し、より上位の algebra structure に必要な追加 field を与える書き方である。

また

```lean
natCast := fun n => ⟨n, 0⟩
```

では `n : ℕ` が第一座標 `ℤ` に期待されるため、Lean の coercion により整数へ cast される。対して

```lean
intCast := fun z => ⟨z, 0⟩
```

では `z : ℤ` をそのまま第一座標へ入れられる。

本宣言には tactic proof がなく、cast の具体的な representation を definition level で固定する。このため後続で numeral や integer cast を含む式を展開した際も、座標 `(z,0)` へ透明に落としやすい。

なお、`AddGroupWithOne` の正確な内部 field 継承関係や既定実装の細部は Mathlib version に依存しうる。本稿では source 上でこの structure update が採用されている事実を根拠とし、未確認の内部 hierarchy details は断定しない。

## 冗長・重複箇所

`natCast` と `intCast` は数学的にはどちらも「定数項への埋め込み」であり、

$$
n \mapsto (n,0),\qquad z \mapsto (z,0)
$$

という非常に近い実装を持つ。その意味では小さな重複がある。

また `GoldenInt` が本質的に整数座標 pair であることを利用すれば、より一般的な scalar embedding helper を先に定義して両 cast から再利用する設計も可能である。

しかし現行実装は、自然数 cast と整数 cast を Mathlib の期待する field に直接対応させており、読み手が cast の正体を即座に確認できるという利点がある。

## 最適化候補

候補は次の通りである。

1. 現行の直接的な `natCast` / `intCast` 定義を維持する。
2. `goldenOfInt : ℤ → GoldenInt := fun z => ⟨z,0⟩` のような helper を定義し、`intCast` と `natCast` から共有する。
3. `GoldenInt` と既存の quadratic-order representation の同型を用意し、cast structure を transport する。
4. 0145–0147 を一つの `CommRing` constructor にまとめ、途中の `AddGroupWithOne` instance を明示しない構成と比較する。

ただし 4 はコード量を減らせても、加法群 → cast layer → 可換環という bootstrap の段階が見えにくくなる。監査可能性を重視する現行設計では、0146 を独立させる意味がある。

## 必要 Mathlib import と import 最適化候補

standalone artifact は

```lean
import Mathlib
```

を使用している。

本宣言単体で必要なのは `AddGroupWithOne`、自然数・整数 cast、0145 の `goldenAddCommGroup` と `GoldenInt` の constructor であり、高度な number theory theorem は使用しない。

したがって `Mathlib` umbrella import 全体が本宣言単独のために必要とは考えにくい。しかし exact minimal import は `GoldenOrder` 上流と Mathlib hierarchy の version-specific dependency を含めて Lean build で検証する必要がある。今回 Lean build は行わないため、最小 import 名は確定しない。

## Comparator challenge 化の可否

適している。特に次の三方式を比較できる。

- 現行の `AddCommGroup` から `AddGroupWithOne` への段階的 structure update
- cast helper を共有した implementation
- `CommRing` を直接構築し、途中 instance を省略する implementation

評価軸は、定義展開の透明性、instance search の安定性、cast simplification、後続 `goldenCommRing` の簡潔さ、representation 変更への耐性、source の監査容易性である。

小さな宣言だが、Lean の algebra hierarchy を段階的に組み上げる設計と、一括構築する設計の比較に向いている。

## PDF・Lean source との対応

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。

形式的根拠は `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/GoldenOrder.lean` generated section である。そこでは 0145 `goldenAddCommGroup` の直後に本 `goldenAddGroupWithOne` が置かれ、続いて `goldenCommRing` が構築される。

この小さな algebra-interface instance に対応する PDF の具体的ページ・節は今回直接特定していないため、PDF 上の位置は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
instance goldenCommRing : CommRing GoldenInt := by
  refine
    { goldenAddGroupWithOne with
      npow := fun n x => goldenPow x n
      npow_zero := by intro x; rfl
      npow_succ := by
        intro n x
        change goldenPow x (n + 1) = goldenMul (goldenPow x n) x
        rfl
      add_comm := ?_
      left_distrib := ?_
      right_distrib := ?_
      zero_mul := ?_
      mul_zero := ?_
      mul_assoc := ?_
      one_mul := ?_
      mul_one := ?_
      mul_comm := ?_ } <;>
    intros <;> ext <;>
    simp <;> ring
```

である。

0145 で可換加法群、0146 で自然数・整数 cast を備えた `AddGroupWithOne` が揃った。次の 0147 では `goldenMul` と `goldenPow` を含む乗法側の law を証明し、`GoldenInt` を完全な `CommRing` として Mathlib の環論 API に載せる。