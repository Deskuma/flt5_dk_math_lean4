# 0109 — `signed_endpoint_square_discriminant`

## Lean の型

```lean
/-- The signed endpoint coordinates retain a square discriminant. -/
theorem signed_endpoint_square_discriminant (x y : ℤ) :
    (x ^ 2 + y ^ 2) ^ 2 - 4 * (-(x * y)) ^ 2 =
      (x ^ 2 - y ^ 2) ^ 2 := by
  ring
```

## 数学的主張

任意の整数 $x,y$ に対して、平方和を第一座標、符号を反転した積を第二座標として

$$
M=x^2+y^2,\qquad N=-xy
$$

と置く。このとき square discriminant は

$$
M^2-4N^2=(x^2-y^2)^2
$$

となる。

定義を代入すれば

$$
(x^2+y^2)^2-4(-xy)^2=(x^2-y^2)^2
$$

であり、$(-xy)^2=(xy)^2$ なので、これは差の平方に関する標準的な恒等式

$$
(x^2+y^2)^2-4x^2y^2=(x^2-y^2)^2
$$

そのものである。

## 証明全体での役割

直前の 0108 `sumGN5_eq_goldenNorm_signed` は、和型 residual `SumGN5` を負の cross coordinate

$$
N=-uv
$$

を持つ黄金ノルムへ移した。本定理は同じ signed endpoint 座標が、黄金ノルムだけでなく square discriminant も保持することを保証する。

後続の signed exceptional packet 構築では、和型 source に対して

```lean
have hSquare : M ^ 2 - 4 * N ^ 2 = delta ^ 2 := by
  dsimp [M, N, delta]
  exact signed_endpoint_square_discriminant (u : ℤ) (v : ℤ)
```

という形で直接利用される。したがって 0108 と 0109 は対になっており、和型 source を既存の square/golden invariant API に載せる二本の入口 bridge とみなせる。

本定理の直後には `SignedSquareGoldenSource` が定義され、difference orientation と sum orientation の双方について $M,N,\delta$ の由来を記録する。0109 はそのうち sum orientation の square discriminant を閉じるための基本恒等式である。

## 直接依存する定義・補題

この theorem は数学的には自己完結しており、リポジトリ固有の定義や補題を直接参照しない。

Lean 上で直接必要なのは次の機能である。

- 整数型 `ℤ`。
- 加法・減法・乗法・冪。
- `ring` tactic による可換環の多項式正規化。

意味上の隣接依存としては、直前の `sumGN5_eq_goldenNorm_signed` と後続の `SignedSquareGoldenSource` / signed exceptional packet 構築がある。ただし theorem 本体の型にはそれらは現れない。

## 証明の流れ

証明は一行である。

```lean
by
  ring
```

`ring` は両辺を可換環上の正規形へ展開し、同一の多項式であることを機械的に確認する。

左辺は概念的には

$$
(x^2+y^2)^2-4(-xy)^2
$$

から

$$
x^4+2x^2y^2+y^4-4x^2y^2
$$

へ展開され、

$$
x^4-2x^2y^2+y^4
$$

となる。右辺 $(x^2-y^2)^2$ も同じ正規形へ展開されるため閉じる。

## Lean 固有の処理

ここでは変数を最初から `ℤ` に取っているため、`Nat.sub` の truncated subtraction や `Nat.cast_sub` のような大小条件付き cast 処理は一切不要である。これは 0108 と鮮明な対照をなす。

また負号は積の外側にあるが、`ring` は

$$
(-xy)^2=x^2y^2
$$

を含む符号処理を自動的に正規化する。そのため `simp [pow_two]` や `neg_sq` に相当する補助処理を手で入れる必要はない。

Lean 的には、この theorem は signed coordinate を採用したことで自然数の枝分けが消え、純粋な整数多項式 identity に落ちた好例である。

## 冗長・重複箇所

式の内容は 0103 `squareGolden_square_discriminant` および、その下位にある `endpoint_square_discriminant` と強く重複する。

違いは cross coordinate の符号である。

- difference orientation: $N=xy$。
- sum orientation: $N=-xy$。

しかし discriminant では $N^2$ しか現れないため、符号は消える。したがって数学的には signed 版を別 theorem として再証明する必要性は低い。

一方、API としては後続 source の形にぴたりと一致するため、呼び出し側で符号消去の rewrite を書かずに済む。したがってこれは論理的重複というより、downstream 可読性のための wrapper 的重複と評価できる。

## 最適化候補

1. 既存 `endpoint_square_discriminant` を再利用し、`simpa` だけで signed 版を導出できるか比較する。
2. discriminant が第二座標の符号に不変である一般補題

   $$
   M^2-4(-N)^2=M^2-4N^2
   $$

   を用意し、difference/sum の双方を同じ基礎 theorem から導出する。
3. `SignedSquareGoldenSource` の constructor ごとに square-discriminant theorem を提供し、個別 endpoint theorem を API の内部へ隠す。
4. 現行の一行 `ring` は極めて短く堅牢なので、抽象化によって証明行数を減らす効果はほぼない。最適化の主目的は重複除去と概念 API の整理になる。

## 必要 Mathlib import と import 最適化候補

standalone artifact は全体として

```lean
import Mathlib
```

を使用している。

本 theorem 単独では整数上の環演算と `ring` tactic があれば足りるため、Mathlib 全体の import は明らかに過剰である。候補としては `Mathlib.Tactic.Ring` と、それが必要とする整数・代数基盤へ縮小できる可能性が高い。

ただし対象リポジトリの実モジュールは standalone artifact に生成結合されており、このブランチから個別 `SignedSquareGoldenExceptional.lean` の import 行を直接取得できなかった。そのため「実ファイルとしての最小 import 集合」は Lean build を行わずに断定せず、ここでは最適化候補として記録する。

## Comparator challenge 化の可否

適している。特に短い theorem なので、証明スタイルの差が明瞭に比較できる。

候補は次の三方式である。

1. 現行: `ring` 一発。
2. 再利用: 既存 `endpoint_square_discriminant` を `simpa` で signed 座標へ移す。
3. 一般不変性: $N\mapsto -N$ に対する discriminant invariance を先に証明し、既存 theorem と合成する。

評価軸は最短行数だけではなく、既存 theorem との重複をどこまで除けるか、signed orientation という意味がソース上で読み取れるか、後続 packet 構築から自然に呼べるか、で比較するとよい。

## 既存資料との対応

形式的根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` に生成収録された `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` 区間である。

standalone artifact の manifest はこの module が `SquareGoldenNormalForm.lean` の直後、`GoldenOrder.lean` の直前に置かれることを示す。

既存日本語・英語 PDF の具体的ページ・節番号は今回の GitHub connector から確定できなかったため、推測で番号を付していない。PDF と Lean source の叙述が異なる場合、この博物館では Lean source を形式的正本とする。

## 次に読むべき定理

依存順で次の未解説宣言は theorem ではなく、次の inductive definition である。

```lean
inductive SignedSquareGoldenSource
    (u v w : ℕ) (M N delta : ℤ) : Prop
  | difference :
      M = (w : ℤ) ^ 2 + (v : ℤ) ^ 2 →
      N = (w : ℤ) * (v : ℤ) →
      delta = (w : ℤ) ^ 2 - (v : ℤ) ^ 2 →
      SignedSquareGoldenSource u v w M N delta
  | sum :
      M = (u : ℤ) ^ 2 + (v : ℤ) ^ 2 →
      N = -((u : ℤ) * (v : ℤ)) →
      delta = (u : ℤ) ^ 2 - (v : ℤ) ^ 2 →
      SignedSquareGoldenSource u v w M N delta
```

0108 が和型 residual の黄金ノルム bridge、0109 が同じ signed endpoint の square-discriminant bridgeを与えたことで、difference と sum の二 orientation を一つの provenance 型へ束ねる準備が整った。次号は `SignedSquareGoldenSource` を読むのが依存順として正しい。