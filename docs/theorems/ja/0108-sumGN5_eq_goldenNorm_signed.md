# 0108 — `sumGN5_eq_goldenNorm_signed`

## Lean の型

```lean
/-- The sum residual is the golden norm with a negative cross-beam coordinate. -/
theorem sumGN5_eq_goldenNorm_signed (u v : ℕ) :
    GoldenNorm
        ((u : ℤ) ^ 2 + (v : ℤ) ^ 2)
        (-((u : ℤ) * (v : ℤ))) =
      (SumGN5 u v : ℤ) := by
  unfold GoldenNorm SumGN5
  by_cases h : v ≤ u
  · rw [if_pos h]
    push_cast
    rw [Nat.cast_sub h]
    ring
  · rw [if_neg h]
    have huv : u ≤ v := Nat.le_of_not_ge h
    push_cast
    rw [Nat.cast_sub huv]
    ring
```

## 数学的主張

自然数 $u,v$ に対し、平方和座標

$$
M=u^2+v^2
$$

と、符号を反転した交差座標

$$
N=-uv
$$

を取ると、黄金ノルム

$$
\operatorname{GoldenNorm}(M,N)=M^2+MN-N^2
$$

は `SumGN5 u v` と一致する。

すなわち

$$
\operatorname{GoldenNorm}(u^2+v^2,-uv)=\operatorname{SumGN5}(u,v).
$$

`SumGN5` は自然数上で差を負にしないため $v\le u$ と $u\le v$ の二枝を持つが、整数上の黄金ノルムへ移した後は、この二枝が同一の符号付き二次形式へ統合される。

## 証明全体での役割

この定理は `SignedSquareGoldenExceptional.lean` の入口に置かれ、和型の signed five-adic source を square/golden 座標へ接続する bridge である。

直前までの `SquareGoldenNormalForm` では差型の座標

$$
M=z^2+y^2,\qquad N=zy
$$

を用いていた。一方、signed exceptional 段階では和型 source も同じ packet に収める必要がある。そのため和型では交差座標を

$$
N=-uv
$$

とし、`SumGN5` を同じ `GoldenNorm` API へ載せる。

後続の `nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit` の `sum` 分岐では、この定理を直接用いて

```lean
have hGoldenBase : GoldenNorm M N = (SumGN5 u v : ℤ) := by
  simpa [M, N] using sumGN5_eq_goldenNorm_signed u v
```

とし、残差が $5b^5$ である five-adic 情報を黄金ノルムへ輸送する。したがって本定理は、差型と和型を共通の `SignedSquareGoldenExceptionalPacket` に合流させるための和型側の入口である。

## 直接依存する定義・補題

直接の主要依存は次の二つである。

- `GoldenNorm` — 整数二変数の黄金二次形式。
- `SumGN5` — $(u+v)$ に対応する fifth-power residual。自然数減算を扱うため大小関係による `if` を含む。

証明技術上は `Nat.cast_sub`、`Nat.le_of_not_ge`、`push_cast`、`ring` を使用する。

## 証明の流れ

まず `GoldenNorm` と `SumGN5` を `unfold` し、両辺を具体的な多項式へ展開する。

次に

```lean
by_cases h : v ≤ u
```

で `SumGN5` の定義と同じ大小分岐を行う。

### $v\le u$ の枝

`if_pos h` で `SumGN5` の第一枝を選び、`push_cast` で自然数式の cast を整数式へ押し込む。その後

```lean
rw [Nat.cast_sub h]
```

により

$$
\uparrow{(u-v)}=(u:\mathbb Z)-(v:\mathbb Z)
$$

へ変換し、最後は `ring` で多項式恒等式として閉じる。

### $v\nleq u$ の枝

`if_neg h` で第二枝を選ぶ。自然数は全順序なので

```lean
have huv : u ≤ v := Nat.le_of_not_ge h
```

を得て、同様に `push_cast` と `Nat.cast_sub huv` で減算を整数差へ移し、`ring` で終了する。

## Lean 固有の処理

数学的には対称な単一の恒等式であるが、Lean では `SumGN5` が `ℕ` 上の truncated subtraction を含むため、そのまま `ring` だけでは処理できない。

重要なのは `Nat.cast_sub` に大小条件が必要な点である。Lean の自然数減算は整数減算と違い負値を持たないため、

$$
\uparrow{(u-v)}=\uparrow u-\uparrow v
$$

を使うには $v\le u$ の証明が必要になる。第二枝ではその役割を `huv : u ≤ v` が担う。

`push_cast` は係数・積・冪の cast を整理し、`ring` が純粋な整数多項式として認識できる形へ正規化するために使われている。

## 冗長・重複箇所

二つの枝は、`if` の選択と `Nat.cast_sub` に渡す不等式が異なるだけで、

```lean
push_cast
rw [Nat.cast_sub ...]
ring
```

という終盤はほぼ同型である。

この重複は `SumGN5` を自然数の piecewise residual として定義した結果生じる実装上の重複であり、数学的な重複ではない。

また、差型には既に `GN5_eq_goldenNorm_squareLink` があり、本定理はその signed-sum counterpart と見なせる。二つを統一する上位 signed coordinate API を導入すれば、bridge theorem の構造重複を減らせる可能性がある。

## 最適化候補

1. `SumGN5` の piecewise 定義を処理する補助補題を用意し、大小分岐と cast 処理を一箇所へ集約する。
2. 差型 `GN5_eq_goldenNorm_squareLink` と和型本定理を、符号付き cross coordinate を持つ共通 bridge に抽象化する。
3. `simpa` / `norm_cast` を用いた短縮が可能か比較する。ただし `Nat.sub` の枝条件を隠しすぎると監査性が落ちるため、現行の明示的 `by_cases` には教育的価値がある。
4. signed source 自体に $M,N$ の構成を持たせ、residual-to-norm bridge を source ごとの field theorem として提供する設計も候補になる。

## 必要 Mathlib import と import 最適化候補

standalone artifact は全体として

```lean
import Mathlib
```

を使用している。

本定理単独で必要になる機能は、整数・自然数の cast、`Nat.cast_sub`、`push_cast`、`ring`、および既存定義 `GoldenNorm` / `SumGN5` である。したがって tactic 側では少なくとも cast 正規化と ring normalization の import が必要になる。

候補としては `Mathlib.Tactic.PushCast` と `Mathlib.Tactic.Ring`、および `Nat.cast_sub` を供給する代数・cast 系モジュールへ縮小できる可能性がある。ただしこのリポジトリの module 単位での最小 import は Lean build を行わずには確定できないため、ここでは候補に留める。

## Comparator challenge 化の可否

適している。

比較課題としては、次の三方式が明確である。

- 現行方式: `by_cases` + `push_cast` + `Nat.cast_sub` + `ring`。
- 補助補題方式: `SumGN5` の二枝を先に整数多項式へ正規化してから一回の `ring` に集約。
- API 抽象化方式: signed square coordinates を定義し、差型・和型を一つの theorem で処理。

評価軸は proof length だけでなく、`Nat.sub` の安全条件がどれだけ可視であるか、差型との構造対応が読みやすいか、後続 packet 構築で再利用しやすいか、がよい。

## 既存資料との対応

形式的根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` に生成収録された `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` 区間である。

既存日本語・英語 PDF の具体的ページ・節番号は今回の GitHub connector から確定できなかったため、推測で番号を付していない。PDF の叙述と Lean source が異なる場合、この博物館では Lean source を正本とする。

## 次に読むべき定理

依存順で次の theorem は

```lean
theorem signed_endpoint_square_discriminant (x y : ℤ) :
    (x ^ 2 + y ^ 2) ^ 2 - 4 * (-(x * y)) ^ 2 =
      (x ^ 2 - y ^ 2) ^ 2 := by
  ring
```

である。

本定理が和型 residual を負の cross coordinate を持つ黄金ノルムへ接続したのに対し、次の theorem は同じ signed endpoint 座標が square discriminant も保持することを示す。これら二本が揃った後、`SignedSquareGoldenSource` と `SignedSquareGoldenExceptionalPacket` へ進むのが依存順として自然である。
