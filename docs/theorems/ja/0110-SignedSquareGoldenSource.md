# 0110 — `SignedSquareGoldenSource`

## Lean の型

```lean
/-- Provenance of the square-golden coordinates in the two signed orientations. -/
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

## 数学的主張

`SignedSquareGoldenSource u v w M N delta` は、整数三座標 $(M,N,\delta)$ が signed square-golden 構成の二つの向きのどちらから来たかを記録する命題型である。

`difference` constructor では

$$
M=w^2+v^2,\qquad N=wv,\qquad \delta=w^2-v^2
$$

を記録する。

`sum` constructor では

$$
M=u^2+v^2,\qquad N=-uv,\qquad \delta=u^2-v^2
$$

を記録する。

したがって本宣言そのものは新しい数論的等式を証明する theorem ではなく、後続の証明が「差型」と「和型」を一つの interface で扱えるように provenance を型として保存する。

## 証明全体での役割

直前の 0108 `sumGN5_eq_goldenNorm_signed` と 0109 `signed_endpoint_square_discriminant` は、和型 orientation において負の積 $N=-uv$ を採用すれば、golden norm と square discriminant が自然な整数恒等式として統一されることを示した。

一方、既存の square-golden difference 側では正の積 $N=wv$ を使う。後続の `SignedSquareGoldenExceptionalPacket` は、この二つを同じ field 群

$$
(M,N,\delta)
$$

として保持し、その由来だけを `source : SignedSquareGoldenSource ...` に委ねる。本宣言は、その packet が branch-specific な座標定義を直接抱え込まずに済むための provenance layer である。

特に後続では、`source` を cases 分解すれば、difference branch と sum branch それぞれについて $M,N,\delta$ の具体式を復元できる。これは「共通 invariant」と「由来の違い」を分離する設計になっている。

## 直接依存する定義・補題

直接依存は極めて小さい。

- `ℕ`, `ℤ`
- 自然数から整数への coercion `(u : ℤ)` など
- 整数の加法、減法、乗法、冪
- Lean の `inductive` 宣言

直前の 0108・0109 を型として直接参照してはいない。ただし設計上は、0108・0109 によって sum constructor が選ぶ

$$
M=u^2+v^2,\qquad N=-uv,\qquad \delta=u^2-v^2
$$

という座標が golden norm と square discriminant に適合することが既に確立されている。

## 証明の流れ

`inductive` 宣言なので theorem proof script は存在しない。代わりに二つの constructor が inhabitance の方法を定義する。

1. `difference` は三つの等式を受け取り、difference provenance を構築する。
2. `sum` は三つの等式を受け取り、sum provenance を構築する。
3. consumer 側は `cases hSource` または `rcases hSource` によって二つの orientation を分岐し、それぞれの等式を利用できる。

これは proposition-valued tagged union と考えると分かりやすい。

## Lean 固有の処理

重要なのは、constructor 自身が $M,N,\delta$ を生成するのではなく、外部から渡された $M,N,\delta$ が所定の式に等しいという証明を受け取る設計である。

たとえば `difference` は

```lean
M = (w : ℤ) ^ 2 + (v : ℤ) ^ 2
```

などを仮定として受け取る。このため後続 packet は $M,N,\delta$ を独立 field として保持したまま、その provenance を別 field で証明できる。

また自然数 $u,v,w$ を整数座標へ埋め込む coercion が constructor の型に明示されているため、consumer 側では `Nat.sub` の切り詰めを避け、符号付き差 $u^2-v^2$ や $w^2-v^2$ をそのまま扱える。

## 冗長・重複箇所

`difference` と `sum` は形がほぼ同型であり、両方とも

$$
M=A^2+v^2,\qquad \delta=A^2-v^2
$$

を持つ。違いは第一 base が $w$ か $u$ か、そして

$$
N=Av
$$

か

$$
N=-Av
$$

かである。

したがってデータ構造としては、orientation sign と base selection を別パラメータにして一つの constructor に一般化する余地がある。ただし現状の二 constructor は数論上の二つの起源を型レベルで明示し、case split の意味を読みやすくしているので、重複は意図的な可読性コストとも評価できる。

また既存の `SignedBranchAOrientation` など「二つの signed orientation」を表す型と概念的に近い可能性がある。ただし本記事では、その宣言との厳密な同値関係までは Lean source 上で直接証明されていないため、統合可能性は最適化候補として扱う。

## 最適化候補

候補は三つある。

第一に、共通式を helper structure に分離する案である。たとえば概念的には

```lean
structure SquareGoldenCoordinates where
  M : ℤ
  N : ℤ
  delta : ℤ
```

を用意し、provenance だけを inductive にする。この場合 packet 間で座標 field の再利用性が上がる。

第二に、orientation を明示的な tag にして一 constructor 化する案である。ただし sign と base selection の dependent な対応を表現する必要があるため、現在の二 constructor より Lean code が必ず短くなるとは限らない。

第三に、constructor の等式方向を逆向きにする、あるいは `let`/helper definition で座標を生成する API と比較する余地がある。現在の方向 `M = ...` は `rw` や `subst` に使いやすいので、変更には downstream proof の実測比較が必要である。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用しているが、本宣言単独では高度な Mathlib theorem や tactic を使っていない。

必要なのは概ね、自然数・整数・coercion・基本環演算・冪と `inductive` 宣言を処理できる Lean/Mathlib の基礎部分だけである。したがって `import Mathlib` はこの宣言単体には大きすぎる。

ただし実ファイル `SignedSquareGoldenExceptional.lean` には直前の `ring`、`push_cast`、`Nat.cast_sub` 等を使う theorem と後続の packet 構築が含まれるため、ファイル単位の最小 import は本宣言だけからは確定できない。Lean build は今回行っていないので、具体的な最小 import 集合は候補に留める。

## Comparator challenge 化の可否

適している。

比較課題としては次が面白い。

- 二 constructor の明示的 provenance 型
- sign/orientation tag を用いた一 constructor 型
- 座標 structure と provenance を分離した設計
- `M,N,delta` を外部 field として保持する設計と、source から計算する設計

評価軸は、後続 `SignedSquareGoldenExceptionalPacket` の構築コード、`cases` 後の rewrite 数、cast の量、定理名・field 名から数学的意味がどれだけ読めるか、である。

本宣言は証明探索 challenge というより、proof-oriented data modeling の Comparator challenge に向いている。

## 既存資料との対応

形式的根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` generated section である。

既存の日本語・英語 PDF の具体的ページ・節位置は今回 GitHub コネクタから確定できなかった。そのため PDF 上の対応位置を推測で補ってはいない。

## 次に読むべき定理

依存順で直後に読むべき宣言は

```lean
structure SignedSquareGoldenExceptionalPacket
    (u v w : ℕ) : Type where
  powerSplit : SignedFiveAdicPowerSplit u v w
  M : ℤ
  N : ℤ
  delta : ℤ
  source : SignedSquareGoldenSource u v w M N delta
  golden_eq : GoldenNorm M N = 5 * (powerSplit.b : ℤ) ^ 5
  tenth_boundary : M - 2 * N = (5 : ℤ) ^ 8 * (powerSplit.a : ℤ) ^ 10
  square_discriminant : M ^ 2 - 4 * N ^ 2 = delta ^ 2
  discriminant_five_eq :
    (2 * M + N) ^ 2 - 5 * N ^ 2 = 20 * (powerSplit.b : ℤ) ^ 5
```

である。

0110 が「どの orientation から座標が来たか」を記録したのに対し、次宣言はその provenance と四本の square/golden invariant を一つの exceptional packet に束ねる。ここで signed exceptional route の主要データ構造が完成する。