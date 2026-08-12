# 0111 — `SignedSquareGoldenExceptionalPacket`

## Lean の型

```lean
/--
The exceptional square-golden packet common to both signed five-adic sources.
The single residual five-layer becomes a golden norm `5*b^5`, while the
carrier becomes the tenth-power square boundary `5^8*a^10`.
-/
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

`SignedSquareGoldenExceptionalPacket u v w` は命題 `Prop` ではなく、具体的な witness とその証明を保持する `Type` である。

## 数学的主張

この structure は、signed five-adic power split から得られる square-golden 座標を一つの共通形式にまとめる。

整数座標を

$$
M,N,\delta\in\mathbb Z
$$

とし、`powerSplit` が与える自然数 witness を $a,b$ と書けば、packet は次の四本の不変量を同時に保持する。

$$
\operatorname{GoldenNorm}(M,N)=5b^5,
$$

$$
M-2N=5^8a^{10},
$$

$$
M^2-4N^2=\delta^2,
$$

$$
(2M+N)^2-5N^2=20b^5.
$$

さらに `source` field が、0110 `SignedSquareGoldenSource` によって $(M,N,\delta)$ が difference orientation と sum orientation のどちらから来たかを保存する。

したがってこの packet は、二つの signed 分岐を消してしまうのではなく、**共通 invariant と分岐由来情報を同じオブジェクトに束ねる** ための proof interface である。

## 証明全体での役割

この宣言は `SignedSquareGoldenExceptional.lean` の中心的なデータ境界である。

上流では `SignedFiveAdicPowerSplit` が、exceptional five-adic case における carrier と residual の exact power split を保持している。しかし、そのままでは difference / sum の二 orientation に分かれた自然数算術の形である。

0110 `SignedSquareGoldenSource` が provenance を統一し、本 0111 がそれを `GoldenNorm`、平方境界、square discriminant、判別式 $5$ の四本と合成する。下流の golden-integer 証明は、この packet を受け取ることで元の Fermat 方程式や branch case split を毎回開き直す必要がなくなる。

特に後続 `SignedGoldenRamifierStrippedPacket` は、本 packet を `exceptional` field として保持し、

$$
\alpha=M+N\varphi
$$

に相当する黄金整数座標へ進む。したがって 0111 は、**自然数・five-adic 層から黄金整数層への hand-off object** と見るのが最も正確である。

## 直接依存する定義・補題

直接の型依存は次の三つである。

1. `SignedFiveAdicPowerSplit u v w`
   - exceptional five-adic normal form と exact power witnesses `a`, `b` を保持する。
   - 本 structure の `golden_eq` と `tenth_boundary` の右辺は `powerSplit.a`、`powerSplit.b` を参照する。

2. `SignedSquareGoldenSource u v w M N delta`
   - 0110 で導入された provenance 型。
   - difference / sum のどちらの signed coordinate system から $(M,N,\delta)$ が来たかを保持する。

3. `GoldenNorm M N`
   - square-golden bridge で導入済みの二変数黄金ノルム。
   - 本 packet では exceptional residual の一層の $5$ を明示した $5b^5$ と等置される。

宣言そのものには proof script がないため、0110 の `sumGN5_eq_goldenNorm_signed` や 0109 `signed_endpoint_square_discriminant` は field の型に直接現れない。しかし直後の packet 構築 theorem がそれらを用いて field を埋めるため、実質的な構築依存として重要である。

## 構築の流れ

`structure` 宣言そのものは証明を実行しない。後続の

```lean
private theorem nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    Nonempty (SignedSquareGoldenExceptionalPacket u v w) := by
  ...
```

が実際の constructor proof を担う。

その theorem は `s.fiveAdic.source` を difference / sum に場合分けし、それぞれで $M,N,\delta$ を定め、必要な四本の invariant を構成して最終的に概ね

```lean
exact ⟨{
  powerSplit := s
  M := M
  N := N
  delta := delta
  source := .difference rfl rfl rfl
  golden_eq := hGolden
  tenth_boundary := hBoundary
  square_discriminant := hSquare
  discriminant_five_eq := hDiscFive }⟩
```

または `source := .sum ...` として `Nonempty` witness を返す。

つまり 0111 は constructor の格納形式を定義し、次の theorem が branch-specific arithmetic をこの共通形式へ正規化する。

## Lean 固有の処理

### `Type` を使う理由

`BranchBSquareGoldenNormalForm` のような論理 packet が `Prop` であったのに対し、本宣言は `Type` である。ここでは `M`, `N`, `delta` と `powerSplit` という計算上・構造上意味のある witness を下流で射影して再利用する必要があるためである。

例えば後続では

```lean
p.M
p.N
p.powerSplit.b
```

のように field を直接読む。この用途にはデータを消去する純粋な `Prop` より `Type` の packet が自然である。

### dependent field

`golden_eq` と `tenth_boundary` は先に宣言された `powerSplit` field の内部 witness に依存する。

```lean
golden_eq : GoldenNorm M N = 5 * (powerSplit.b : ℤ) ^ 5
```

のように、structure 内の後続 field が前の field を参照する dependent record になっている。

### `ℕ` から `ℤ` への境界

`u v w` と power witnesses は自然数で保持する一方、$M,N,\delta$ と invariant は整数上で表現される。sum orientation の $N=-uv$ を自然に扱い、自然数減算の truncation を避けるための型境界である。

## 冗長・重複箇所

`discriminant_five_eq` は `golden_eq` と `GoldenNorm` の定義から代数的に導出できる可能性が高い。実際、square-golden 系の前段でも golden norm equality から判別式 $5$ の恒等式を得る wrapper が存在する。

したがって論理的には

```lean
golden_eq
```

だけを保存し、`discriminant_five_eq` を derived theorem にする設計も可能である。

一方、現設計には利点がある。golden arithmetic の下流では判別式 $5$ の式を頻繁に使うため、必要な shape を packet field として materialize しておけば、毎回 `GoldenNorm` を unfold して `ring` する必要がない。これは論理的冗長性と API 上の有用性の意図的な交換である。

また `M`, `N`, `delta` と `source` の組は 0110 の provenance と一体であるため、座標専用 structure にまとめる余地がある。

## 最適化候補

1. `SignedSquareGoldenCoordinates` のような小 structure を導入し、`M`, `N`, `delta`, `source` を一つにまとめる。
2. `discriminant_five_eq` を packet field ではなく `golden_eq` から導く theorem にする版と比較する。
3. difference / sum の構築 theorem で共通する `hSquare`、`hDiscFive` の生成を orientation-independent lemma に押し出す。
4. `powerSplit.a`、`powerSplit.b` を頻繁に使うなら projection alias を用意し、下流の長い field chain を短くする。
5. packet を「最小 core」と「derived API」の二層に分け、kernel 上の仮定量と利用時の便利さを分離する。

ただし現在の flat packet は、proof state で必要な事実が一目で一覧できるため、形式証明の監査性という点ではかなり強い。

## 必要 Mathlib import と import 最適化候補

対象ブランチの generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は先頭で

```lean
import Mathlib
```

を使用している。したがって現 artifact について必要 import は `Mathlib` で満たされる。

一方、この generated artifact は元 module の個別 import 行を保存していないため、`SignedSquareGoldenExceptional.lean` 単体の厳密な最小 Mathlib import 集合はこの資料だけからは確定できない。

本 structure 宣言そのものは tactic を使わず、必要なのは `ℕ`, `ℤ`, 冪、既存の DkMath 型・定義だけである。したがって module 全体の import 最適化を行う場合は、まず DkMath 側の

- `SignedFiveAdicPowerSplit`
- `SquareGoldenBridge` / `GoldenNorm`
- 0110 の signed square-golden bridge

を提供する module import を明示し、その transitive Mathlib dependency を `#print axioms` ではなく実ビルドで削っていくのが安全である。

**推測:** この declaration 単体のために `Mathlib` 全体を直接 import する必要はない可能性が高い。ただし今回は Lean ビルドを行わない指示なので、最小 import の確定までは行っていない。

## Comparator challenge 化の可否

**適している。** 証明 tactic の短さではなく、data-model / API design の比較課題に向く。

比較案として、同じ downstream theorem を次の三設計で成立させられるかを見るとよい。

1. 現在の flat structure。
2. `Coordinates` + `Invariants` の二層 structure。
3. 最小 field のみ保存し、`discriminant_five_eq` を derived theorem にする structure。

評価軸は、constructor proof の長さ、projection の読みやすさ、rewrite の安定性、下流 theorem の行数、import 依存、変更耐性である。

## 資料上の位置づけ

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし今回の GitHub connector では PDF 内の該当ページを直接照合できていないため、ページ番号・節番号は推測で記していない。

形式的な最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` generated section である。

## 次に読むべき定理

次は直後の private theorem

```lean
private theorem nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    Nonempty (SignedSquareGoldenExceptionalPacket u v w) := by
  ...
```

を読むべきである。

0111 が「何を保存するか」を宣言したのに対し、この theorem は difference / sum の二 orientation から実際にその packet を構築する。ここで 0108 `sumGN5_eq_goldenNorm_signed`、0109 `signed_endpoint_square_discriminant`、既存の difference-side square-golden bridge が一つに合流するため、次の依存段階として最も自然である。
