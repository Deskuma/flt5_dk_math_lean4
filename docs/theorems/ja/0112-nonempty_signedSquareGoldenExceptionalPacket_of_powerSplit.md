# 0112 — `nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit`

## Lean の型

```lean
private theorem nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    Nonempty (SignedSquareGoldenExceptionalPacket u v w) := by
  ...
```

この theorem は `private` であり、module 外へ公開する API ではない。目的は、exact five-adic power split `s` から 0111 `SignedSquareGoldenExceptionalPacket` の具体的 witness が存在することを示し、その直後の `Classical.choice` に渡すことである。

## 数学的主張

`SignedFiveAdicPowerSplit u v w` が与えられれば、difference orientation と sum orientation のどちらであっても、整数座標 $M,N,\delta$ を選んで

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
(2M+N)^2-5N^2=20b^5
$$

を同時に満たす `SignedSquareGoldenExceptionalPacket u v w` を構成できる、という存在主張である。ここで $a,b$ は `s.a`, `s.b` である。

重要なのは、二つの signed orientation が異なる座標を用いるにもかかわらず、最終的には同じ四本の invariant shape に正規化される点である。

## 証明全体での役割

0111 は packet の型を宣言しただけだった。本 theorem はその packet が実際に構成可能であることを証明する最初の constructor theorem であり、signed five-adic 層から square-golden 層への実質的な変換器である。

直後には

```lean
noncomputable def signedSquareGoldenExceptionalPacket_of_powerSplit
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    SignedSquareGoldenExceptionalPacket u v w :=
  Classical.choice (nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit s)
```

があり、本 theorem の `Nonempty` witness を `Classical.choice` でデータとして取り出す。したがって本 theorem は、proof-only existence と downstream data API の境界に位置する。

## 直接依存する定義・補題

直接・実質的に使う主な宣言は次のとおりである。

1. `SignedFiveAdicPowerSplit`
   - 入力 `s`。`s.fiveAdic`, `s.a`, `s.b`, `s.carrier_eq`, `s.residual_eq` を使用する。
2. `SignedSquareGoldenExceptionalPacket`
   - 0111 の出力 packet 型。
3. `SignedSquareGoldenSource`
   - constructor `.difference` / `.sum` を provenance field に格納する。
4. `right_lt_of_fermat5Equation`
   - difference 側で $v\le w$ を得るために使う。
5. `GN5_eq_goldenNorm_squareLink`
   - difference 側の `GN5` residual を `GoldenNorm` へ変換する。
6. `sumGN5_eq_goldenNorm_signed`
   - 0108。sum 側の `SumGN5` residual を signed `GoldenNorm` へ変換する。
7. `endpoint_square_discriminant`
   - difference 側の square discriminant。
8. `signed_endpoint_square_discriminant`
   - 0109。sum 側の square discriminant。
9. `four_mul_goldenNorm_eq_discriminant_five`
   - golden norm equality から判別式 $5$ の形を作る。

## 証明の流れ

証明はまず

```lean
let p := s.fiveAdic
cases p.source with
```

として、five-adic provenance を difference / sum の二場合に分ける。

### difference orientation

source が difference のとき、

```lean
let M : ℤ := (w : ℤ) ^ 2 + (v : ℤ) ^ 2
let N : ℤ := (w : ℤ) * (v : ℤ)
let delta : ℤ := (w : ℤ) ^ 2 - (v : ℤ) ^ 2
```

と置く。

`right_lt_of_fermat5Equation` から $v\le w$ を得て、`Nat.sub_add_cancel` により gap coordinate $w-v$ を endpoint coordinate $w$ に戻す。これによって

```lean
GN5_eq_goldenNorm_squareLink (w - v) v
```

を

$$
\operatorname{GoldenNorm}(M,N)=GN5(w-v,v)
$$

へ合わせる。

その後 `p.residual` と `s.residual_eq` を経由して

$$
\operatorname{GoldenNorm}(M,N)=5b^5
$$

を得る。

境界式では source の carrier equality を整数へ cast し、

$$
M-2N=(p.carrier)^2
$$

を示してから `s.carrier_eq` を使い、

$$
(5^4a^5)^2=5^8a^{10}
$$

へ `push_cast` と `ring` で正規化する。

square discriminant は `endpoint_square_discriminant` を直接再利用する。

最後の判別式 $5$ は

$$
(2M+N)^2-5N^2=4\operatorname{GoldenNorm}(M,N)
$$

を `four_mul_goldenNorm_eq_discriminant_five` から得て `hGolden` を代入し、$20b^5$ に整理する。

最終 constructor は

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

である。

### sum orientation

sum 側では

```lean
let M : ℤ := (u : ℤ) ^ 2 + (v : ℤ) ^ 2
let N : ℤ := -((u : ℤ) * (v : ℤ))
let delta : ℤ := (u : ℤ) ^ 2 - (v : ℤ) ^ 2
```

と置く。

黄金ノルムは 0108 `sumGN5_eq_goldenNorm_signed` を `simpa [M, N]` で適用する。carrier boundary は source equality を `rw` した後、`push_cast`, `dsimp`, `ring` で平方に直す。square discriminant は 0109 `signed_endpoint_square_discriminant` をそのまま使う。

判別式 $5$ と最終 packet constructor は difference 側と同型で、provenance だけが

```lean
source := .sum rfl rfl rfl
```

になる。

## Lean 固有の処理

### `Nonempty` と `Classical.choice`

この theorem の conclusion は packet 自体ではなく `Nonempty (...)` である。構築自体は完全に具体的だが、後続 API は `noncomputable def` として `Classical.choice` を使う設計になっている。したがって existence proof と chosen witness を分離している。

### `private theorem`

本 theorem は implementation detail であり、公開側では `signedSquareGoldenExceptionalPacket_of_powerSplit` のみを使わせる構造である。これは downstream proof を constructor の細部から隔離する。

### 自然数減算と cast

difference 側では `w - v` が自然数なので、`Nat.cast_sub` や `Nat.sub_add_cancel` に必要な順序条件 $v\le w$ を明示的に作る。一方 sum 側は整数の負 cross term $N=-uv$ を最初から使うため、自然数減算の truncation 問題を持たない。

### `simpa`, `push_cast`, `ring`

本 proof は、上流 theorem の shape を現在の local definitions に合わせるための `simpa`、自然数から整数への埋め込みを整理する `push_cast`、最後の多項式正規化を行う `ring` という三層が明確に分かれている。

## 冗長・重複箇所

difference / sum の二枝は、座標生成と `hGoldenBase`, `hSquare` 以外の大部分が重複している。特に

- residual から $5b^5$ への変換
- carrier square から $5^8a^{10}$ への変換
- `hDiscFive` の導出
- packet record constructor

はほぼ同型である。

これは provenance ごとの監査性を高める一方、保守時には同じ変更を二枝へ反映する必要がある。

また `discriminant_five_eq` は `golden_eq` から導出しているため、0111 で指摘したとおり packet field としては論理的に冗長である。

## 最適化候補

1. orientation ごとに `(M,N,delta,hGoldenBase,hSquare)` を返す小さな helper を作り、その後の共通処理を一本化する。
2. `hDiscFive` を `golden_eq` から生成する共通 theorem に切り出す。
3. carrier square の正規化
   `((5^4*a^5 : ℕ : ℤ)^2) = 5^8*(a:ℤ)^10`
   を named lemma 化する。
4. `Nonempty` + `Classical.choice` が本当に必要か比較し、直接 packet を返す `noncomputable def` 内で proof を構成する設計と比較する。
5. difference / sum の座標を orientation abstraction で統一し、重複を減らす。ただし現在の branch-local proof は監査しやすいので、短縮だけを目的に抽象化しすぎない方がよい。

## 必要 Mathlib import と import 最適化候補

対象の generated standalone artifact は先頭で

```lean
import Mathlib
```

を使用しているため、現 artifact ではこれで十分である。

本 theorem が実際に使う tactic / 基礎機能には `ring`, `push_cast`, `norm_num`, `Nat.cast_sub`, `Nat.sub_add_cancel` などが含まれる。さらに DkMath 側の five-adic packet、GN5 / SumGN5 bridge、square discriminant、golden norm discriminant bridge が必要である。

元 module の最小 Mathlib import 集合は standalone artifact からは確定できない。したがって `Mathlib` 全体 import をより小さくできる可能性は高いが、今回は Lean ビルドを行わない指示なので最小 import の確定は行わない。

## Comparator challenge 化の可否

**非常に適している。** 同じ packet を構築する複数の proof architecture を比較できる。

比較候補は、

1. 現在の二枝を完全に明示する版。
2. orientation-specific coordinate helper + common constructor 版。
3. `SignedSquareGoldenSource` を eliminator として使う generic normalization 版。
4. `discriminant_five_eq` を保存せず derived theorem にする minimal packet 版。

評価軸として、proof 行数だけでなく、型推論の安定性、cast 処理量、エラー局所性、branch provenance の可読性、upstream definition 変更への耐性を見るべきである。

## 資料上の位置づけ

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし今回の connector では PDF 本文の該当ページを直接照合していないため、ページ番号・節番号は推測で補っていない。

形式的根拠は `Flt5DkMath/FLT5StandAlone.lean` 内の `DkMath/FLT/Five/SignedSquareGoldenExceptional.lean` generated section である。

## 次に読むべき定理

次は直後の

```lean
noncomputable def signedSquareGoldenExceptionalPacket_of_powerSplit
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    SignedSquareGoldenExceptionalPacket u v w :=
  Classical.choice (nonempty_signedSquareGoldenExceptionalPacket_of_powerSplit s)
```

を読むべきである。

本 0112 が `Nonempty` として existence を証明し、次宣言がその witness を公開データへ選択する。proof proposition から reusable packet object への切替点なので、依存順上ここを飛ばすべきではない。