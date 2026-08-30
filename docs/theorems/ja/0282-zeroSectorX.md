# 0282 — `zeroSectorX`

## 宣言種別

これは **`def`** である。

theorem ではなく、zero-sector inversion で用いる新しい整数座標を導入する定義である。`gamma = (r,s)` の二座標から、対角方向の一次結合

$$
X=2r+s
$$

を取り出す。

## Lean の型

```lean
/-- The diagonal coordinate `X = 2*r+s`. -/
def zeroSectorX (r s : ℤ) : ℤ :=
  2 * r + s
```

したがって Lean 上の完全な型は

```lean
zeroSectorX : ℤ → ℤ → ℤ
```

である。

## 数学的意味

入力を `r,s : ℤ` とすると、

$$
\operatorname{zeroSectorX}(r,s)=2r+s
$$

である。

この定義そのものは新しい定理を主張しない。重要なのは、直前まで `GoldenInt` の座標 `r,s` と quartic factor を直接操作していた zero-sector 算術から、以後の inversion で使用する座標系へ表現を切り替える点にある。

`SignedGoldenZeroSectorInversion.lean` 冒頭では、この `X` に続いて

$$
U=X^2+5s^2,
\qquad
W=4d^5
$$

が定義される。Lean 正本では実際に

```lean
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2


def zeroSectorW (d : ℕ) : ℤ :=
  4 * (d : ℤ) ^ 5
```

と続く。したがって `zeroSectorX` は単独の略記ではなく、inversion layer 全体の最初の座標変換である。

## 証明全体での役割

0281 `SignedGoldenRamifierStrippedPacket.zeroSector_tenthPower_split` までで、zero sector の第二座標と fifth-power quartic factor は

$$
|s|=5^6c^{10},
\qquad
|H(r,s)|=d^{10}
$$

という tenth-power normal form へ整理された。

0282 からは、その因数分解情報を直接追う段階から、`r,s` の多項式関係を inversion 用の二次形式へ再配置する段階へ移る。

その入口が

$$
X=2r+s
$$

である。この変数を導入すると次の `zeroSectorU` は

$$
U=(2r+s)^2+5s^2
$$

となる。展開すれば

$$
U=4r^2+4rs+6s^2
$$

であり、元の座標を対角化に近い形でまとめるための基礎量となる。

ここで「対角座標」という呼称は Lean source の docstring `The diagonal coordinate` に基づく。これ以上の幾何学的・線形代数的な意味づけは、この `def` 単独からは確定しないため、本稿では推測として追加しない。

## 直接依存する定義・補題

### 整数型 `ℤ`

入力・出力はいずれも整数である。自然数絶対値へ移した直前の factorization 層と異なり、inversion 座標では符号を保持するため再び `ℤ` を使う。

### 整数の乗法と加法

定義本体は

```lean
2 * r + s
```

だけであり、他の DkMath 独自定義や theorem には依存しない。

### 0281 との関係

Lean の定義依存として 0281 を参照しているわけではない。しかし証明全体の依存順では、0281 が zero-sector arithmetic を完了し、その次の source module `SignedGoldenZeroSectorInversion.lean` の最初の宣言として本定義が現れる。

つまり **コード上の直接依存はほぼ無いが、証明設計上の前段は 0281** である。

## 定義・構築の流れ

### 1. `r,s` を整数座標として受け取る

```lean
(r s : ℤ)
```

ここでは `GoldenInt` 自体を引数にせず、その二つの整数座標だけを受け取る。

### 2. 対角座標を一次結合として定義する

```lean
2 * r + s
```

補題、場合分け、型変換、証明 tactic は一切必要ない。

### 3. 後続定義が `zeroSectorX` を名前付き部品として再利用する

直後の

```lean
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

が `zeroSectorX` を直接呼び出す。このため、後続の theorem では `(2*r+s)^2` を毎回展開するのではなく、`X` を一つの inversion coordinate として扱える。

## Lean 固有の処理

この宣言には proof term は無く、`def` の右辺がそのまま定義内容である。

したがって

```lean
zeroSectorX r s
```

は必要に応じて定義展開され、

```lean
2 * r + s
```

へ reduction できる。等式

```lean
zeroSectorX r s = 2 * r + s
```

は定義的等価性により `rfl` で示せる。

後続証明では `[zeroSectorX]` を simplifier や `unfold zeroSectorX` に与えて展開することができる。もっとも、名前を導入した目的は式の構造を保つことなので、常時展開するより必要な局面だけ unfold する方が読みやすい。

## 冗長・重複箇所

定義本体には冗長性はほぼ無い。

候補としては、単に `2 * r + s` を後続式へ直接埋め込めば `zeroSectorX` 自体を消せる。しかしそうすると

```lean
zeroSectorX r s ^ 2 + 5 * s ^ 2
```

という構造化された `U` が

```lean
(2 * r + s) ^ 2 + 5 * s ^ 2
```

へ戻り、inversion の座標名 `X,U,W,...` の対応が失われる。

したがってコード量だけを基準にしたインライン化は可能だが、証明設計と文書可読性の観点では現在の独立 `def` の方が適切である。

## 最適化候補

### `abbrev` 化

定義を透明な略記としてしか使わないなら `abbrev zeroSectorX` にする選択肢は理論上ある。しかし後続 API で名前付き定義として rewrite/unfold の境界を保持したい場合、通常の `def` の方が制御しやすい。

現状の source だけから `abbrev` 化が有利とは判断できない。

### 専用 unfolding lemma

たとえば

```lean
@[simp] theorem zeroSectorX_eq (r s : ℤ) :
    zeroSectorX r s = 2 * r + s := rfl
```

を追加することもできる。しかし定義本体が一行であり、`simp [zeroSectorX]` で十分なので、現段階では重複 API になりやすい。

### 構造体化

inversion で `X,U,W,A,B` を常に一組として運ぶのであれば、将来的には座標をまとめた structure を作る設計もあり得る。ただし `zeroSectorX` の時点では後続使用状況を全て検証していないため、これは設計候補に留まり、現コードへの具体的改善提案とはしない。

## 必要 Mathlib import と import 最適化候補

対象 repository の standalone 正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用しており、生成 manifest 上では本宣言が `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` に属することを確認できる。

本 `def` 単独が必要とする機能は整数 `ℤ`、整数リテラル、乗法、加法だけなので、`import Mathlib` はこの宣言だけを見る限り大幅に広い。しかし元 source module 自体の正確な import 行は standalone artifact では保存されておらず、今回は Lean build も行わないため、`Mathlib.Data.Int.Basic` など特定の最小 import へ安全に縮約できるかは **未確認** である。

したがって import 最適化候補は「`SignedGoldenZeroSectorInversion.lean` 全体の実使用 declaration を調べた上で `Mathlib` umbrella import を個別 import へ縮小する」であり、この 0282 だけを根拠に具体的 import を断定しない。

## Comparator challenge 化の可否

**単独 challenge としては優先度が低い。**

理由は、定義そのものについて

```lean
example (r s : ℤ) : zeroSectorX r s = 2 * r + s := by
  rfl
```

とするだけなら、Comparator が比較する proof engineering の余地がほとんど無いからである。

一方、後続の `zeroSectorU` や factorization identity と組み合わせ、`X=2r+s` を使うと複雑な quartic relation がどの程度短くなるかを比較する challenge なら価値がある。その場合の題材は 0282 単独ではなく、inversion section の恒等式 theorem を選ぶべきである。

## PDF との対応

対象 branch には既存の日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在することを確認した。

ただし今回 GitHub コネクタから PDF binary 本文を解析可能な形では取得できず、0282 に対応するページ番号・節番号・本文表現は確認できなかった。そのため PDF の具体的記述を推測して本稿へ混ぜていない。

本稿で確定的に述べた Lean 上の内容は、対象 branch の `Flt5DkMath/FLT5StandAlone.lean` に含まれる generated source `DkMath/FLT/Five/SignedGoldenZeroSectorInversion.lean` を正本としている。

## 次に読むべき宣言

次は **0283 `zeroSectorU`** である。種別は `def`。

```lean
/-- The positive quadratic quantity `U = X^2+5*s^2`. -/
def zeroSectorU (r s : ℤ) : ℤ :=
  zeroSectorX r s ^ 2 + 5 * s ^ 2
```

0282 で導入した

$$
X=2r+s
$$

を初めて直接使用して、

$$
U=X^2+5s^2
$$

という inversion の二次量を構成する。したがって依存順では 0282 → 0283 が明確な直接依存になっている。
