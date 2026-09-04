# 0130 — `instance : Neg GoldenInt`

## Lean の型

```lean
instance : Neg GoldenInt := ⟨goldenNeg⟩
```

これは theorem ではなく、`GoldenInt` に Lean / Mathlib 標準の単項否定型クラス `Neg` を与える匿名 instance である。0122 で定義済みの raw operation

```lean
def goldenNeg (x : GoldenInt) : GoldenInt :=
  ⟨-x.fst, -x.snd⟩
```

を標準記法 `-x` へ接続する。

## 数学的主張

`GoldenInt` を $x=a+b\varphi$ と読むと、

$$
-x=(-a)+(-b)\varphi
$$

である。本 instance により、この座標ごとの加法逆元が Lean 標準の `-x` として使えるようになる。新しい代数恒等式を証明する宣言ではなく、`goldenNeg` と標準否定記法を definitional に接続する interface である。

## 証明全体での役割

0121–0125 で raw arithmetic を定義し、0127 以降で `Zero`、`One`、`Add` などの標準型クラスへ接続している。本宣言はその加法逆元部分を担当する。

```text
0122 goldenNeg
      ↓
0130 Neg GoldenInt
      ↓
標準記法 -x
      ↓
AddCommGroup / CommRing GoldenInt
```

後続の加法群・環構造では専用名 `goldenNeg` を毎回使わず、通常の環記法で証明を記述できるようになる。

## 直接依存する定義・補題

直接依存は次の三点である。

1. `GoldenInt`
2. `goldenNeg`
3. Lean / Mathlib の `Neg` 型クラス

`GoldenInt.ext`、`goldenAdd`、`goldenMul` などには直接依存しない。

## 証明・定義の流れ

本宣言に tactic proof はない。

```lean
instance : Neg GoldenInt := ⟨goldenNeg⟩
```

期待型 `Neg GoldenInt` から Lean が constructor の field 型 `GoldenInt → GoldenInt` を推論し、`goldenNeg` を実装として登録する。以後 `x : GoldenInt` に対して `-x` と書けば、この instance を通じて `goldenNeg x` が使われる。

## Lean 固有の処理

主な点は typeclass resolution、constructor elaboration、definitional equality の三つである。

`-x` は `Neg GoldenInt` instance の探索を通じて解釈される。右辺 `⟨goldenNeg⟩` は期待型から constructor が推論される。また raw 定義をそのまま登録しているため、標準記法と raw operation の間に別の変換 theorem を挟む必要がない。

この設計では、後続の座標補題は典型的には

```lean
(-x).fst = -x.fst
(-x).snd = -x.snd
```

を `rfl` で閉じられる。具体的な後続 theorem 名は現行 source を最終根拠とする。

## 冗長・重複箇所

`goldenNeg x` と `-x` は機能的には重複している。しかしこれは raw coordinate API と標準 algebra API を分離する意図的な二層構造である。

raw 定義を先に置けば、型クラス構造が完成する前でも `goldenSub` などを組み立てられる。後から標準 instance を登録すれば Mathlib の additive group / ring API に接続できる。したがって削除対象というより architecture-level redundancy と見るのが適切である。

## 最適化候補

候補は三つある。

1. `Neg GoldenInt` に `fun x => ⟨-x.fst, -x.snd⟩` を直接 inline し、`goldenNeg` を削除する。
2. `Add`、`Neg`、`Sub` を個別登録せず、早い段階で `AddCommGroup GoldenInt` を bundle する。
3. carrier を `ℤ × ℤ` に寄せ、既存の coordinatewise negation instance を再利用する。

ただし 1 は bootstrap の見通し、2 は依存関係の監査性、3 は `GoldenInt` という意味付き carrier の明瞭さを損なう。現行方式は段階的構築を読むにはかなり良い。

## 必要な Mathlib import と import 最適化候補

standalone source は

```lean
import Mathlib
```

を使用している。本宣言単独で概念上必要なのは `GoldenInt`、`goldenNeg`、`Neg`、`ℤ` の否定だけであり、`Mathlib` 全体が本 instance のために必要とは考えにくい。

ただし最小 import 集合は今回 Lean build を行っていないため未検証である。最適化するなら、元の modular `GoldenOrder.lean` を分離した状態で import を漸減して確認するのが安全である。

## Comparator challenge 化

適性は高い。

比較候補は、現行の「raw 定義→instance 登録」、instance への直接 inline、既存 product carrier の再利用の三方式である。比較軸は definitional equality、`rfl` / `simp` の量、bootstrap dependency、後続 `AddCommGroup` / `CommRing` 構築の容易さ、可読性・監査性である。

一行宣言ながら、抽象化量と proof cost の比較には良い小規模 challenge になる。

## PDF との対応について

対象ブランチには日本語 PDF `docs/pdf/FLT5-main-ja-v0-r1.pdf` と英語 PDF `docs/pdf/FLT5-main-en-v0-r1.pdf` が存在する。ただし今回の connector 経由では、この匿名 `Neg GoldenInt` instance に対応する本文ページ・節まで直接照合できなかった。そのため PDF 固有のページ番号や叙述は推測していない。

形式的内容の最終根拠は `Flt5DkMath/FLT5StandAlone.lean` 内の `GoldenOrder.lean` generated section である。

## 次に読むべき宣言

現行 source で直後に続くのは

```lean
instance : Sub GoldenInt := ⟨goldenSub⟩
```

である。0123 で定義済みの `goldenSub` を Lean 標準の `x - y` へ接続する宣言であり、0129 `Add` と今回の 0130 `Neg` に続く自然な依存順である。
