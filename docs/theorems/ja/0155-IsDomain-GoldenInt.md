# 0155 — `instance : IsDomain GoldenInt`

## Lean の型

```lean
instance : IsDomain GoldenInt := NoZeroDivisors.to_isDomain _
```

これは theorem ではなく、`GoldenInt` に Mathlib 標準の型クラス `IsDomain` を登録する匿名 `instance` である。

## 数学的主張・宣言の意味

この宣言は、ここまで構築した `GoldenInt` が整域として扱えることを Mathlib の algebra hierarchy に登録する。

直前までに `GoldenInt` には可換環構造 `CommRing GoldenInt`、零因子がないことを表す `NoZeroDivisors GoldenInt`、さらに `0 ≠ 1` を保証する `Nontrivial GoldenInt` が与えられている。

したがって数学的には、

$$
xy=0 \Longrightarrow x=0 \lor y=0
$$

かつ

$$
0 \neq 1
$$

を備えた可換環として、`GoldenInt` を整域の標準インターフェースへ接続する段階である。

## 証明全体での役割

0148–0152 では doubled embedding を `Zsqrtd 5` 側へ送り、そこで零因子排除を借りて `GoldenInt` に戻すという具体的な証明を行った。0153 ではその結果を `NoZeroDivisors GoldenInt` として登録し、0154 では `Nontrivial GoldenInt` を供給した。

0155 は、それらを新たに証明し直すのではなく、Mathlib が用意する

```lean
NoZeroDivisors.to_isDomain
```

によって標準 `IsDomain` instance にまとめる。

概念的な流れは

$$
\texttt{CommRing GoldenInt}
+\texttt{NoZeroDivisors GoldenInt}
+\texttt{Nontrivial GoldenInt}
\longrightarrow
\texttt{IsDomain GoldenInt}
$$

である。

この時点から下流の証明は、黄金整数専用の零積補題だけでなく、Mathlib の整域一般の補題・型クラス推論を利用できるようになる。

## 直接依存する定義・補題

直接依存する主要要素は次の通りである。

- `GoldenInt`
- `goldenCommRing : CommRing GoldenInt`
- 0153 `NoZeroDivisors GoldenInt`
- 0154 `Nontrivial GoldenInt`
- Mathlib の `NoZeroDivisors.to_isDomain`

Lean の term 自体は

```lean
NoZeroDivisors.to_isDomain _
```

だけであり、明示的に名前を参照するのは変換 constructor 側だけである。ただし `_` の型推論と typeclass search によって、既に登録された `GoldenInt` 上の algebra instance 群が解決される。

## 証明・構築の流れ

証明 script は存在しない。一行の instance 定義である。

```lean
instance : IsDomain GoldenInt := NoZeroDivisors.to_isDomain _
```

Lean は期待型 `IsDomain GoldenInt` を見て `_` を `GoldenInt` と推論し、現在の typeclass environment から必要な `CommRing`、`NoZeroDivisors`、`Nontrivial` などを探索する。

したがって、この宣言は数学的な新規証明というより、既に証明済みの性質を標準 hierarchy に昇格させる interface registration である。

## Lean 固有の処理

ここで重要なのは typeclass inference である。

`NoZeroDivisors.to_isDomain _` は、対象型を明示的に `GoldenInt` と書かなくても、左辺の期待型

```lean
IsDomain GoldenInt
```

から対象型を推論できる。

さらに、`IsDomain` の構築に必要な前提は、0153・0154 までに既に instance として登録済みなので、ユーザー側で proof term を再配線する必要がない。

この設計により、以後の theorem は `GoldenInt` が整域であることを typeclass search に任せられる。専用 theorem を毎回引数として渡す必要がなくなる点が Lean らしい境界である。

## 冗長・重複箇所

数学的には 0152 の theorem、0153 の `NoZeroDivisors` instance、0154 の `Nontrivial` instance、0155 の `IsDomain` instance が近接しており、同じ「整域性」の話を複数段階に分けている。

しかしこれは単なる重複ではなく、

- 0152: 再利用可能な named theorem
- 0153: 零因子なしの標準 typeclass
- 0154: 非自明性の標準 typeclass
- 0155: 整域 hierarchy への統合

という異なる API 層を明示している。

一つの巨大な `IsDomain` instance に全証明を埋め込むこともできるが、現在の分離の方が各段階の責務と依存関係を監査しやすい。

## 最適化候補

候補は次の通りである。

1. 現行のまま `NoZeroDivisors.to_isDomain _` を使う。
2. 対象型を `NoZeroDivisors.to_isDomain GoldenInt` のように明示して可読性を上げる。
3. 0152–0155 を一つの局所 section にまとめ、零因子排除から `IsDomain` までの構造昇格を視覚的に近づける。
4. もし Mathlib の hierarchy 変更でより直接的な constructor が推奨されるなら、それへ更新する。

現行コードは最短であり、Mathlib が既に提供する標準変換を素直に利用しているため、無理な短縮余地は小さい。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本宣言そのものが必要とするのは `IsDomain`、`NoZeroDivisors` とその変換 `NoZeroDivisors.to_isDomain`、および上流で構築済みの `CommRing` / `Nontrivial` instance である。

したがって 0155 単独のために `Mathlib` 全体が必要とは考えにくい。実際の最小 import は `GoldenOrder` 全体で利用する環構造と tactic 群に支配される。

今回は Lean build を行わないため、正確な最小 import 集合は未検証である。この点は import 最適化候補としての推測である。

## Comparator challenge 化の可否

可能だが、対象は数学アルゴリズムではなく instance 設計の比較になる。

比較候補は、

- `NoZeroDivisors.to_isDomain _` による標準昇格
- `IsDomain` を直接 structure literal で構築
- より上位の既存 algebra structure から自動導出

などである。

比較軸は、コード量、依存 instance の透明性、Mathlib hierarchy 変更への耐性、エラーメッセージの分かりやすさ、downstream theorem での typeclass resolution の安定性となる。

このケースでは標準 constructor を使う現行方式が最も自然であり、Comparator challenge としては「標準 hierarchy を再実装しない価値」を確認する題材になる。

## PDF・Lean source との対応

形式的根拠は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `GoldenOrder` 部分である。source 上では 0154 `Nontrivial GoldenInt` の直後に本 `IsDomain GoldenInt` instance が置かれ、その次に raw operation と標準記法の一致を公開する `golden_add_eq` が続く。

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。ただし本 instance に対応する具体的 PDF ページ・節は今回直接特定していないため、推測しない。

## 次に読むべき宣言

依存順の次は

```lean
@[simp] theorem golden_add_eq (x y : GoldenInt) :
    goldenAdd x y = x + y := rfl
```

である。

0155 までで `GoldenInt` の整域 structure が標準 hierarchy に登録された。次からは raw operation `goldenAdd` と標準 notation `x + y` が定義的に一致することを `@[simp]` theorem として公開する API 整理段階へ進む。