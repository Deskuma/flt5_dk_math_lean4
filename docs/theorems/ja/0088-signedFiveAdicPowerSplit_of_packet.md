# 0088 — `signedFiveAdicPowerSplit_of_packet`

## Lean の型

```lean
noncomputable def signedFiveAdicPowerSplit_of_packet
    {u v w : ℕ} (p : SignedFiveAdicPacket u v w) :
    SignedFiveAdicPowerSplit u v w :=
  Classical.choice (nonempty_signedFiveAdicPowerSplit_of_packet p)
```

本宣言は theorem ではなく `noncomputable def` である。0087 `nonempty_signedFiveAdicPowerSplit_of_packet` が証明した

```lean
Nonempty (SignedFiveAdicPowerSplit u v w)
```

から `Classical.choice` によって一つの witness を選び、以後の証明で直接使える `SignedFiveAdicPowerSplit u v w` を返す。

## 数学的主張

数学的内容は 0087 で既に証明済みである。すなわち signed five-adic packet が与えられれば、ある正の互いに素な自然数 $a,b$ が存在して

$$
\operatorname{carrier}=5^4a^5,
$$

$$
\operatorname{residual}=5b^5,
$$

$$
\operatorname{distinguished}=5ab
$$

と書ける。

本宣言はこの存在主張に新しい算術条件を加えない。存在する power split のうち一つを選択し、名前付きデータとして返すだけである。

したがって数学的には

$$
\exists s:\mathrm{SignedFiveAdicPowerSplit}(u,v,w)
$$

から

$$
s:\mathrm{SignedFiveAdicPowerSplit}(u,v,w)
$$

を選ぶ choice operation に対応する。

## 証明全体での役割

0087 までは packet から exact fifth-power split が存在することを証明しただけであり、その結果は `Nonempty` に包まれている。

後続の定理では毎回

```lean
rcases nonempty_signedFiveAdicPowerSplit_of_packet p with ⟨s⟩
```

と witness を取り出すより、

```lean
let s := signedFiveAdicPowerSplit_of_packet p
```

あるいは単に projection を通して

```lean
(signedFiveAdicPowerSplit_of_packet p).carrier_eq
```

のように利用できた方が API として読みやすい。

本宣言はそのための selection layer である。

概念的な流れは

$$
\mathrm{SignedFiveAdicPacket}
\Longrightarrow
\mathrm{Nonempty}(\mathrm{SignedFiveAdicPowerSplit})
\Longrightarrow
\mathrm{SignedFiveAdicPowerSplit}
$$

であり、前半を 0087 が、後半を本宣言が担う。

これにより、長い gcd stripping・mod 25・fifth-power factor split の構成証明を後続コードから完全に隠蔽できる。

## 直接依存する定義・補題

直接依存は非常に少ない。

- `SignedFiveAdicPacket`
- `SignedFiveAdicPowerSplit`
- `nonempty_signedFiveAdicPowerSplit_of_packet`（0087）
- `Classical.choice`

重要なのは、本宣言自身は

- `signedFiveAdicPacket_gcd_eq_five`
- `fifth_power_factor_split`
- mod $25$ 補題群
- `Nat.Coprime` の power API
- `ring`
- `omega`
- `norm_num`

を直接使わない点である。それらはすべて 0087 の内部へ封じ込められている。

## 証明の流れ

証明は一段だけである。

### 1. 0087 の存在証明を取得する

```lean
nonempty_signedFiveAdicPowerSplit_of_packet p
```

は

```lean
Nonempty (SignedFiveAdicPowerSplit u v w)
```

を返す。

### 2. `Classical.choice` で witness を選ぶ

```lean
Classical.choice (nonempty_signedFiveAdicPowerSplit_of_packet p)
```

により、その `Nonempty` の中から一つの

```lean
SignedFiveAdicPowerSplit u v w
```

を取り出す。

それが定義の返り値となる。

数学的な再計算や case split はない。

## Lean 固有の処理

本宣言の Lean 固有性はほぼ `Classical.choice` に集中している。

`Nonempty α` は「型 `α` に要素が存在する」ことだけを Prop として表すため、そのままでは計算可能な値 `α` を取り出せない。Lean の構成的核では、一般に Prop 内の存在証明から任意のデータを抽出することはできない。

そこで classical choice を使い、存在証明から witness を選ぶ。このため定義には

```lean
noncomputable
```

が必要になる。

重要なのは、この `noncomputable` が数学的証明の弱さを意味しないことである。0087 の existence proof は Lean kernel により検証済みであり、本宣言はその witness に計算規則を要求せず、後続証明で利用するための名前を与えるだけである。

また、`Classical.choice` が返す witness は canonical である必要はない。後続コードは `SignedFiveAdicPowerSplit` の field が満たす命題だけに依存すべきであり、「どの $a,b$ が選ばれたか」という実装依存の選択には依存しない設計になっている。

## 冗長・重複箇所

コード自体は一行であり、局所的な冗長性はほぼない。

ただし API 設計としては、0087 と本宣言が

```lean
private theorem ... : Nonempty T
noncomputable def ... : T := Classical.choice ...
```

という二段構成になっている。

これは存在証明と witness 選択を分離する典型的な形で、監査性は高い。一方、0087 の proof を構成的な `def` として直接 `SignedFiveAdicPowerSplit` を返すよう再編できるなら、本宣言そのものを消せる可能性がある。

ただし 0087 は `fifth_power_factor_split` の existential witness を用いており、現状の証明スタイルでは `Nonempty` と `Classical.choice` の分離は自然である。

## 最適化候補

### 候補 A — 現行の二段構成を維持する

最も保守的で読みやすい案である。

- 0087：存在証明
- 0088：選択 API

と責務が明確に分かれている。

### 候補 B — constructive constructor を直接返す

もし 0087 の内部 witness を term として直接組み立てられるなら、

```lean
def signedFiveAdicPowerSplit_of_packet ... : SignedFiveAdicPowerSplit ... := by
  ...
```

とし `noncomputable` と `Classical.choice` を除ける可能性がある。

ただし proof irrelevance と computation が必要な箇所ではないため、実利は限定的である。

### 候補 C — choice wrapper の一般パターン化

同じ module 群に

```lean
private theorem nonempty_X ... : Nonempty X
noncomputable def X_of_... := Classical.choice ...
```

という形が多数あるなら、命名規則や API 方針を統一する価値がある。ただし helper 自体を一般化しても `Classical.choice` 一行より短くはならないため、抽象化の目的はコード削減ではなく設計統一になる。

## 必要 Mathlib import と import 最適化候補

対象ブランチの generated standalone artifact は `import Mathlib` で構築されている。

本宣言が Mathlib 側から直接必要とする機能は実質的に `Classical.choice` と `Nonempty` の基本 API だけである。したがって本宣言単体に `import Mathlib` 全体は明らかに過大である。

ただし実際の `SignedFiveAdicPowerSplit.lean` は直前の 0087 を含み、自然数 gcd、coprimality、素数、冪、除算、`ring`、`omega`、`norm_num` などを利用する。そのため module 単位の最小 import は本宣言だけを見て決められない。

import 最適化を行うなら、まず分割元 module 全体で使う定理・tactic を列挙し、`Mathlib` umbrella import を段階的に狭め、Lean build で検証する必要がある。本タスクでは build は行わない。

## Comparator challenge 化の可否

可能である。ただし数論の証明探索 challenge ではなく、Lean API 設計の comparator として適している。

比較案は例えば次の三つである。

1. `Nonempty` + `Classical.choice` の現行方式。
2. constructor proof を直接 `def` にして witness を返す方式。
3. existence theorem だけを公開し、各 call site で `rcases` する方式。

評価軸は、

- classical dependency の有無
- API の使いやすさ
- proof term の局所性
- downstream code の簡潔さ
- witness の実装詳細への依存を防げるか

である。

現行方式は downstream の読みやすさと existence proof の監査性のバランスが良い。

## PDF・ソース根拠について

形式的な根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` であり、本宣言が `SignedFiveAdicPowerSplit.lean` 部分に属すること、0087 の直後に配置されることを確認した。

既存の日英 PDF は叙述的な背景資料として扱う。ただし今回 GitHub code search が 502 upstream error となり、本 choice wrapper に一対一対応する PDF の具体的ページ・節番号は確認できなかった。そのため PDF 固有の定理番号・ページ番号・文章は推測で補っていない。

## 次に読むべき定理

source 上で直後に置かれるのは

```lean
noncomputable def signedFiveAdicPowerSplit_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedFiveAdicPowerSplit u v w :=
  signedFiveAdicPowerSplit_of_packet (signedFiveAdicPacket_of_normalForm hNF)
```

である。

次号では

$$
\mathrm{SignedBranchANormalForm}
\Longrightarrow
\mathrm{SignedFiveAdicPacket}
\Longrightarrow
\mathrm{SignedFiveAdicPowerSplit}
$$

という二つの既存 adapter の合成を読む。これにより normal form から exact power split までを一つの公開入口で得られるようになる。