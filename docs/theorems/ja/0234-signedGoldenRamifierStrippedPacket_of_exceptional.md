# 0234 — `signedGoldenRamifierStrippedPacket_of_exceptional`

## Lean の型

```lean
noncomputable def signedGoldenRamifierStrippedPacket_of_exceptional
    {u v w : ℕ} (p : SignedSquareGoldenExceptionalPacket u v w) :
    SignedGoldenRamifierStrippedPacket u v w :=
  Classical.choice
    (nonempty_signedGoldenRamifierStrippedPacket_of_exceptional p)
```

これは `theorem` ではなく `noncomputable def` であり、0233 `nonempty_signedGoldenRamifierStrippedPacket_of_exceptional` が証明した存在から、実際の `SignedGoldenRamifierStrippedPacket u v w` を一つ選び出して downstream から直接使える object として公開する。

## 数学的主張・宣言の意味

0233 では exceptional packet `p` から、ramifier `τ` を一度取り除いた packet が存在すること、すなわち

$$
\exists P:\mathrm{SignedGoldenRamifierStrippedPacket}(u,v,w)
$$

を証明した。

0234 は新しい数学的事実を追加するのではなく、その存在証明から一つの代表元

$$
P=\operatorname{choice}(\text{0233 の存在証明})
$$

を選択する。

選ばれた packet は 0231 の field をすべて保持しているので、特に

$$
\alpha=\tau\beta,
$$

$$
N(\beta)=b^5,
$$

$$
5\nmid N(\beta),
$$

$$
\tau\nmid\beta
$$

を downstream で field projection として利用できる。

## 証明全体での役割

0231–0234 は ramifier stripping block を構成する。

- 0231: stripping 後の packet structure を定義する。
- 0232: `5 ∤ b` の primitive certificate を証明する。
- 0233: exceptional packet から stripped packet が `Nonempty` であることを構成的に証明する。
- 0234: その存在から実際の packet object を一つ選び、後続 API の入口にする。

この宣言により、後続 module は毎回 existential witness を `rcases` する必要がなく、

```lean
let p' := signedGoldenRamifierStrippedPacket_of_exceptional p
```

のように一つの object を参照し、その `beta`、`beta_norm`、`tau_not_dvd_beta` などを直接使える。

したがって 0234 は、存在 theorem を consumer-friendly な data API へ変換する境界である。

## 直接依存する定義・補題

直接依存は極めて小さい。

- 0231 `SignedGoldenRamifierStrippedPacket`
- 0233 `nonempty_signedGoldenRamifierStrippedPacket_of_exceptional`
- `Classical.choice`

数学的な heavy lifting はすべて 0233 で完了しており、本定義自身は factorization、norm、five-adic arithmetic を再計算しない。

概念的には

$$
\texttt{Nonempty P}
\longrightarrow
\texttt{Classical.choice}
\longrightarrow
P
$$

という一段の選択である。

## 構築の流れ

定義本体は一行である。

```lean
Classical.choice
  (nonempty_signedGoldenRamifierStrippedPacket_of_exceptional p)
```

1. 0233 を `p` に適用して `Nonempty (SignedGoldenRamifierStrippedPacket u v w)` を得る。
2. `Classical.choice` にその存在証明を渡す。
3. `SignedGoldenRamifierStrippedPacket u v w` の inhabitant を一つ返す。

ここでは witness の具体式は展開されない。どの packet が選ばれたかは proof irrelevance 的な consumer 視点では重要ではなく、0231 の field を満たす object が得られることだけが必要である。

## Lean 固有の処理

`Classical.choice` は `Nonempty α` から `α` の要素を取り出す classical choice operator である。

このため宣言は `noncomputable def` になっている。Lean の kernel 上では定義として正当だが、実行可能な計算コードとして witness を抽出することは要求していない。

0233 の proof 自体は `k` と `beta` を明示的に構成しているため、数学的には witness がかなり具体的である。それでも 0234 では proof term の内部からデータを直接計算的に取り出す設計ではなく、`Nonempty` と `Classical.choice` の標準境界を採用している。

この分離により、0233 は proposition-valued existence theorem、0234 は data-valued API と役割が明確になる。

## 冗長・重複箇所

最も明確な重複候補は、0233 の `Nonempty` theorem と 0234 の choice 定義の二段構成である。

0233 内部では `k`、`beta`、各 certificate がすべて明示的に構成されているため、理論上は constructor logic を直接

```lean
def signedGoldenRamifierStrippedPacket_of_exceptional ... := { ... }
```

へ移し、別途 `Nonempty` theorem をその object から導く設計も可能である。

ただし現行方式には次の利点がある。

- proof-producing 部分と object-selecting 部分が分離される。
- complicated construction proof を theorem として単独監査できる。
- downstream は `Classical.choice` の詳細を意識せず object を使える。
- 0233 の存在 theorem は choice を必要としない命題として再利用可能である。

したがってコード量としては二層だが、API 設計上は意図的な分離と見なせる。

## 最適化候補

1. **直接 constructor へ統合する**
   - 0233 の explicit witness construction を `def` へ移し、`Nonempty` theorem をそこから導く。

2. **現行の theorem / choice 分離を維持する**
   - proof audit を優先するなら現行方式は明快である。

3. **`Nonempty` ではなく `∃ packet, True` 型を避ける**
   - 現行 `Nonempty` は choice と最も自然に接続しており、この点は既に良い設計である。

4. **downstream が field のみ必要なら accessor theorem を置く**
   - selected packet 自体を公開せず、必要な `beta` や certificate の存在だけを theorem API にする設計も比較できる。

現状では、0233 の長い構築証明を 0234 の一行 choice から分離している可読性の利点が大きい。

## 必要 Mathlib import と import 最適化候補

本定義自身が直接必要とする Mathlib 表面は主に classical choice である。

- `Classical.choice`
- `Nonempty`

その他の黄金整数・five-adic infrastructure は 0233 と 0231 の上流依存である。

したがって宣言単独なら `Mathlib` 全体は不要と考えられる。ただし module 全体では 0233 が `nlinarith`、`omega`、`ring`、`norm_num`、素数整除、cast などを使うため、実際の最小 import は module 単位で検証する必要がある。

今回は Lean build を行わないため、正確な最小 import 集合は未検証である。

## Comparator challenge 化の可否

適している。比較対象は明瞭である。

- A: 現行 `Nonempty` theorem + `Classical.choice`
- B: explicit computable/constructive `def` を直接構成
- C: data object を公開せず existential theorem API のみ利用
- D: structure constructor helper を作り、theorem と def の双方から再利用

比較軸は、proof term の監査性、noncomputable dependency、downstream usability、コード重複、constructor logic の局所性、将来の refactoring 耐性である。

特に A と B は、「存在証明と選択を分離する Lean 設計」と「explicit witness をそのまま data constructor にする設計」の比較としてよい challenge になる。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` generated section である。

0233 の正本文書でも、本 theorem の直後に

```lean
noncomputable def signedGoldenRamifierStrippedPacket_of_exceptional
    {u v w : ℕ} (p : SignedSquareGoldenExceptionalPacket u v w) :
    SignedGoldenRamifierStrippedPacket u v w :=
  Classical.choice
    (nonempty_signedGoldenRamifierStrippedPacket_of_exceptional p)
```

が続くことが確認できる。

対象ブランチには日本語・英語 PDF も存在するが、この一行の choice 定義に対応する具体的ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

次はリポジトリ正本上で 0234 の直後の宣言を再確認して選ぶべきである。

0234 で ramifier-stripped packet が data object として取得可能になったため、次段ではその `beta` と `goldenConj beta` の共通因子を調べる conjugate-coprimality block に入る可能性が高い。ただし宣言名と正確な順序は次回必ず source を読み直して確定する。
