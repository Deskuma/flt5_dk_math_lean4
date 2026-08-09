# 0083 — `SignedFiveAdicPowerSplit`

## Lean の型

```lean
structure SignedFiveAdicPowerSplit
    (u v w : ℕ) : Type where
  fiveAdic : SignedFiveAdicPacket u v w
  a : ℕ
  b : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_b : Nat.Coprime a b
  carrier_eq : fiveAdic.carrier = 5 ^ 4 * a ^ 5
  residual_eq : fiveAdic.residual = 5 * b ^ 5
  distinguished_eq : fiveAdic.distinguished = 5 * a * b
```

これは theorem ではなく、five-adic packet の情報をさらに正確な第五冪分解へ持ち上げた `structure ... : Type` である。依存順では 0082 `signedFiveAdicPacket_gcd_eq_five` の直後に置かれ、後続定理は本 structure の各 field を直接使用するため、ここを一宣言として解説する必要がある。

## 数学的主張

`SignedFiveAdicPacket u v w` に含まれる carrier、residual、distinguished が、正の互いに素な自然数 $a,b$ を用いて

$$
carrier=5^4a^5,
$$

$$
residual=5b^5,
$$

$$
distinguished=5ab
$$

という形に分解されることを保持するデータ型である。

さらに

$$
a>0,\qquad b>0,\qquad \gcd(a,b)=1
$$

を field として保持する。

前号で確定した

$$
\gcd(carrier,residual)=5
$$

を「共通因子 $5$ を一個だけ持つ」という情報として使い、その共通因子を剥がした後の部分を互いに素な第五冪へ整理した normal form が本 structure の数学的意味である。

## 証明全体での役割

`SignedFiveAdicPacket` は mod $25$、$5$-進付値、carrier/residual の因数積などを保持する five-adic 層の共通 packet だった。本 structure はその packet を、後段の代数的整数・黄金比二次形式へ渡せる「第五冪の形」に変換する中間 API である。

特に後続では

- `five_not_dvd_b` により $5\nmid b$ を得る。
- `coprime_scaled_a20_b5` により $5^{15}a^{20}$ と $b^5$ の互いに素性を得る。
- `nonempty_signedFiveAdicPowerSplit_of_packet` が任意の five-adic packet から本 structure の inhabitant を構成する。
- さらに `signedFiveAdicPowerSplit_of_packet` / `signedFiveAdicPowerSplit_of_normalForm` が chosen split を後段へ供給する。

したがって本 structure は five-adic 情報から exact power split へ移る境界である。

## 直接依存する定義・補題

宣言そのものの直接依存は非常に薄い。

- `SignedFiveAdicPacket u v w`
- `Nat.Coprime`
- 自然数の冪 `(^)` と積

数学的には直前の `signedFiveAdicPacket_gcd_eq_five` が本 structure の inhabitant を構成するための主要入力になるが、structure 定義そのものはその theorem を field に持たない。これは「仕様」と「構築証明」を分離した設計である。

## 証明・構成の流れ

structure 自体には proof script はない。代わりに field が exact split の仕様を段階的に固定する。

1. `fiveAdic` で元の `SignedFiveAdicPacket` を保持する。
2. `a`, `b` を第五冪部分の基底として保存する。
3. `a_pos`, `b_pos` で退化した零解を排除する。
4. `coprime_a_b` で共通因子を $5$ 以外へ持ち越していないことを保証する。
5. `carrier_eq` で carrier の five-adic load がちょうど $5^4$ で、その残部が第五冪であることを固定する。
6. `residual_eq` で residual の five-adic load がちょうど $5$ で、その残部が第五冪であることを固定する。
7. `distinguished_eq` で積の右辺の第五冪基底が $5ab$ に一致することを固定する。

この三等式は packet の

$$
carrier\cdot residual=distinguished^5
$$

と整合しており、左辺は

$$
(5^4a^5)(5b^5)=5^5a^5b^5=(5ab)^5
$$

となる。

## Lean 固有の処理

`structure ... : Type` なので、これは命題ではなくデータを伴う型である。後続では `s.carrier_eq`、`s.residual_eq` のように projection として直接利用できる。

`fiveAdic : SignedFiveAdicPacket u v w` を丸ごと保持しているため、後段は exact split だけでなく元 packet の `residual_mod_twentyFive` や `source` などにも戻れる。この設計は情報を捨てずに refinement layer を重ねる方式である。

`a_pos`, `b_pos`, `coprime_a_b` も derived theorem にせず field として持つため、後段は構築過程を再生せず即座に使える。

## 冗長・重複箇所

本 structure には意図的な冗長性がある。三つの exact equality のうち、`carrier_eq` と `residual_eq`、さらに元 packet の `factor_eq` があれば、正値条件の下で `distinguished_eq` は第五冪の injectivity を使って再導出できる。

また `coprime_a_b` も構築時には 0082 の gcd 情報から導かれるため、理論上は derived theorem にできる。

しかし後続証明がこれらを頻繁に利用するなら、field として保持することは proof cache として合理的である。現時点では「冗長だから削除すべき」とは断定できない。

## 最適化候補

第一候補は core/derived の二層化である。例えば core structure には `fiveAdic`, `a`, `b`, `carrier_eq`, `residual_eq` だけを保持し、positivity、coprimality、`distinguished_eq` を projection theorem として導出する設計が考えられる。

第二候補は逆に、現在の fat record を維持しつつ constructor helper を一本にまとめること。後続の `nonempty_signedFiveAdicPowerSplit_of_packet` が証明した facts を一箇所で record 化すれば、利用側 API は最も単純になる。

第三候補は five-adic exponent を定数 `4` と `1` に固定した専用型ではなく、一般の ramified prime $p$ と exponent split をパラメータ化する案である。ただし FLT5 専用証明では抽象化コストが大きく、現段階では Comparator 用の設計案に留めるのが妥当である。

## 必要 Mathlib import と import 最適化候補

対象ブランチの生成 standalone は `import Mathlib` を使用している。本 structure 単体が必要とする Mathlib 機能は、自然数、冪、積、`Nat.Coprime` 程度である。

したがって宣言単体なら import はかなり縮小できる可能性が高い。一方、実際の分割元 `SignedFiveAdicPowerSplit.lean` には直前・直後で gcd、divisibility、`omega`、`ring`、`ZMod` などが使われるため、ファイル単位の最小 import は structure 単体より広い。正確な最小集合は Lean ビルドを行っていないため未検証である。

## 既存 PDF との関係

数学的には、five-adic exceptional factor $5$ を carrier/residual から正確に分配した後、残部を互いに素な第五冪へ分解する段階に対応する。

リポジトリ内 Lean source が型と field の一次根拠である。既存の日本語・英語 PDF で本 structure と一対一対応するページ番号・定理番号は今回確定できなかったため、PDF 固有の番号や引用は推測で補っていない。

## Comparator challenge 化の可否

適している。ただし theorem proving challenge より API 設計 challenge としての価値が高い。

比較候補は、

- 現行の fat record
- 最小 core + derived projection theorem
- carrier/residual の split を別 structure に分け、distinguished を後から復元する設計
- 一般 prime/exponent split へ抽象化した設計

である。

評価軸は、後続証明の短さ、field の再利用回数、構築時の複雑さ、内部表現への依存度、エラー局所性である。

## 次に読むべき定理

次は直後の

```lean
theorem SignedFiveAdicPowerSplit.five_not_dvd_b
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) : ¬ 5 ∣ s.b := by
  ...
```

を読むべきである。

`residual_eq : residual = 5*b^5` と元 packet の

$$
residual\bmod25=5
$$

を組み合わせ、もし $5\mid b$ なら $25\mid residual$ となる矛盾を導く。power split の基底 $b$ に five-adic factor が残っていないことを最初に確定する定理である。