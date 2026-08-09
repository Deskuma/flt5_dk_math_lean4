# 0086 — `SignedFiveAdicPowerSplit.coprime_b5_scaled_a20`

## Lean の型

```lean
theorem SignedFiveAdicPowerSplit.coprime_b5_scaled_a20
    {u v w : ℕ} (s : SignedFiveAdicPowerSplit u v w) :
    Nat.Coprime (s.b ^ 5) (5 ^ 15 * s.a ^ 20) :=
  s.coprime_scaled_a20_b5.symm
```

## 数学的主張

0085 で証明した

$$
\gcd(5^{15}a^{20},b^5)=1
$$

の向きを反転し、

$$
\gcd(b^5,5^{15}a^{20})=1
$$

を得る companion lemma である。

数学的内容は 0085 と同一であり、新しい数論的情報を追加してはいない。互いに素という関係の対称性だけを利用して、後続の theorem が要求する引数順へ型を整えている。

## 証明全体での役割

本定理の役割は arithmetic discovery ではなく API orientation の調整である。

0085 は

$$
5^{15}a^{20}
\quad\text{と}\quad
b^5
$$

の順で coprimality を供給したが、後続の golden-order 側では $b^5$ を第一因子として扱う箇所がある。実際、対象ブランチの standalone source では後段で

```lean
have hab := p.exceptional.powerSplit.coprime_b5_scaled_a20
have habs : Nat.Coprime (p.exceptional.powerSplit.b ^ 5)
    (5 ^ 15 * p.exceptional.powerSplit.a ^ 20) := hab
```

と消費され、そのまま `Nat.eq_one_of_dvd_coprimes` に渡されている。

したがって流れは

$$
\gcd(5^{15}a^{20},b^5)=1
\Longrightarrow
\gcd(b^5,5^{15}a^{20})=1
\Longrightarrow
\text{後続 API の要求する向き}
$$

である。

## 直接依存する定義・補題

- `SignedFiveAdicPowerSplit`
- `SignedFiveAdicPowerSplit.coprime_scaled_a20_b5`（0085）
- `Nat.Coprime.symm`

本定理は `s.five_not_dvd_b`、`s.coprime_a_b`、`Nat.Prime 5`、冪の coprimality 補題を直接は使わない。それらの算術的仕事はすべて 0085 に封じ込められている。

## 証明の流れ

証明は一段だけである。

1. 0085 から

$$
\operatorname{Coprime}(5^{15}a^{20},b^5)
$$

を得る。

2. `Nat.Coprime.symm` により

$$
\operatorname{Coprime}(b^5,5^{15}a^{20})
$$

へ反転する。

Lean コードではこれが

```lean
s.coprime_scaled_a20_b5.symm
```

の一式に圧縮されている。

## Lean 固有の処理

`Nat.Coprime` は二引数を持つ命題であり、数学的には対称でも Lean の型としては

```lean
Nat.Coprime A B
```

と

```lean
Nat.Coprime B A
```

は別の式である。後続 lemma の引数順が後者を要求するなら、前者をそのまま渡すことはできない。

そこで `.symm` が orientation adapter として働く。

```lean
s.coprime_scaled_a20_b5.symm
```

では、Lean が receiver `s.coprime_scaled_a20_b5` の型から $A=5^{15}a^{20}$ と $B=b^5$ を推論し、対称化後の型を目標へ直接一致させる。

このため `by` ブロック、`exact`、中間 `have` は不要である。

## 冗長・重複箇所

数学的には 0085 と完全に重複している。単独で見れば削除して、利用箇所で

```lean
s.coprime_scaled_a20_b5.symm
```

と直接書くこともできる。

しかし source の後段では `coprime_b5_scaled_a20` という向きそのものが意味を持つ形で利用されている。したがって、この一行 theorem は「重複した数学」ではあるが、「重複した API」とは限らない。

特に長い修飾名を後段で何度も反転させるより、用途に沿った companion name を一度与える方が proof script の可読性を保ちやすい。

## 最適化候補

候補は三つある。

1. 現行維持。
   - forward / reverse の両 orientation を明示的な companion theorem として公開する。
2. 本 theorem を削除。
   - 利用箇所で `s.coprime_scaled_a20_b5.symm` を直接使う。
3. 後続 API の orientation を統一。
   - project 全体で coprimality の因子順を統一できるなら companion theorem 自体を減らせる。

この宣言については、後段で実際に名前付き API として利用されているため、現行維持には十分な理由がある。最適化の焦点は proof length ではなく、project 全体の orientation convention が一貫しているかどうかである。

## 必要 Mathlib import と import 最適化候補

対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` で構築されており、manifest 上では本宣言は `DkMath/FLT/Five/SignedFiveAdicPowerSplit.lean` に属する。

この theorem 自身が直接必要とする Mathlib 側機能は `Nat.Coprime.symm` だけであり、0085 よりさらに小さい。したがって theorem 単体だけを見れば `import Mathlib` は明らかに過大である。

ただし実際の分割元 module は `SignedFiveAdicPowerSplit` 本体と前段 theorem 群を同時に必要とするため、最小 import は theorem 単体ではなく module 全体の依存 graph で決めるべきである。本回では分割元 module の import 列を Lean build で検証していないため、最小 import の具体名は断定しない。

## Comparator challenge 化の可否

可能だが、証明探索 challenge としては非常に小さい。むしろ API-design comparator に向く。

比較候補は、

1. 名前付き reverse companion theorem を置く現行方式。
2. 各 call site で `.symm` を直接使う方式。
3. coprimality の orientation convention を project-wide に固定する方式。

評価軸は、行数ではなく、後続 theorem の可読性、検索性、補完候補としての発見しやすさ、refactor 時の安定性である。

## PDF との対応

既存の日英 PDF は叙述的根拠として扱う方針だが、本 theorem は 0085 の純粋な対称化 adapter であり、今回この一行宣言に一対一対応する PDF のページ・節番号は確認できなかった。

GitHub code search も今回 502 upstream error となったため、PDF 内位置を推測で補っていない。形式的な最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` にある実際の Lean 宣言である。

## 次に読むべき定理

次は source 上で直後に置かれた

```lean
private theorem nonempty_signedFiveAdicPowerSplit_of_packet
    {u v w : ℕ} (p : SignedFiveAdicPacket u v w) :
    Nonempty (SignedFiveAdicPowerSplit u v w) := by
  let c := p.carrier / 5
  let r := p.residual / 5
  let d := p.distinguished / 5
  ...
```

を読むべきである。

0083 は power split の record 型を定義し、0084–0086 はその record が持つ後続向け性質を整えた。次の private theorem は、いよいよ `SignedFiveAdicPacket` から `SignedFiveAdicPowerSplit` の実データを構成する存在証明である。

すなわち流れは

$$
\mathrm{SignedFiveAdicPacket}
\Longrightarrow
\mathrm{Nonempty}(\mathrm{SignedFiveAdicPowerSplit})
$$

へ進み、構造定義から constructor 層へ移る。