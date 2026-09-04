# 0237 — `SignedGoldenRamifierStrippedCore`

## Lean の型

```lean
/-- Receiver contract for contradictions stated after the visible ramifier is removed. -/
abbrev SignedGoldenRamifierStrippedCore : Prop :=
  ∀ {u v w : ℕ}, SignedGoldenRamifierStrippedPacket u v w → False
```

これは `theorem` ではなく `abbrev` である。可視な ramifier `tau` を一度取り除いた `SignedGoldenRamifierStrippedPacket` を受け取れば必ず `False` を返す、という downstream contradiction contract に短い名前を与える。

## 数学的主張・宣言の意味

`SignedGoldenRamifierStrippedCore` は概念的には

$$
\forall u,v,w,\quad
\mathrm{SignedGoldenRamifierStrippedPacket}(u,v,w)
\Longrightarrow \bot
$$

という命題である。

0231–0236 で構築された stripped packet は、概念的に

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

といった「可視 ramifier を除去した後の正規化状態」を保持する。本 `abbrev` は、その状態まで到達したなら contradiction を導ける、という残りの数学を一つの受け口にまとめる。

したがって新しい数論を証明しているのではなく、証明 pipeline の残余 obligation を命題型として切り出している。

## 証明全体での役割

0236 までで

$$
\mathrm{SignedBranchANormalForm}
\longrightarrow
\mathrm{SignedGoldenRamifierStrippedPacket}
$$

という直接経路が完成した。0237 はその直後に置かれ、stripped packet を refuter へ渡すための抽象 contract を定義する。

正本 source の直後では、

```lean
theorem signedBranchARefuter_of_goldenRamifierStrippedCore
    (hCore : SignedGoldenRamifierStrippedCore) : SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

と、本 core を `SignedBranchARefuter` へ持ち上げる theorem が続く。さらにその refuter から Branch-B の routed counterexample まで閉じる theorem へ接続される。

つまり 0237 は、ramifier-stripped 層の局所 contradiction と、FLT5 signed Branch-A / Branch-B 全体の closure を分離する境界である。

## 直接依存する定義・補題

直接依存する型は次の二つである。

- 0231 `SignedGoldenRamifierStrippedPacket`
- Lean の `False`

量化変数として `u v w : ℕ` を使う。

proof script は存在せず、既存 theorem への直接依存もない。概念的には

$$
\texttt{SignedGoldenRamifierStrippedPacket}
\longrightarrow
\texttt{False}
$$

という関数型を全 `u,v,w` に対して要求するだけである。

ただし downstream では 0236 `signedGoldenRamifierStrippedPacket_of_normalForm` と直接組み合わされる。

## 構築の流れ

構築は型別名の定義だけである。

```lean
abbrev SignedGoldenRamifierStrippedCore : Prop :=
  ∀ {u v w : ℕ}, SignedGoldenRamifierStrippedPacket u v w → False
```

1. 任意の自然数 `u v w` を暗黙引数として受け取る。
2. 対応する `SignedGoldenRamifierStrippedPacket u v w` を受け取る。
3. `False` を返すことを要求する。

証明内容そのものはこの宣言には含まれない。後続の theorem が、この contract を満たす仮定 `hCore` を利用して高位 refuter を構成する。

## Lean 固有の処理

`abbrev` は透明な別名であり、新しい opaque な定義境界を作らない。そのため `SignedGoldenRamifierStrippedCore` は必要に応じて

```lean
∀ {u v w : ℕ}, SignedGoldenRamifierStrippedPacket u v w → False
```

へ軽く展開できる。

また codomain が `False` である関数型は Lean では「その入力 packet は存在しえない」という refuter と同値の使い方をする。つまり

```lean
hCore p : False
```

という形で packet `p` をそのまま contradiction に送れる。

`u v w` が implicit binder `{u v w : ℕ}` になっているため、downstream は packet の型から index を推論でき、通常は明示的に渡す必要がない。

## 冗長・重複箇所

数学的には、この名前を付けずに各 theorem で

```lean
(∀ {u v w : ℕ}, SignedGoldenRamifierStrippedPacket u v w → False)
```

と直接書くこともできる。

しかし専用名を置く利点は大きい。

- proof pipeline の「残りの核心」が theorem 型として可視化される。
- signed Branch-A refuter への adapter が短くなる。
- downstream の unit/fifth-power exclusion と stripped-core の同値を独立 API として述べやすい。
- packet の内部 field が増減しても consumer 側の contract 名を維持できる。

したがって論理的には薄い alias だが、proof architecture の境界として有用である。

## 最適化候補

1. **現行 `abbrev` を維持する**
   - 最も軽量で、contract 名だけを追加できる。

2. **`def` にする**
   - 明示的な定義境界を作れるが、この単純な proposition alias では透明性を失う利点が小さい。

3. **generic refuter alias を導入する**
   - `PacketRefuter P := P → False` のような一般化は可能だが、FLT5 固有の意味が theorem 名から薄れる。

4. **`¬ Nonempty (...)` 型へ再表現する**
   - 各 index ごとの packet 不在として書けるが、現在の `p ↦ False` 形式の方が downstream の関数合成には自然である。

現行設計は facade / contract としてほぼ最小であり、局所的な最適化余地は小さい。

## 必要 Mathlib import と import 最適化候補

standalone artifact は `import Mathlib` を使用している。本宣言自体が直接要求する Mathlib 表面は極めて小さい。

- `Nat`
- `Prop`
- `False`
- dependent universal quantification

実際の import 負荷は `SignedGoldenRamifierStrippedPacket` の上流定義に支配される。本 `abbrev` 単独のために高度な tactic や number-theory module は不要である。

今回は Lean build を行わないため、`SignedGoldenRamifierStripped.lean` 全体の厳密な最小 import 集合は未検証であり、import 最適化候補としてのみ記録する。

## Comparator challenge 化の可否

適している。ただし theorem proving ではなく contract / API 設計の比較課題である。

比較候補は次の通り。

- A: 現行 `abbrev` contract
- B: explicit function type を各 theorem に直接記述
- C: generic `PacketRefuter` abstraction
- D: `¬ Nonempty` / no-packet formulation

比較軸は、proof term の短さ、型の読みやすさ、downstream adapter の単純さ、refactor 耐性、definition unfolding の扱いやすさである。

## PDF・Lean source との対応

形式的正本は `docs/flt5-theorem-museum-v2` ブランチの `Flt5DkMath/FLT5StandAlone.lean` に埋め込まれた `DkMath/FLT/Five/SignedGoldenRamifierStripped.lean` generated section である。

正本 source では 0236 `signedGoldenRamifierStrippedPacket_of_normalForm` の直後に本 `abbrev` があり、その直後に `signedBranchARefuter_of_goldenRamifierStrippedCore` が続くことを確認した。

対象ブランチの日英 0236 文書は双方ともこの source 順を同じように記録している。対象ブランチには日本語・英語 PDF も存在すると正本文書に記録されているが、本 `abbrev` に対応する具体的 PDF ページ・節番号は今回特定していないため推測しない。

## 次に読むべき宣言

依存順の次は **0238 `signedBranchARefuter_of_goldenRamifierStrippedCore`** である。

```lean
/-- A refuter for all stripped packets closes both signed orientations. -/
theorem signedBranchARefuter_of_goldenRamifierStrippedCore
    (hCore : SignedGoldenRamifierStrippedCore) : SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedGoldenRamifierStrippedPacket_of_normalForm hNF)
```

0237 が stripped packet から `False` への contract を定義したので、0238 は normal form から 0236 の bridge で stripped packet を作り、その packet を `hCore` に渡して `SignedBranchARefuter` へ昇格させる adapter になる。
