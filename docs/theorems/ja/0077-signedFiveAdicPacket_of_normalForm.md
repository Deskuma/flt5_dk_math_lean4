# 0077 — `signedFiveAdicPacket_of_normalForm`

## Lean の型

```lean
noncomputable def signedFiveAdicPacket_of_normalForm
    {u v w : ℕ} (hNF : SignedBranchANormalForm u v w) :
    SignedFiveAdicPacket u v w :=
  Classical.choice (nonempty_signedFiveAdicPacket_of_normalForm hNF)
```

この宣言は theorem ではなく `noncomputable def` である。0076 が証明した

```lean
Nonempty (SignedFiveAdicPacket u v w)
```

から `Classical.choice` を使い、後段が直接参照できる `SignedFiveAdicPacket u v w` を一つ選び出す。

## 数学的主張

数学的に新しい算術命題を追加する宣言ではない。0076 が既に保証した「five-adic packet が少なくとも一つ存在する」という存在命題から、ひとつの packet を選択する。

選ばれた packet は 0075 の仕様により、ある `carrier`, `residual`, `distinguished` について

$$
carrier\cdot residual=distinguished^5,
$$

$$
residual\equiv5\pmod{25},
$$

$$
v_5(residual)=1,
$$

$$
v_5(carrier)=4+5m
$$

などの情報を保持する。ただし本宣言自身は、どの inhabitant が選ばれるかを計算的に指定しない。

## 証明全体での役割

0076 までは packet の存在が `Nonempty` の内部に包まれていた。後段の refuter や power-split 構成では、存在命題を毎回分解するよりも、実際の `SignedFiveAdicPacket` を引数として渡せる方が API として扱いやすい。

本宣言はその境界を埋める canonical-choice adapter である。直後の

```lean
abbrev SignedFiveAdicCore : Prop :=
  ∀ {u v w : ℕ}, SignedFiveAdicPacket u v w → False
```

および

```lean
theorem signedBranchARefuter_of_fiveAdicCore
    (hCore : SignedFiveAdicCore) :
    SignedBranchARefuter := by
  intro u v w hNF
  exact hCore (signedFiveAdicPacket_of_normalForm hNF)
```

では、この chosen packet が normal form と contradiction core を直結する。

## 直接依存する定義・補題

直接依存は非常に少ない。

- `SignedBranchANormalForm`
- `SignedFiveAdicPacket`
- `nonempty_signedFiveAdicPacket_of_normalForm`
- `Classical.choice`

数学的な mod 25 計算や `padicValNat` の補題には本宣言から直接は触れない。それらは 0076 の存在証明の内部に既に封じ込められている。

## 証明の流れ

流れは一段だけである。

1. `hNF : SignedBranchANormalForm u v w` を 0076 に渡す。
2. `nonempty_signedFiveAdicPacket_of_normalForm hNF` から `Nonempty (SignedFiveAdicPacket u v w)` を得る。
3. `Classical.choice` で inhabitant を一つ取り出す。

したがって proof term の本体は

```lean
Classical.choice (nonempty_signedFiveAdicPacket_of_normalForm hNF)
```

そのものに等しい。

## Lean 固有の処理

最重要点は `noncomputable` と `Classical.choice` である。

`SignedFiveAdicPacket u v w` の inhabitant の存在は証明されているが、その witness を計算手続きとして公開してはいない。Lean では classical choice により存在証明から値を抽出できるが、その定義は一般には executable な計算内容を持たないため `noncomputable def` になる。

また `Nonempty α` は `Exists` と異なり、値そのものをデータとして通常計算に使うための構造ではない。本宣言は `Nonempty` から actual term へ移る典型的な bridge である。

## 冗長・重複箇所

本宣言自体に実質的な重複はない。むしろ 0076 の長い constructor proof を後段から隠蔽するための薄い wrapper である。

ただし「canonical」というコメントは数学的な一意性を意味しない点に注意が必要である。`Classical.choice` が選ぶ inhabitant は一意であることを証明していない。ここでの canonical は API 上の固定された代表、という意味に読むのが安全である。

## 最適化候補

候補は二つある。

第一に、0076 の証明を `Nonempty` ではなく直接

```lean
SignedBranchANormalForm u v w → SignedFiveAdicPacket u v w
```

を返す constructive constructor に書き換えられるなら、本宣言と `Classical.choice` を不要にできる可能性がある。実際、0076 は両 orientation で具体的な record literal を構成しているため、設計上は直接値を返す形へ寄せられる余地がある。

第二に、現行の「存在 theorem + chosen def」を維持する場合でも、この二段構成は specification と selection を分離するという利点がある。最適化は単なる行数削減だけでなく、constructive API を重視するか proof abstraction を重視するかで判断すべきである。

いずれも Lean ビルド未実施の設計案である。

## 必要 Mathlib import と import 最適化候補

対象 standalone artifact は `import Mathlib` を使用している。本宣言から見える外部依存は `Classical.choice` のみで、five-adic 算術自体は直接使わない。

したがって本宣言単独なら非常に小さな import で足りる可能性が高い。ただし `SignedBranchANormalForm` と `SignedFiveAdicPacket` の定義側依存を含める必要があるため、正確な最小 import は元モジュールの import graph を確認しない限り断定できない。

最適化候補としては、`SignedFiveAdic.lean` の実 import を確認し、`Classical` とローカル定義群だけでこの wrapper が成立するかを分離検証するのがよい。

## 既存 PDF との関係

今回の最終根拠はリポジトリ内の Lean source である。この `noncomputable def` に一対一対応する既存日本語・英語 PDF の具体的ページは今回特定できていないため、PDF 固有の説明やページ番号は推測で補っていない。

## Comparator challenge 化の可否

**適している。** 数学証明そのものではなく API 設計比較として有効である。

比較案は、

- 現行の `Nonempty` theorem + `Classical.choice` def
- 直接 packet を返す constructive constructor

の二方式である。

評価軸は、classical dependency の有無、後段 proof の簡潔さ、definition unfolding の透明性、extraction 可能性、constructor proof の再利用性である。

## 次に読むべき宣言

次は

```lean
abbrev SignedFiveAdicCore : Prop :=
  ∀ {u v w : ℕ}, SignedFiveAdicPacket u v w → False
```

である。

0077 が normal form から実際の packet を一つ取り出せるようにし、次号は「任意の exact five-adic packet から矛盾を返す」という receiver contract を一行の命題として定義する。ここから packet construction 側と contradiction 側が明確に分離される。