# 0099 — `goldenNorm_eq_fifth_power_of_GN5`

## Lean の型

```lean
theorem goldenNorm_eq_fifth_power_of_GN5
    {g y b : ℕ} (hGN : GN5 g y = b ^ 5) :
    GoldenNorm
        (↑((g + y) ^ 2 + y ^ 2) : ℤ)
        (↑((g + y) * y) : ℤ) =
      (b : ℤ) ^ 5 := by
  calc
    GoldenNorm
        (↑((g + y) ^ 2 + y ^ 2) : ℤ)
        (↑((g + y) * y) : ℤ) =
        (GN5 g y : ℤ) := (GN5_eq_goldenNorm_squareLink g y).symm
    _ = ((b ^ 5 : ℕ) : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) hGN
    _ = (b : ℤ) ^ 5 := by norm_num
```

## 数学的主張

自然数 `g y b` が

$$
\mathrm{GN5}(g,y)=b^5
$$

を満たすなら、endpoint-square 座標

$$
M=(g+y)^2+y^2,\qquad N=(g+y)y
$$

に対して

$$
\mathrm{GoldenNorm}(M,N)=b^5
$$

が整数上で成り立つ。

0096 `GN5_eq_goldenNorm_squareLink` が既に

$$
\mathrm{GN5}(g,y)=\mathrm{GoldenNorm}(M,N)
$$

を与えているので、本 theorem の数学的内容は「自然数上で得た fifth-power 等式を、同じ値を表す黄金ノルムへ輸送する」ことにある。

## 証明全体での役割

`SquareGoldenBridge.lean` 区間の締めの theorem である。

0093 で `GoldenNorm` を導入し、0094–0096 で `GN5` と endpoint-square 座標を黄金ノルムへ接続し、0097–0098 で判別式 $5$ と完全平方境界を露出した。本 theorem はその橋に fifth-power 情報を載せる。

したがって proof graph は

$$
\mathrm{GN5}(g,y)=b^5
\Longrightarrow
\mathrm{GoldenNorm}(M,N)=b^5
$$

となる。後続 `SquareGoldenNormalForm.lean` は、この黄金ノルムの fifth-power 情報と square-world の境界情報を同じ named coordinates にまとめる段階へ進む。

## 直接依存する定義・補題

project-local な直接依存は次の通り。

1. `GN5` — 自然数上の五次円分因子。
2. `GoldenNorm` — 整数上の二次形式 $m^2+mn-n^2$。
3. `GN5_eq_goldenNorm_squareLink` — `GN5` と endpoint-square 座標上の `GoldenNorm` の同一視。

Lean 標準・Mathlib 側では、等式へ関数を作用させる `congrArg`、自然数から整数への coercion、冪の cast 正規化を閉じる `norm_num` を利用する。

## 証明の流れ

証明は三段の `calc` である。

第一段では 0096 を逆向きに使う。

```lean
(GN5_eq_goldenNorm_squareLink g y).symm
```

これにより黄金ノルムを `(GN5 g y : ℤ)` へ戻す。

第二段では仮定

```lean
hGN : GN5 g y = b ^ 5
```

の両辺へ自然数から整数への埋め込みを作用させる。

```lean
congrArg (fun n : ℕ => (n : ℤ)) hGN
```

したがって

$$
(\mathrm{GN5}(g,y):\mathbb Z)=((b^5:\mathbb N):\mathbb Z)
$$

を得る。

第三段で

$$
((b^5:\mathbb N):\mathbb Z)=(b:\mathbb Z)^5
$$

という cast と冪の可換性を `norm_num` で正規化して閉じる。

## Lean 固有の処理

本 theorem の本質的な Lean 処理は、数学的には同じ整数値を表す `ℕ` と `ℤ` の世界を明示的に横断する点にある。

`hGN` は `ℕ` 上の等式なので、そのままでは `GoldenNorm : ℤ → ℤ → ℤ` の等式へ接続できない。そこで `congrArg` に coercion 関数を渡して、等式全体を `ℤ` へ持ち上げている。

また 0096 は

$$
(\mathrm{GN5}(g,y):\mathbb Z)=\mathrm{GoldenNorm}(M,N)
$$

の向きなので、本 theorem の `calc` の始点に合わせて `.symm` を使う。

最後の `norm_num` は新しい数論を証明しているのではなく、`Nat.cast_pow` に相当する coercion 正規化を自動処理している。

## 冗長・重複箇所

数学的には 0096 と `hGN` の推移律だけで内容はほぼ尽きている。三段目の cast 正規化は Lean の型境界に由来する実装上の段差である。

また、同種の「自然数上の等式を整数へ cast して project-local bridge に接続する」パターンが今後繰り返されるなら、局所 helper を作る余地がある。

一方、現行の三段 `calc` は、

1. 構造変換、
2. 仮定の輸送、
3. coercion 正規化、

を一行ずつ分離しており、監査性は高い。短縮しすぎない価値がある。

## 最適化候補

1. 現状維持。proof graph が最も読みやすい。
2. `exact_mod_cast hGN` や `norm_cast` 系 tactic を試し、第二・第三段をまとめる。ただし tactic の挙動が見えにくくなる可能性がある。
3. `rw [← GN5_eq_goldenNorm_squareLink g y]` 型の証明へ短縮する。ただし cast の方向と正規化が一か所に集中するため、説明性は下がる。
4. 自然数等式を整数へ持ち上げる汎用 helper を導入する。類似箇所が複数ある場合にのみ有力。
5. endpoint-square 座標を後続の `SquareGoldenM` / `SquareGoldenN` へ早期に統一し、長い座標式の反復を減らす。これは module 境界を跨ぐ設計変更になる。

## 必要 Mathlib import と import 最適化候補

対象 standalone artifact は `import Mathlib` を使用している。本 theorem が直接必要とする機能は、整数 coercion、冪、`congrArg`、および `norm_num` tactic である。project-local には `GN5`、`GoldenNorm`、`GN5_eq_goldenNorm_squareLink` が必要である。

単独 theorem の観点では umbrella `Mathlib` は過大である可能性が高く、`Mathlib.Tactic.NormNum` と整数・自然数 coercion の基礎 import を中心に縮小できる余地がある。ただし分割元 `SquareGoldenBridge.lean` 全体には `ring` や `push_cast` を使う先行 theorem が含まれるため、module 全体の最小 import 集合は Lean build を行わずには断定しない。

## Comparator challenge 化の可否

適している。難度は基礎から中級寄りで、特に cast 処理の比較教材として価値がある。

比較候補は次の通り。

1. 現行の明示的 `calc + congrArg + norm_num`。
2. `norm_cast` / `exact_mod_cast` を利用する短縮版。
3. 0096 を `rw` してから `hGN` を利用する rewrite 中心版。
4. cast helper lemma を先に用意する構造化版。

評価軸は、証明行数だけでなく、`ℕ → ℤ` の型境界が読者に見えるか、依存 theorem の役割が追えるか、tactic 依存が過剰でないか、とするのがよい。

## 既存資料との対応

形式的な最終根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` である。generated source marker により、本 theorem は `DkMath/FLT/Five/SquareGoldenBridge.lean` の最後の theorem で、その直後に `SquareGoldenNormalForm.lean` が始まることを確認できる。

既存の日英 PDF については、今回 GitHub code search が upstream 502 を返し、公開 Web 検索でも対象 repository の対応 PDF を一意に特定できなかった。そのため具体的なページ・節番号は推測で補っていない。

## 次に読むべき定理

依存順で次の宣言は、新 module `SquareGoldenNormalForm.lean` の最初の定義

```lean
def SquareGoldenM (z y : ℕ) : ℤ :=
  (z : ℤ) ^ 2 + (y : ℤ) ^ 2
```

である。その次に

```lean
def SquareGoldenN (z y : ℕ) : ℤ :=
  (z : ℤ) * (y : ℤ)
```

が続く。

博物館が定義も依存順に扱う方針を維持するなら、次号は `SquareGoldenM` が自然である。もし theorem のみに限定するなら、二つの座標定義の直後にある `squareGolden_tenth_boundary_base` が次の theorem となる。