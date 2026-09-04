# 0143 — `golden_fst_mul`

## Lean の型

```lean
@[simp] theorem golden_fst_mul (x y : GoldenInt) :
    (x * y).fst = x.fst * y.fst + x.snd * y.snd := rfl
```

これは `GoldenInt` 上の標準乗法 `x * y` の第一座標 `fst` を、整数座標による明示式へ還元する `@[simp]` theorem である。

## 数学的主張・宣言の意味

`GoldenInt` の元を

$$
x=a+b\varphi,\qquad y=c+d\varphi
$$

と書き、生成元が

$$
\varphi^2=\varphi+1
$$

を満たすとする。積を展開すると

$$
(a+b\varphi)(c+d\varphi)=ac+(ad+bc)\varphi+bd\varphi^2
$$

であり、二次関係を用いれば

$$
(a+b\varphi)(c+d\varphi)=(ac+bd)+(ad+bc+bd)\varphi
$$

となる。したがって第一座標、すなわち基底 `1` の係数は

$$
\operatorname{fst}(xy)=ac+bd
$$

である。本 theorem はこれを Lean 上で

```lean
(x * y).fst = x.fst * y.fst + x.snd * y.snd
```

として公開する。

0141–0142 の減算 projection と異なり、ここでは単なる coordinatewise operation ではなく、`goldenMul` に埋め込まれた黄金整数固有の二次関係が座標式に現れる。

## 証明全体での役割

本 theorem は `GoldenInt` の抽象的な標準乗法を整数算術へ落とす乗法 projection API の第一半分である。次の 0144 `golden_snd_mul` と組み合わせることで、黄金整数の積に関する等式を両座標の整数恒等式へ完全に分解できる。

この役割は直後の `goldenCommRing : CommRing GoldenInt` 構築で重要である。source では環法則の各 goal に対して概ね

```lean
intros <;> ext <;>
simp <;> ring
```

という形を使う。`GoldenInt.ext` で座標へ分解した後、`simp` が本 theorem と `golden_snd_mul` を使って `GoldenInt` の乗法を整数多項式へ変換し、最後に `ring` が閉じる。

つまり本 theorem は表示用の補題ではなく、黄金整数を実際に可換環として組み立てる証明の rewrite interface を担っている。

## 直接依存する定義・補題

直接依存は次の通りである。

- `GoldenInt`
- `goldenMul`
- `Mul GoldenInt` instance

上流の raw multiplication は

```lean
def goldenMul (x y : GoldenInt) : GoldenInt :=
  ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

で定義され、`Mul GoldenInt` は

```lean
instance : Mul GoldenInt := ⟨goldenMul⟩
```

として登録される。

したがって本 theorem の右辺は `goldenMul` の第一座標そのものである。数学的背景としては $\varphi^2=\varphi+1$ が必要だが、その還元は theorem の証明時に別補題として呼ばれるのではなく、既に `goldenMul` の定義式へコンパイルされている。

0144 `golden_snd_mul` は対になる projection theorem だが、本 theorem の証明自体は 0144 に依存しない。

## 証明・構築の流れ

証明は

```lean
:= rfl
```

だけで完了する。

Lean が `(x * y).fst` を展開すると、概念的には

```text
x * y
→ goldenMul x y
→ ⟨x.fst * y.fst + x.snd * y.snd,
    x.fst * y.snd + x.snd * y.fst + x.snd * y.snd⟩
```

となる。第一射影 `fst` を取れば

```lean
x.fst * y.fst + x.snd * y.snd
```

がそのまま現れるため、左右は定義的に同一であり `rfl` で閉じる。

重要なのは、二次関係の代数変形をこの theorem 内で再証明していない点である。複雑さは `goldenMul` の定義時に一度だけ処理され、この theorem は標準 notation と座標式の definitional bridge に徹している。

## Lean 固有の処理

`@[simp]` と `rfl` の組み合わせが中心である。

`rfl` が成立するため、標準乗法 notation `x * y` から raw `goldenMul x y`、さらに第一座標式まで完全に definitional に透明である。

`@[simp]` により、後続 goal 中の

```lean
(x * y).fst
```

は自動的に

```lean
x.fst * y.fst + x.snd * y.snd
```

へ正規化される。これにより `GoldenInt` 固有の演算を早い段階で消去し、整数上の `ring` tactic に渡せる。

特に `goldenCommRing` 構築で `ext <;> simp <;> ring` が成立するのは、このような projection simp theorem 群が整備されているためである。

## 冗長・重複箇所

本 theorem の式は `goldenMul` の第一座標定義をそのまま再公開しているため、定義内容としては重複している。また 0144 `golden_snd_mul` と対になって二本の projection theorem を置くことも、二座標 structure に由来する boilerplate である。

しかし raw definition を毎回 unfold する方式では、downstream proof が `goldenMul` の内部実装へ直接依存する。専用 `@[simp]` theorem を置けば、内部表現と後続証明の間に安定した rewrite API を設けられる。

したがってこの重複は、simp の制御性と proof auditability のための意図的な API-level duplication と評価できる。

## 最適化候補

候補は次の通りである。

1. 現行どおり `fst` / `snd` の乗法 projection theorem を個別に維持する。
2. `x * y = ⟨..., ...⟩` という pair-level theorem を一つ作り、二つの projection theorem をそこから導出する。
3. projection theorem を削除し、必要箇所で `simp [goldenMul]` を用いる。
4. 一般の二次関係 $\theta^2=p\theta+q$ に対する generic coordinate multiplication を抽象化し、本式を $p=q=1$ の特殊化として生成する。
5. `AdjoinRoot` や quadratic algebra 系の既存 Mathlib infrastructure に寄せ、座標 API の一部を一般理論へ委譲する。

現行方式の強みは `rfl` と単純な simp normal form を維持できる点である。抽象化によるコード削減は可能だが、`goldenCommRing` のような downstream proof が複雑化するなら、FLT5 証明の監査性との trade-off が発生する。

## 必要 Mathlib import と import 最適化候補

standalone artifact は

```lean
import Mathlib
```

を使用している。

本 theorem 単独では高度な Mathlib theorem を直接利用せず、必要なのは `GoldenInt`、`goldenMul`、`Mul GoldenInt`、整数の加法・乗法と標準 simp machinery である。

ただし `GoldenOrder` モジュール全体では直後に `AddCommGroup`、`CommRing` を構築し、`ring` tactic や二次拡大関連の infrastructure も利用する。そのため実際の最小 import は theorem 単体ではなくモジュール全体の依存で決まる。

今回は Lean build を行わないため、正確な最小 import 集合は未検証である。`Mathlib` umbrella import からの分割は最適化候補として扱う。

## Comparator challenge 化の可否

適している。

比較対象として次の方式を用意できる。

- 現行の dedicated `@[simp]` projection theorem
- `simp [goldenMul]` による raw unfold
- pair-level multiplication theorem からの projection
- generic quadratic-order / `AdjoinRoot` ベース実装

評価軸は、`goldenCommRing` の proof 行数、`rfl` で閉じる補題数、simp normal form の安定性、内部実装変更への耐性、一般化可能性、下流 FLT5 theorem の可読性である。

特に本 theorem は黄金整数固有の二次関係が初めて標準乗法の projection として表面化する箇所なので、専用座標実装と一般二次環実装を比較する良い Comparator challenge になる。

## PDF・Lean source との対応

対象ブランチには日本語 PDF `FLT5-main-ja-v0-r1.pdf` と英語 PDF `FLT5-main-en-v0-r1.pdf` が存在する。

本 theorem の形式的根拠は `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/GoldenOrder.lean` generated section で確認した。同 source では `goldenMul`、`Mul GoldenInt`、本 theorem、0144 `golden_snd_mul`、`goldenCommRing` が同じ局所 API として連続して配置されている。

ただし、この projection theorem に対応する PDF の具体的ページ・節は今回直接特定していない。そのため PDF 上のページ番号や叙述位置は推測しない。

## 次に読むべき宣言

依存順の次は

```lean
@[simp] theorem golden_snd_mul (x y : GoldenInt) :
    (x * y).snd = x.fst * y.snd + x.snd * y.fst + x.snd * y.snd := rfl
```

である。

0143 が積の基底 `1` 成分 $ac+bd$ を公開したのに対し、0144 は $\varphi$ 成分 $ad+bc+bd$ を公開する。二つが揃うことで、黄金整数の乗法が完全に整数座標へ展開され、直後の `CommRing GoldenInt` 構築へ進める。