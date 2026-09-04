# 0031 — `BranchBFifthPowerNormalForm`

## Lean の型

```lean
structure BranchBFifthPowerNormalForm
    (x y z a b : ℕ) : Prop where
  pack : CounterexamplePack x y z
  branchB : ¬ 5 ∣ z - y
  gap_eq : z - y = a ^ 5
  GN_eq : GN5 (a ^ 5) y = b ^ 5
  x_eq : x = a * b
  z_eq : z = y + a ^ 5
  a_pos : 0 < a
  b_pos : 0 < b
  coprime_a_y : Nat.Coprime a y
  coprime_a_b : Nat.Coprime a b
  coprime_b_y : Nat.Coprime b y
  five_not_dvd_a : ¬ 5 ∣ a
```

`BranchBFifthPowerNormalForm x y z a b` は、Branch B に属する FLT5 反例候補を、第五冪因子の根 `a`、`b` と、それらが満たす正値性・互いに素性・例外素数排除まで含めて一つの `Prop` 構造体へ束ねる。

## 数学的主張

この構造体の inhabitant は、次のデータを同時に証明する。

$$
x^5+y^5=z^5,\qquad 5\nmid z-y
$$

に加え、

$$
z-y=a^5,\qquad GN5(a^5,y)=b^5,\qquad x=ab,\qquad z=y+a^5
$$

さらに、

$$
a>0,\qquad b>0,\qquad \gcd(a,y)=\gcd(a,b)=\gcd(b,y)=1,\qquad 5\nmid a
$$

である。

ここで `pack` が正値な原始反例候補を保持し、残りのフィールドが Branch B の第五冪分離後に必要となる標準形を固定する。

## 証明全体での役割

本宣言は新しい定理を証明するものではなく、後続証明が受け取る **receiver interface** である。Reduction 層で個別に得られた事実を、square/golden bridge 以降が安定して利用できる単一パケットへまとめる。

特に、後続コードは元の因数分解を毎回再構成せず、`normal.gap_eq`、`normal.GN_eq`、`normal.coprime_a_b` などの射影を直接利用できる。これにより、Branch B の初等整数論的縮約と、黄金整数・平方世界側の議論との境界が明確になる。

## 直接依存する定義・補題

確認できる直接依存は次のとおりである。

- `CounterexamplePack`：`pack` フィールドの型。
- `GN5`：`GN_eq` が完全第五冪として固定する残余核。
- `Nat.Coprime`：三組の互いに素性を表す。
- 自然数の冪、減算、整除、正値性。

宣言自体は構造体なので、前号 `coprime_GN5_y_of_coprime` を証明本体として呼び出さない。ただし、その結果は直後の provider `exists_branchB_fifthPowerNormalForm` が `coprime_b_y` を構成する際に使われる。この意味で前号は本構造体を満たすための依存である。

## 構成の流れ

構造体は事実を四層に分けている。

1. 入力層：`pack` と `branchB` が元の反例候補と分岐条件を保持する。
2. 第五冪標準形層：`gap_eq` と `GN_eq` が二因子を第五冪へ射影する。
3. 再構成層：`x_eq` と `z_eq` が元の座標を `a,b,y` から復元する。
4. 非退化・原始性層：正値性、三つの互いに素性、`5 ∤ a` を保持する。

この配列は、元データ、標準形、座標復元、算術的不変量という依存方向に沿っている。

## Lean 固有の処理

`structure ... : Prop` であるため、これは計算用データではなく証明パケットであり、proof irrelevance の対象となる。各フィールドは名前付き射影として自動生成される。

`gap_eq` の右辺を `a ^ 5` とし、`GN_eq` を `GN5 (a ^ 5) y` としている点が重要である。`GN5 (z-y) y` のまま保持せず、既に `gap_eq` で正規化された座標へ揃えるため、後続の rewrite が減る。

一方、`pack` と `branchB` から理論上再導出可能なフィールドも保持している。これは最小性よりも後続 API の使いやすさを優先した設計である。

## 冗長・重複箇所

- `z_eq` は `gap_eq` と `pack` から、`y ≤ z` を経て再導出できる。
- `five_not_dvd_a` は `branchB` と `gap_eq` から再導出できる。
- `a_pos`、`b_pos` も `pack`、`gap_eq`、`x_eq` から再導出可能である。
- `coprime_a_b`、`coprime_b_y` は先行の factor split と合同議論から得られるが、後続で頻繁に使うためキャッシュされている。

したがって論理的には冗長だが、証明工学上は意図的な正規形キャッシュと読める。

## 最適化候補

1. 変更せず receiver interface として維持する案が最も安全である。
2. 最小核 `BranchBFifthPowerCore` と派生事実を持つ拡張構造体へ二層化する案がある。ただし射影経路が増え、後続証明を複雑化する可能性がある。
3. `x_eq` と `z_eq` を simp lemma として登録する案があるが、広域 rewrite の暴走を避けるため局所的な `[simp]` 監査が必要である。
4. `a_pos`、`b_pos` を `PNat` 的な型で表す設計も考えられるが、現行の自然数 API との変換コストが増える。

以上は設計提案であり、現ソースで検証済みの変更ではない。

## 必要 Mathlib import と import 最適化候補

確認できた standalone 生成物は `import Mathlib` を使用している。本構造体宣言だけなら、自然数、整除、冪、`Nat.Coprime` と先行する DkMath 宣言があれば足りる。

実モジュール単位では `Reduction.lean` と必要な Mathlib の自然数整除・gcd 系 import へ縮小できる可能性がある。ただし個別モジュールの import 行は今回参照できた standalone 区間には含まれないため、これは未検証の import 最適化候補である。

## Comparator challenge 化

適性は高い。ただし証明探索問題というより、構造体設計・型同値比較の challenge が向く。

候補課題：

- 同じ数学的内容を持つ最小構造体と現構造体を定義し、相互変換を構成する。
- `gap_eq` を使って `GN5 (z-y) y = b^5` 版と現行版の同値を示す。
- 冗長フィールドを除いた構造体から `z_eq`、`five_not_dvd_a`、正値性を再構成する。

評価点は、rewrite の安定性、依存の少なさ、後続利用時の簡潔さである。

## 根拠と推測の区別

構造体の宣言、フィールド順、NormalForm 層での役割、直後の provider 名はリポジトリ内 Lean コードで確認した。最小構造体への分割、simp 属性、import 縮小は未検証の提案である。

## 次に読むべき定理

次は、

```lean
theorem exists_branchB_fifthPowerNormalForm
```

を読む。この provider は `CounterexamplePack` と Branch B 条件から `a,b` を構成し、本号の receiver interface の全フィールドを実際に埋める。
