# 0038 — `counterexample_false_of_clean_GN5Channel_by_dvd`

## 1. 宣言

```lean
theorem counterexample_false_of_clean_GN5Channel_by_dvd
    {x y z q : ℕ}
    (hPack : CounterexamplePack x y z)
    (hClean : CleanGN5Channel (z - y) y q) :
    False := by
  have hyz : y ≤ z :=
    Nat.le_of_lt (right_lt_of_fermat5Equation hPack.hx hPack.hEq)
  apply not_fifth_power_body_of_clean hClean
  exact ⟨x, body5_eq_fifth_power_of_fermat hyz hPack.hEq⟩
```

## 2. Lean の型

この定理は自然数 `x y z q` を暗黙引数として受け取る。

- `hPack : CounterexamplePack x y z` は、`x,y,z` が正で、`x` と `y` が互いに素であり、Fermat 方程式 `x^5 + y^5 = z^5` を満たすという反例候補パケットである。
- `hClean : CleanGN5Channel (z - y) y q` は、素数 `q` が gap 座標の `GN5` に一度だけ現れ、gap 自身には現れないという局所 no-lift 証拠である。
- 結論は `False` であり、この二つの入力が同時には成立しないことを述べる。

## 3. 数学的主張

`hPack` から、正の `x` を含む Fermat 方程式

$$
x^5+y^5=z^5
$$

が得られる。したがって `y<z`、特に `y≤z` であり、自然数 gap `z-y` が正しく復元できる。

前号までの bridge により、

$$
Body5(z-y,y)=x^5
$$

である。一方、clean channel `hClean` は、ある素数 `q` が full body

$$
Body5(z-y,y)=(z-y)GN5(z-y,y)
$$

を割るが、その平方 `q^2` は割らないことを保証する。完全第五冪を割る素数は底も割るので、その平方も必ず第五冪を割る。ゆえに、この body は完全第五冪ではあり得ない。

したがって、

$$
Body5(z-y,y)=x^5
$$

と「`Body5(z-y,y)` は第五冪ではない」が衝突し、`False` を得る。

## 4. 証明全体での役割

この定理は `BranchB.lean` における局所 clean-channel 経路の終端である。

前段は二つの独立した流れを準備した。

1. Fermat 方程式側：`body5_eq_fifth_power_of_fermat` が full body を `x^5` と同一視する。
2. 局所整除側：`not_fifth_power_body_of_clean` が clean channel を持つ full body の第五冪性を排除する。

本定理はこの二本を接続する adapter であり、新しい数論を追加せず、既存の存在証拠を否定命題へ渡すだけで反例候補を閉じる。

ただし、これは無条件の Branch B 排除ではない。`CleanGN5Channel (z-y) y q` を供給する仕事は後続の provider interface に残される。最終的な無条件 FLT5 証明は、リポジトリ内コメントによれば signed five-adic normalization と golden descent を通る別経路で進む。

## 5. 直接依存する定義・補題

### 5.1 `CounterexamplePack`

次を保持する構造体である。

- `hPack.hx : 0 < x`
- `hPack.hEq : Fermat5Equation x y z`

本定理で直接使うフィールドはこの二つだけである。

### 5.2 `CleanGN5Channel`

`hClean` は `q` の素数性、`q ∣ GN5 (z-y) y`、`q ∤ z-y`、`q^2 ∤ GN5 (z-y) y` を束ねる。内部フィールドは本定理で直接展開されず、`not_fifth_power_body_of_clean` にまとめて渡される。

### 5.3 `right_lt_of_fermat5Equation`

```lean
right_lt_of_fermat5Equation hPack.hx hPack.hEq : y < z
```

正の `x` と Fermat 方程式から `y<z` を得る。

### 5.4 `body5_eq_fifth_power_of_fermat`

```lean
body5_eq_fifth_power_of_fermat hyz hPack.hEq :
  Body5 (z - y) y = x ^ 5
```

`hyz : y ≤ z` を用いて自然数減算を正しく復元し、body を完全第五冪へ接続する。

### 5.5 `not_fifth_power_body_of_clean`

```lean
not_fifth_power_body_of_clean hClean :
  ¬ ∃ x : ℕ, (z - y) * GN5 (z - y) y = x ^ 5
```

`Body5` は定義上 `(z-y) * GN5 (z-y) y` なので、本定理の `apply` では definitional equality により目標が一致する。

## 6. 証明の流れ

### 6.1 gap の順序条件を作る

```lean
have hyz : y ≤ z :=
  Nat.le_of_lt (right_lt_of_fermat5Equation hPack.hx hPack.hEq)
```

まず `y<z` を証明し、`Nat.le_of_lt` で `y≤z` に弱める。これは `body5_eq_fifth_power_of_fermat` が要求する自然数減算の安全条件である。

### 6.2 非第五冪命題を現在の目標へ適用する

```lean
apply not_fifth_power_body_of_clean hClean
```

`¬ ∃ t, Body = t^5` は Lean では `(∃ t, Body = t^5) → False` である。`apply` によって、目標 `False` は完全第五冪の存在証拠を構成する目標へ変わる。

### 6.3 witness と等式を与える

```lean
exact ⟨x, body5_eq_fifth_power_of_fermat hyz hPack.hEq⟩
```

witness として元の反例候補の `x` を選び、前号の bridge が与える body 等式を添える。これで clean channel の非第五冪性と直接矛盾する。

## 7. Lean 固有の処理

### 7.1 `Nat.le_of_lt`

数学的には `y<z` から `y≤z` は自明だが、Lean では補題の要求する型に合わせて明示的に変換している。

### 7.2 否定は関数

`not_fifth_power_body_of_clean hClean` の型は否定命題であり、Lean では存在証拠を入力して `False` を返す関数として扱われる。`apply` はこの関数適用を逆向きに利用している。

### 7.3 存在証拠の構築

`⟨x, proof⟩` は `∃ x, ...` の constructor 記法である。ここでは witness の探索はなく、Fermat 方程式の左項 `x` をそのまま使う。

### 7.4 definitional equality

`not_fifth_power_body_of_clean` は積 `g * GN5 g y` を直接述べ、`body5_eq_fifth_power_of_fermat` は `Body5 g y` を述べる。`Body5` の定義が透明なので、Lean は両者を定義展開だけで同一視できる。

## 8. 冗長・重複箇所

証明本体は三段だけであり、実質的な冗長性はほとんどない。

ただし `hyz` の生成は、この種の counterexample consumer で繰り返される可能性がある。`CounterexamplePack` から `y≤z` を返す名前付き補題が多数の箇所で必要になるなら、次のような補題を追加する余地がある。

```lean
theorem CounterexamplePack.y_le_z
    {x y z : ℕ} (h : CounterexamplePack x y z) : y ≤ z :=
  (right_lt_of_fermat5Equation h.hx h.hEq).le
```

ただし現時点では一行の導出であり、API を増やす利益は限定的である。

## 9. 最適化候補

### 9.1 `.le` による短縮

現在の

```lean
Nat.le_of_lt (right_lt_of_fermat5Equation hPack.hx hPack.hEq)
```

は、次のようにも書ける。

```lean
(right_lt_of_fermat5Equation hPack.hx hPack.hEq).le
```

既に他モジュールでも使われている形であり、短く読みやすい。

### 9.2 `exact` 一式への圧縮

理論上は否定命題へ直接存在証拠を渡す形に圧縮できる。

```lean
exact (not_fifth_power_body_of_clean hClean)
  ⟨x, body5_eq_fifth_power_of_fermat
    (right_lt_of_fermat5Equation hPack.hx hPack.hEq).le hPack.hEq⟩
```

しかし現在の三段構成の方が、順序条件、非第五冪 consumer、第五冪 witness の役割を明確に分離しており、博物館的にも保守性が高い。

### 9.3 `Body5` 版 consumer

`not_fifth_power_body_of_clean` の結論を `Body5 g y` で表す薄い wrapper を用意すれば definitional equality への依存を表面から除ける。ただし数学的内容は増えず、API 重複になるため、現状のままが妥当である。

以上は最適化提案であり、Lean ビルドによる再検証は本記事作成時には行っていない。

## 10. 必要 Mathlib import と import 最適化候補

生成済み standalone ソースはファイル全体で `import Mathlib` を用いており、本定理がその環境で成立することはリポジトリ内 Lean コードから確認できる。

本定理自体が直接必要とする機能は小さい。

- 自然数の順序変換 `Nat.le_of_lt`
- 存在量化と否定
- 前段のプロジェクト定義・補題

モジュール分割上は、`BranchB.lean` が `CounterexamplePack`、`CleanGN5Channel`、`Body5` 関連 bridge を得られるプロジェクト内 import を持てば足りるはずである。具体的には `DkMath.FLT.Five.CleanChannel` と、そこから推移的に必要となる `Basic`・`GN5` が候補となる。

ただし、個別モジュール `BranchB.lean` の正確な import 行は今回参照した生成済み standalone 断片には保存されていない。したがって、`import Mathlib` からの縮小可否と最小 import 集合は推測を含み、`lake env lean` またはプロジェクトの import 監査で確認すべきである。本作業では Lean ビルドを行っていない。

## 11. Comparator challenge 化の可否

適している。

### Challenge A — adapter の再構成

次の宣言型と利用可能な補題だけを与え、三行程度の証明を再構成させる。

- `right_lt_of_fermat5Equation`
- `body5_eq_fifth_power_of_fermat`
- `not_fifth_power_body_of_clean`

評価点は、`¬∃` を関数として適用できるか、witness に `x` を選べるか、`y≤z` を正しく作れるかである。

### Challenge B — definitional equality の認識

`Body5 g y` と `g * GN5 g y` の間に明示的 rewrite がなくても証明が通る理由を説明させる。単なる数学理解ではなく Lean の reducibility 理解を測れる。

### Challenge C — 過剰自動化との比較

`aesop` や強い自動化で閉じる版と、現在の明示的 proof term を比較し、依存・可読性・将来の API 変更耐性を評価させる。

## 12. 根拠と推測の区別

確認済み事項：

- 宣言名、型、証明本体
- `BranchB.lean` 内で `body5_eq_fifth_power_of_fermat` の直後に置かれること
- この宣言で `BranchB.lean` が終了し、次に `Provider.lean` が始まること
- standalone 全体が `import Mathlib` で生成されていること

推測・監査候補：

- 個別 `BranchB.lean` の最小 import 集合
- `CounterexamplePack.y_le_z` を追加した場合の全体的な重複削減効果
- `Body5` 版 consumer wrapper の有用性

既存 PDF は証明全体の物語を理解する補助資料であるが、本記事の宣言型と証明手順はリポジトリ内 Lean ソースを最終根拠とした。

## 13. 次に読むべき宣言

次は `DkMath.FLT.Five.BranchBCleanGN5ChannelProvider` を読む。

```lean
abbrev BranchBCleanGN5ChannelProvider : Prop :=
  ∀ {x y z : ℕ},
    CounterexamplePack x y z →
    ¬ 5 ∣ z - y →
    ∃ q : ℕ, CleanGN5Channel (z - y) y q
```

本号が「clean channel が与えられれば反例候補を閉じる」局所 refuter であるのに対し、次号は Branch B の任意の反例候補へ clean channel を供給する条件付き provider interface を定義する。これにより、局所矛盾と素数供給問題の責務分離が明確になる。
