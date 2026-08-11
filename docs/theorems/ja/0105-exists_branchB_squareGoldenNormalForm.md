# 0105 — `exists_branchB_squareGoldenNormalForm`

## Lean の型

```lean
theorem exists_branchB_squareGoldenNormalForm
    {x y z : ℕ} (hPack : CounterexamplePack x y z)
    (hBranch : ¬ 5 ∣ z - y) :
    ∃ a b : ℕ, BranchBSquareGoldenNormalForm x y z a b := by
  rcases exists_branchB_fifthPowerNormalForm hPack hBranch with ⟨a, b, hNF⟩
  have hzy : a ^ 5 + y = z := by
    simpa [Nat.add_comm] using hNF.z_eq.symm
  have hGolden :
      GoldenNorm (SquareGoldenM z y) (SquareGoldenN z y) = (b : ℤ) ^ 5 := by
    have h := goldenNorm_eq_fifth_power_of_GN5 hNF.GN_eq
    simpa [SquareGoldenM, SquareGoldenN, hzy] using h
  have hzInt : (z : ℤ) = (y : ℤ) + (a : ℤ) ^ 5 := by
    exact_mod_cast hNF.z_eq
  have hTenth :
      SquareGoldenM z y - 2 * SquareGoldenN z y = (a : ℤ) ^ 10 := by
    calc
      SquareGoldenM z y - 2 * SquareGoldenN z y =
          ((z : ℤ) - (y : ℤ)) ^ 2 := squareGolden_tenth_boundary_base z y
      _ = (a : ℤ) ^ 10 := by
        rw [hzInt]
        ring
  have hSquare := squareGolden_square_discriminant z y
  have hDiscFive :
      (2 * SquareGoldenM z y + SquareGoldenN z y) ^ 2 -
          5 * (SquareGoldenN z y) ^ 2 =
        4 * (b : ℤ) ^ 5 := by
    calc
      (2 * SquareGoldenM z y + SquareGoldenN z y) ^ 2 -
            5 * (SquareGoldenN z y) ^ 2 =
          4 * GoldenNorm (SquareGoldenM z y) (SquareGoldenN z y) :=
        (four_mul_goldenNorm_eq_discriminant_five
          (SquareGoldenM z y) (SquareGoldenN z y)).symm
      _ = 4 * (b : ℤ) ^ 5 := by rw [hGolden]
  exact ⟨a, b, hNF, hGolden, hTenth, hSquare, hDiscFive⟩
```

## 数学的主張

仮定は Branch-B にいる primitive な FLT5 候補である。

- `hPack : CounterexamplePack x y z` は正値・互いに素・$x^5+y^5=z^5$ を保持する。
- `hBranch : ¬ 5 ∣ z-y` は gap が $5$ で割れない Branch-B 条件である。

この二条件から、ある自然数 $a,b$ が存在して 0104 `BranchBSquareGoldenNormalForm x y z a b` を満たすことを示す。

0104 の packet を展開すると、まず従来の fifth-power normal form

$$
z=y+a^5,
$$

および

$$
GN5(a^5,y)=b^5
$$

を保持し、さらに square/golden 座標

$$
M=z^2+y^2,\qquad N=zy
$$

に対して

$$
\operatorname{GoldenNorm}(M,N)=b^5,
$$

$$
M-2N=a^{10},
$$

$$
M^2-4N^2=(z^2-y^2)^2,
$$

$$
(2M+N)^2-5N^2=4b^5
$$

を同時に得る。

したがって本 theorem は新しい一個の恒等式を発見するものではなく、それまで別々に証明してきた fifth-power、square、golden、判別式 $5$ の情報が **同じ witness $a,b$ に対して同時成立する** ことを保証する存在定理である。

## 証明全体での役割

本 theorem は `SquareGoldenNormalForm.lean` における **組立 theorem** である。

0104 までは、必要な部品が別々に用意されていた。

1. `exists_branchB_fifthPowerNormalForm` が $a,b$ と fifth-power normal form を供給する。
2. 0099 `goldenNorm_eq_fifth_power_of_GN5` が `GN5 = b^5` を golden norm へ輸送する。
3. 0102 `squareGolden_tenth_boundary_base` が $M-2N=(z-y)^2$ を与える。
4. 0103 `squareGolden_square_discriminant` が $M^2-4N^2=(z^2-y^2)^2$ を与える。
5. 0097 `four_mul_goldenNorm_eq_discriminant_five` が golden norm を判別式 $5$ の形へ対角化する。

本 theorem はこれらを一度だけ接続し、最後に

```lean
exact ⟨a, b, hNF, hGolden, hTenth, hSquare, hDiscFive⟩
```

として 0104 の proof packet を構築する。

この変換により、後続の contradiction core は cyclotomic factorization や cast の詳細を再び扱う必要がない。`BranchBSquareGoldenNormalForm` だけを受け取って square/golden invariant に集中できる。

すなわち proof architecture はここで

$$
\text{Branch-B arithmetic}
\longrightarrow
\text{fifth-power normal form}
\longrightarrow
\text{square/golden packet}
\longrightarrow
\text{contradiction core}
$$

と明確に phase 分離される。

## 直接依存する定義・補題

本 theorem が直接利用する project-local 宣言は次のとおりである。

1. `CounterexamplePack`
2. 0104 `BranchBSquareGoldenNormalForm`
3. `exists_branchB_fifthPowerNormalForm`
4. 0099 `goldenNorm_eq_fifth_power_of_GN5`
5. 0100 `SquareGoldenM`
6. 0101 `SquareGoldenN`
7. 0102 `squareGolden_tenth_boundary_base`
8. 0103 `squareGolden_square_discriminant`
9. 0097 `four_mul_goldenNorm_eq_discriminant_five`

さらに `hNF` の field として `BranchBFifthPowerNormalForm.z_eq` と `BranchBFifthPowerNormalForm.GN_eq` を利用する。

重要なのは、0104 の structure 自体が 0099・0102・0103・0097 を参照しないのに対し、本 theorem はそれらを実際に呼び出して inhabitant を作る点である。0104 が API の型なら、0105 はその canonical constructor theorem と読める。

## 証明の流れ

### 1. fifth-power normal form の witness を取得する

```lean
rcases exists_branchB_fifthPowerNormalForm hPack hBranch with ⟨a, b, hNF⟩
```

ここで existential witness $a,b$ を一度だけ選び、以後すべての invariant を同じ二数に結びつける。

### 2. `z = y + a^5` の向きを golden bridge 用に整える

`hNF.z_eq` の向きから

```lean
have hzy : a ^ 5 + y = z := by
  simpa [Nat.add_comm] using hNF.z_eq.symm
```

を作る。

0099 の bridge は `g+y` 型の座標を使うため、gap $g=a^5$ を `z` に戻す rewrite にこの形が便利である。

### 3. GN5 の fifth power を golden norm へ輸送する

```lean
have h := goldenNorm_eq_fifth_power_of_GN5 hNF.GN_eq
simpa [SquareGoldenM, SquareGoldenN, hzy] using h
```

0099 の結果は gap 座標 $(a^5,y)$ で表現される。それを `hzy` で endpoint $z$ に戻し、0100・0101 の named coordinate API に一致させて `hGolden` を得る。

### 4. 自然数の normal form を整数等式へ移す

```lean
have hzInt : (z : ℤ) = (y : ℤ) + (a : ℤ) ^ 5 := by
  exact_mod_cast hNF.z_eq
```

後続の差

$$
(z:ℤ)-(y:ℤ)
$$

を扱うため、自然数等式を整数へ cast する。

### 5. tenth-power boundary を構築する

0102 から

$$
M-2N=(z-y)^2
$$

を得て、`hzInt` を代入する。

$$
(z-y)^2=(a^5)^2=a^{10}.
$$

Lean では最後を `ring` に任せる。

### 6. square discriminant をそのまま取得する

```lean
have hSquare := squareGolden_square_discriminant z y
```

ここは完全な再利用であり、新たな algebraic normalization はない。

### 7. golden norm を判別式 $5$ へ変換する

0097 の対角化を逆向きに使って

$$
(2M+N)^2-5N^2=4\operatorname{GoldenNorm}(M,N)
$$

とし、`hGolden` を rewrite して

$$
(2M+N)^2-5N^2=4b^5
$$

を得る。

### 8. packet を構築する

最後に、得た四つの invariant と元の `hNF` を constructor へ渡す。

この一行が本 theorem の目的を最もよく表している。

## Lean 固有の処理

### 1. `rcases` で existential witness を固定する

本 theorem の核心は witness synchronization である。`a,b` を最初に `rcases` で固定するため、後で構築される golden/square の各式が同じ fifth-power decomposition に由来することが型レベルで保証される。

### 2. `simpa` が API 間の座標変換を吸収する

`hGolden` では、新しい数学を証明しているのではなく、0099 の gap-based expression を 0100・0101 の endpoint-based API へ変換している。

```lean
simpa [SquareGoldenM, SquareGoldenN, hzy] using h
```

は定義展開、加法の置換、endpoint の再同定を一度に処理する。

### 3. `exact_mod_cast` が `ℕ` と `ℤ` の境界を担当する

`hNF.z_eq` は自然数等式だが、square/golden world は整数上にある。`exact_mod_cast` により、同一の等式内容を安全に整数へ移す。

これは単なる見た目の coercion ではなく、`Nat.sub` の切り詰めを避けて通常の環の差を使うための phase transition である。

### 4. `ring` は局所的に一度だけ使う

本 theorem では大規模な恒等式を `ring` で再証明しない。`ring` の役割は

$$
((y+a^5)-y)^2=a^{10}
$$

という局所的な正規化だけである。

square discriminant と判別式 $5$ は既存 theorem を再利用しているため、proof provenance が保たれている。

### 5. `.symm` で 0097 を consumer 側の向きにする

0097 は

$$
4\operatorname{GoldenNorm}(M,N)=(2M+N)^2-5N^2
$$

の向きだが、本 theorem の goal は右辺の判別式から始まる。そこで `.symm` により rewrite-friendly な向きへ変えている。

## 冗長・重複箇所

### `hDiscFive` は `hGolden` から導出可能

0104 でも指摘した通り、`discriminant_five_eq` は `golden_eq` と 0097 から常に導出できる。本 theorem はそれを明示的に再計算して packet field として materialize している。

論理最小性だけを見るなら冗長である。しかし downstream が判別式 $5$ の式を直接欲する場合、毎回 0097 を適用せず projection 一回で済む。

### `hzy` と `hzInt` は同じ normal form の二つの型表現

`hzy` は自然数上で 0099 の gap coordinate rewrite に使い、`hzInt` は整数上で tenth boundary に使う。同一の `hNF.z_eq` から二つの補助等式を作っているため、意味としては重複する。

ただし両者を無理に統一すると cast rewrite が増え、proof readability が落ちる可能性が高い。現行コードは自然数 phase と整数 phase の境界を明示していると評価できる。

### 0102 の平方完成はここでも直接 `ring` 可能

`hTenth` 全体を 0100・0101・`hzInt` から直接 `ring` で証明することも可能である。しかし現行 proof は 0102 を経由し、既に博物館で独立 theorem として切り出した平方境界を再利用する。これは重複削減と proof graph の可視性の面で現行の方がよい。

## 最適化候補

### 候補 A — `hzy` / `hzInt` の変換補題を normal-form API に追加する

`BranchBFifthPowerNormalForm` に

```lean
z_eq_int : (z : ℤ) = (y : ℤ) + (a : ℤ) ^ 5
```

のような derived theorem を用意すれば、本 theorem 内の `exact_mod_cast` を隠蔽できる。

ただし normal form structure 自体へ整数世界の API を増やすことになり、自然数中心の前半と整数中心の後半の separation が弱くなる。

### 候補 B — 0104 の derived field を theorem 化する

`discriminant_five_eq` を structure field から外し、例えば

```lean
theorem BranchBSquareGoldenNormalForm.discriminant_five_eq ...
```

として `golden_eq` から導出すれば、本 theorem の `hDiscFive` block と constructor obligation を削除できる。

これは logical core を小さくする最も明確な候補である。一方、packet construction 完了時点で全 invariant が materialize 済みであるという現在の phase semantics は弱くなる。

### 候補 C — named-field constructor へ変更する

現在の

```lean
exact ⟨a, b, hNF, hGolden, hTenth, hSquare, hDiscFive⟩
```

は短いが、0104 の field 順に依存する。

`refine ⟨a, b, { normal := ..., golden_eq := ..., ... }⟩` のような named constructor は長くなる代わりに、structure field の追加・並べ替えへの耐性が高い。

### 候補 D — `hTenth` の最後を `norm_num` / `ring_nf` と比較する

現行の `ring` は明快であり、実質的に最適に近い。`ring_nf` に変える利点は小さい。むしろ一般補題

$$
((Y+A^5)-Y)^2=A^{10}
$$

を別に作るかどうかが設計上の比較対象になる。

## 必要な Mathlib import と import 最適化候補

対象ブランチの generated standalone artifact `Flt5DkMath/FLT5StandAlone.lean` は `import Mathlib` を使用している。

本 theorem で直接見える Mathlib 側の機能は主に次である。

- `rcases`
- `simpa`
- `exact_mod_cast`
- `rw`
- `ring`
- `Nat.add_comm`
- 自然数から整数への coercion

したがって theorem 単独の tactic 面では `Mathlib.Tactic` 系、特に `ring` と cast normalization を供給する import 群が主要候補になる。ただし実際の project module は `CounterexamplePack`、normal form、square/golden bridge など多数の project-local 宣言を経由しており、それらの import closure も必要である。

本作業では Lean ビルドを行わないため、具体的な最小 import リストは **未検証の推測として固定しない**。安全な現状は standalone の `import Mathlib` であり、import 最適化を行うなら別途 `#check` / build による段階的削減が必要である。

## Comparator challenge 化の可否

**適している。** 特に proof architecture 比較に向く。

### Challenge 1 — theorem reuse vs 一括 `ring`

現行版は 0102・0103・0097 を再利用する。対案として `SquareGoldenM/N` と normal form を展開し、大部分を algebraic tactics で直接閉じる版を作れる。

比較指標は次である。

1. 行数
2. tactic 実行量
3. upstream theorem 変更への追従性
4. 数学的 provenance の読みやすさ
5. failure localization

現行版は行数だけなら必ずしも最短ではないが、どの invariant がどの theorem から来たかが明瞭である。

### Challenge 2 — materialized packet vs minimal packet

0104 の `discriminant_five_eq` を field として保持する版と、`golden_eq` から derived theorem として作る版を比較できる。

これは「論理最小性」と「downstream API の即時性」の比較として良い Comparator challenge になる。

### Challenge 3 — positional constructor vs named constructor

最後の constructor 一行を、field 名付き構築へ置き換える比較も可能である。短さでは positional、保守性では named-field が有利になる可能性が高い。

## 既存資料との照合

形式的根拠は対象ブランチの `Flt5DkMath/FLT5StandAlone.lean` に収録された `DkMath/FLT/Five/SquareGoldenNormalForm.lean` generated section である。そこで本 theorem が 0104 `BranchBSquareGoldenNormalForm` の直後にあり、その後に `BranchBSquareGoldenCore` が続くことを確認した。

既存の日本語・英語 PDF については、今回 GitHub code search が upstream 502 を返し、具体的な PDF ファイル位置・ページ対応を再確認できなかった。そのため PDF の節番号・ページ番号は推測で補っていない。数学的・形式的内容は Lean source を最終根拠としている。

## 次に読むべき宣言

依存順で次に現れる宣言は

```lean
abbrev BranchBSquareGoldenCore : Prop :=
  ∀ {x y z a b : ℕ}, BranchBSquareGoldenNormalForm x y z a b → False
```

である。

これは 0105 が構築した大きな packet から、後半に本当に要求する interface を

$$
\text{BranchBSquareGoldenNormalForm}\to\mathrm{False}
$$

だけへ絞り込む receiver abstraction である。

その直後の theorem `branchB_false_of_squareGoldenCore` は、本 theorem `exists_branchB_squareGoldenNormalForm` で packet を作り、`BranchBSquareGoldenCore` へ渡して Branch-B を閉じる。

したがって次は `BranchBSquareGoldenCore` を読むのが依存順として自然である。