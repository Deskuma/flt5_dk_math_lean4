# 0326 — `coprime_of_odd_of_no_common_odd_prime`

## 宣言種別

これは **`private theorem`** である。

`SignedGoldenZeroSectorFactorization.lean` の先頭に置かれた局所補題であり、モジュール外へ公開する API ではない。

## Lean の型

```lean
/-- An odd factor cannot share any prime with a second factor once common odd
prime divisors have been excluded. -/
private theorem coprime_of_odd_of_no_common_odd_prime
    {m n : ℕ} (hm : Odd m)
    (hodd : ∀ q : ℕ, Nat.Prime q → q ≠ 2 → q ∣ m → q ∣ n → False) :
    Nat.Coprime m n := by
  apply Nat.coprime_of_dvd
  intro q hq hqm hqn
  by_cases hq2 : q = 2
  · subst q
    have hmEven : Even m := even_iff_two_dvd.mpr hqm
    exact (Nat.not_even_iff_odd.mpr hm) hmEven
  · exact hodd q hq hq2 hqm hqn
```

型としては、暗黙引数 `m n : ℕ` に対して

```lean
Odd m →
(∀ q : ℕ, Nat.Prime q → q ≠ 2 → q ∣ m → q ∣ n → False) →
Nat.Coprime m n
```

である。

## 数学的主張

仮定は二つである。

1. `m` は奇数である。
2. `2` 以外の素数 `q` が `m` と `n` の両方を割ることはない。

このとき

$$
\gcd(m,n)=1
$$

すなわち `Nat.Coprime m n` が成立する。

論理は単純である。共通素因子 `q` が存在すると仮定する。`q=2` なら `2 ∣ m` なので `m` が偶数となり、`Odd m` に反する。`q≠2` なら第2仮定 `hodd` がその共通素因子を直接排除する。したがって共通素因子は一つも存在できない。

## FLT5 証明全体での役割

この theorem は零セクター反転後の factorization phase に入る最初の局所道具である。

直前の inversion packet では、正の自然数因子 `A0`, `B0` と

$$
A_0B_0=4Q^5,
$$

$$
B_0=A_0+8d^5
$$

などが得られている。factorization phase では、これらから 2 の冪を取り除いた因子同士が互いに素であることを示し、それぞれを独立した 5 乗部分へ分離していく必要がある。

本 theorem はそのための一般的な補助変換である。

- 一方の因子が奇数である。
- 共通奇素因子が存在しない。

という二つの情報を、Mathlib が後続で使いやすい `Nat.Coprime` へまとめる。

したがって「奇素因子排除」という局所的な素因数情報から「完全な互いに素性」へ昇格させる bridge とみなせる。

## 直接依存する定義・補題

### `Odd m`

`m` が奇数であることを表す標準述語である。

### `Nat.Prime q`

`q` が自然数上の素数であることを表す。

### `Nat.Coprime m n`

結論となる自然数上の互いに素性である。

### `Nat.coprime_of_dvd`

証明の骨格を与える Mathlib theorem である。共通の素因子 `q` を任意に取り、それが矛盾を起こすことを示す形へ問題を変換する。

### `even_iff_two_dvd`

`2 ∣ m` と `Even m` を結びつける。

### `Nat.not_even_iff_odd`

`Odd m` から `¬ Even m` を得るために使われる。

### `hodd`

この theorem の仮定であり、`q ≠ 2` の場合の共通素因子を直接排除する。

## 証明の流れ

1. `Nat.coprime_of_dvd` を適用して、互いに素性を「任意の共通素因子を排除する問題」へ変換する。
2. 素数 `q` と仮定 `q ∣ m`, `q ∣ n` を受け取る。
3. `by_cases hq2 : q = 2` で `q=2` と `q≠2` に分岐する。
4. `q=2` の場合は `subst q` で `q` を 2 に置換する。
5. `hqm : 2 ∣ m` から `even_iff_two_dvd.mpr hqm` により `Even m` を得る。
6. `hm : Odd m` から `Nat.not_even_iff_odd.mpr hm : ¬ Even m` を得て矛盾する。
7. `q≠2` の場合は `hodd q hq hq2 hqm hqn` がそのまま `False` を返す。

証明は共通素因子が 2 か奇素数かという完全な場合分けだけで閉じる。

## Lean 固有の処理

### `private theorem`

この宣言は namespace 内にはあるが `private` なので、生成された内部名を除き、通常の外部 API として参照することを意図していない。factorization module 内部だけで利用する局所補題である。

### `apply Nat.coprime_of_dvd`

結論 `Nat.Coprime m n` を、素因子ベースの証明目標へ変換している。数論的主張の形と Mathlib API の形を合わせる主要な一手である。

### `by_cases hq2 : q = 2`

素数 `q` を「唯一の偶素数 2」と「それ以外」に分ける。`hodd` は最初から `q ≠ 2` を要求するため、この分岐がインターフェース上自然である。

### `subst q`

`q = 2` の枝で変数 `q` を完全に 2 に置換し、`hqm` を `2 ∣ m` としてそのまま利用できる形にする。

### `.mpr`

`even_iff_two_dvd.mpr` と `Nat.not_even_iff_odd.mpr` は同値命題の右向き適用である。ここでは tactic より proof term を直接組み立てている。

## 冗長・重複箇所

証明自体に大きな冗長性はない。

ただし `q=2` の枝は、Mathlib に「奇数は 2 で割れない」という形のより直接的な lemma が利用可能なら、

```lean
exact hm.not_two_dvd_nat hqm
```

のような短縮が可能な可能性がある。ただしこの正確な lemma 名と適用可能性は本実行では Lean build を行っていないため **未確認** である。

また、仮定 `hodd` は

```lean
∀ q, Nat.Prime q → q ≠ 2 → q ∣ m → q ∣ n → False
```

という curried form で明示されている。読みやすさを重視するなら

```lean
∀ q, Nat.Prime q → q ≠ 2 → ¬ (q ∣ m ∧ q ∣ n)
```

のような形も考えられるが、後続 theorem からの適用しやすさは現行形の方が高い可能性がある。

## 最適化候補

最も自然な最適化候補は、`q=2` 枝を「Odd なら `¬ 2 ∣ m`」という直接 lemma で閉じることである。

もう一つは theorem 自体を公開 API にせず現行通り `private` に保つことである。内容は一般的だが、このモジュールでは factorization の局所的 glue theorem として使われており、公開 namespace を増やす積極的理由は見当たらない。

一方、同型の証明が他モジュールにも複数存在するなら共有 lemma 化の価値がある。この重複状況は本実行では repository 全体の同型 theorem を完全検索していないため **未確認** である。

## 必要 Mathlib import と import 最適化候補

確認できる正本 `Flt5DkMath/FLT5StandAlone.lean` は

```lean
import Mathlib
```

を使用する。

本 theorem が直接利用する主要 API は、

- `Nat.Coprime`
- `Nat.Prime`
- `Odd`, `Even`
- `Nat.coprime_of_dvd`
- `even_iff_two_dvd`
- `Nat.not_even_iff_odd`

である。

したがって理論上は `Mathlib` 全体より小さい import に縮約できる可能性が高い。しかし正確な最小 import 集合は Lean build / import minimization を実行していないため **未確認** である。

## Comparator challenge 化の可否

**適している。**

小さく自己完結した theorem であり、同じ数学的主張に対して複数の Lean 証明スタイルを比較しやすい。

比較候補は、

1. 現行の `Nat.coprime_of_dvd` + `by_cases q = 2`。
2. `Nat.coprime_iff_gcd_eq_one` から gcd の素因子を排除する方法。
3. `Nat.Coprime` の prime-divisor characterization を直接使う方法。
4. oddness から `¬ 2 ∣ m` を直接得る lemma を使って 2 の枝を短縮する方法。

評価軸は proof length、依存 lemma 数、読みやすさ、Mathlib API への頑健性、elaboration の単純さである。

## 次に読むべき宣言

次は同じ factorization module 内の private theorem

```lean
private theorem exists_eq_two_mul_odd_of_two_dvd_not_four_dvd
    {n : ℕ} (h2 : 2 ∣ n) (h4 : ¬ 4 ∣ n) :
    ∃ m : ℕ, n = 2 * m ∧ Odd m := by
  rcases h2 with ⟨m, hm⟩
  refine ⟨m, hm, Nat.not_even_iff_odd.mp ?_⟩
  rw [even_iff_two_dvd]
  intro h2m
  rcases h2m with ⟨k, hk⟩
  apply h4
  refine ⟨k, ?_⟩
  omega
```

である。

これは

$$
2\mid n,\qquad 4\nmid n
$$

から

$$
n=2m,\qquad m\text{ は奇数}
$$

を抽出する補題であり、二進付値がちょうど 1 の因子を `2 × odd` として正規化する。museum の依存順では **0327 `exists_eq_two_mul_odd_of_two_dvd_not_four_dvd`** として読むのが自然である。
