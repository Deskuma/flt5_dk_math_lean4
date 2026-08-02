# FLT5 定理博物館 — 日本語正本

> 本文書群は日本語正本です。英語版は本正本からの対応翻訳として刊行します。

## この博物館について

Lean 4 による指数5の場合のフェルマーの最終定理の形式化を、入口から依存順に一宣言ずつ読む定理解説集です。定義・構造体・補題・定理を個別の展示物として分離し、それぞれが受け取る事実と次へ渡す事実を記録します。

日本語版を正本とし、英語版は内容・宣言名・数式・節構成を保った対応翻訳とします。数学的・形式的な最終根拠はリポジトリ内の Lean ソースです。

## 番号規則

各記事は依存順の4桁番号と宣言名を共有します。

```text
0001-DeclarationName.md
0002-NextDeclaration.md
...
```

各号には Lean の型、数学的主張、証明全体での役割、直接依存、証明の流れ、Lean 固有処理、冗長性、最適化候補、Mathlib import、Comparator challenge 化、次に読む宣言を収録します。確認事実と未検証の提案は区別して記します。

## 目録

- [0001 — `Fermat5Equation`](./0001-Fermat5Equation.md) — 指数5方程式の最小命題インターフェース。
- [0002 — `CounterexamplePack`](./0002-CounterexamplePack.md) — 正値性・原始性・方程式を束ねる入力構造体。
- [0003 — `fifth_sub_eq_of_add_eq`](./0003-fifth_sub_eq_of_add_eq.md) — 加法形を自然数上の第五冪差分形へ移す補題。

次号は `DkMath.FLT.Five.right_lt_of_fermat5Equation` を扱います。
