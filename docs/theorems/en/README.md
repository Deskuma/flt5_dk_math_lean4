# FLT5 Theorem Museum — English Translation

> This series is translated from the Japanese canonical edition. In case of editorial discrepancy, the Japanese edition is authoritative.

## About this museum

This gallery is a theorem-by-theorem guide to the Lean 4 formalization of Fermat's Last Theorem for exponent five. It reads the development from its entry point in explanatory dependency order, one declaration at a time.

Rather than summarizing the whole proof at once, the museum separates definitions, structures, lemmas, and theorems into individual exhibits. Each article records what a declaration receives, what it establishes, and what it passes to the next stage.

The series is designed to serve as:

- a guided reading route through the FLT5 proof;
- a dependency catalogue for public declarations;
- an explanation of Lean-specific proof processing;
- an audit notebook for redundancy and reconstruction;
- an import-minimization notebook for Mathlib dependencies;
- a source of small Comparator-style proof challenges.

## Canonical edition and translation

The Japanese edition is canonical. The English edition preserves the declaration names, formulas, article numbers, and section structure of the corresponding Japanese article.

The Lean source in this repository remains the final mathematical and formal authority. Neither language edition overrides the declarations checked by Lean's kernel.

## Numbering convention

Each article uses a four-digit sequence number followed by the declaration name:

```text
0001-DeclarationName.md
0002-NextDeclaration.md
...
```

The sequence follows explanatory dependency order rather than merely reproducing textual order in the standalone source. Japanese and English articles use matching numbers and file names.

## Standard article structure

Each article normally records:

1. the Lean declaration and fully qualified name;
2. the mathematical statement;
3. its role in the complete proof;
4. directly required definitions and lemmas;
5. the proof or construction flow;
6. Lean-specific coercions, rewrites, and tactics;
7. redundancy or duplication;
8. refactoring and optimization candidates;
9. required Mathlib imports and import-minimization candidates;
10. suitability for a Comparator challenge;
11. the next declaration to study.

Facts directly supported by the Lean source are distinguished from interpretation, inference, and unverified optimization proposals.

## Sources

The primary source is the Lean code checked by the kernel in this repository.

The existing Japanese and English PDFs are used as supporting narrative references for the mathematical route and background. They do not replace the types and implementations present in the Lean source.

## Catalogue

No numbered article has been published yet. Issue 0001 will begin with the minimal FLT5 equation interface, then proceed through the positive primitive counterexample packet, gap and GN5 stages, the 5-adic split, the golden integer order, unit classes, the zero sector, infinite descent, and the final refutation.
