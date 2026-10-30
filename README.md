# Reductions for Erdős Problem 919

[Erdős Problem 919](https://www.erdosproblems.com/919) asks for a graph on the ordinal `ω₂²` with
chromatic number `ℵ₂`, or `ℵ₁`, such that every subgraph on a vertex set of smaller order type is
countably chromatic.

This project proves four things in Lean 4 with Mathlib.

1. The `ℵ₂` question is equivalent to the first question of Erdős Problem 918.
2. The `ℵ₁` question is equivalent to the existence of a graph on `ℵ₂` vertices that is not
   countably chromatic although all its subgraphs on `ℵ₁` vertices are.
3. A positive answer to the `ℵ₂` question gives a positive answer to the `ℵ₁` question.
4. Under the continuum hypothesis the `ℵ₁` question has a positive answer.

It does not settle either question in ZFC. The first question of Problem 918 is known to be
independent of ZFC, relative to a huge cardinal, by Baumgartner (1984), Shelah (1990), and Foreman
and Laver (1988). Combined with item 1 that makes the `ℵ₂` question independent as well, but that
set theory is not formalized here.

## Files

`Challenge.lean` has the statements and is the file to read. It imports only Mathlib. Mathlib has
no chromatic cardinal of a graph, so the file defines `SimpleGraph.chromaticCardinal`.

`Solution.lean` has the proofs.

`comparator.json` lists the four theorems that have to match.

`formalization.yaml` records the sources, scope, and how the work was done.

## Building

```bash
lake exe cache get
lake build
```

Apache 2.0, see `LICENSE`.
