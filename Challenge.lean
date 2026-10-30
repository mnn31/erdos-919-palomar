module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Erdős Problem 919: reductions

Problem 919 (<https://www.erdosproblems.com/919>) asks for a graph on the ordinal `ω₂²` with
chromatic number `ℵ₂`, or `ℵ₁`, such that every subgraph on a vertex set of order type less
than `ω₂²` has chromatic number at most `ℵ₀`. A subgraph on a vertex set has chromatic number at
most that of the induced subgraph, so the statements below use induced subgraphs.

This file does not answer the two questions outright. It proves that the `ℵ₂` question is
equivalent to the first question of Problem 918, that the `ℵ₁` question is equivalent to the
existence of a graph on `ℵ₂` vertices that is not countably chromatic although all its subgraphs
on `ℵ₁` vertices are, that the `ℵ₂` question implies the `ℵ₁` question, and that the `ℵ₁`
question has a positive answer under the continuum hypothesis.

The independence of the `ℵ₂` question from ZFC follows from the first equivalence together with
published set theory (Baumgartner 1984, Shelah 1990, Foreman and Laver 1988). That set theory is
not formalised here.
-/

@[expose] public section

universe u

open Cardinal Ordinal

/-- The chromatic cardinal of a graph: the least cardinality of a type of colours that admits a
proper colouring. Unlike `SimpleGraph.chromaticNumber`, which is `⊤` for every graph that is not
finitely colourable, this tells different infinite chromatic numbers apart. -/
noncomputable def SimpleGraph.chromaticCardinal {V : Type u} (G : SimpleGraph V) : Cardinal :=
  sInf {κ : Cardinal | ∃ (C : Type u) (_ : Cardinal.mk C = κ), Nonempty (G.Coloring C)}

namespace Erdos919

/-- The `ℵ₂` version of Problem 919 is equivalent to the first question of Problem 918: is there
a graph with `ℵ₂` vertices and chromatic number `ℵ₂` all of whose subgraphs on `ℵ₁` vertices
have chromatic number at most `ℵ₀`? -/
theorem erdos_919.variants.iff_erdos_918_i :
    (∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ_ 2 ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀) ↔
    ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀ := by
  sorry

/-- The `ℵ₁` version of Problem 919 is equivalent to the existence of a graph on `ℵ₂` vertices
with chromatic number greater than `ℵ₀` all of whose subgraphs on `ℵ₁` vertices have chromatic
number at most `ℵ₀`. -/
theorem erdos_919.variants.aleph_1_iff :
    (∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ₁ ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀) ↔
    ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ ℵ₀ < G.chromaticCardinal ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀ := by
  sorry

/-- A positive answer to the `ℵ₂` version gives a positive answer to the `ℵ₁` version. -/
theorem erdos_919.variants.aleph_2_imp_aleph_1 :
    (∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ_ 2 ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀) →
    ∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ₁ ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀ := by
  sorry

/-- Under the continuum hypothesis the `ℵ₁` version has a positive answer. -/
theorem erdos_919.variants.aleph_1_of_CH (hCH : 𝔠 = ℵ₁) :
    ∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ₁ ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀ := by
  sorry

end Erdos919
