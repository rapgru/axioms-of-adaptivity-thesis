import VersoManual
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Docs

set_option pp.rawOnError true

-- Abschließende Gedanken, was könnten man noch machen, wo sind die größten
-- Schwierigkeiten, Link zum Github Repo

#doc (Manual) "Conclusion" =>
%%%
htmlSplit := .never
%%%



We have seen four lemmas of *AoA* formalized in Lean.
When seen as a case study, we can definitely say
that Lean and especially the ecosystem including {ref "mathlib"}[mathlib4]
is already very apt to prove numerical theorems in. All the basic
infrastructure is there, starting with a formalization
in this field is effortless.

What did this formalization achieve?
- The lemmata we have formalized have been acknowledged as correct by
  Lean. This means that, assuming there Lean does not have compiler errors,
  they are implied by an axiom system that can be used as a
  foundation of mathematics.
- A very small index mistake was found in Lemma 4.7 of *AoA*
- The missing assumption $`a_n ≠ 0` was found in Lemma 4.9
- The constants that depend on the choice of $`δ` are now
  handled very precisely. Theorem statements including these
  constants are now very explicit about the role $`δ` plays in them,
  while in *AoA* these details are hidden in phrases like
  "for sufficiently small".


Altough, while definitions are very quick to translate into Lean,
proving theorems about the objects one has defined is far from effortless.
- A mathematician has the ability to quickly fill in clear, obvious
  facts. The computer cannot.
  An example that appeared very often in this documentation is that
  Lean required explicit proofs of non-negativity. A trained eye
  just "see" that a term is non-negative, but in Lean this could turn into
  an auxiliary proof that costs half an hour.
  Of course this is exactly where automated tools, which are
  a key component of Lean, can be help. As their improvement is a high priority goal
  in the roadmap, in the future Lean might catch up
  and reduce the effort needed to show facts that are obvious to humans.
- Additional complexity in the formalization of the type of proofs we have
  seen was arranging the proof in a way that it fits into a
  calculation (`calc`-block). While it turned out to be
  a very robust method, it requires fitting the whole proof into a
  chain of inequalities before one can start coding.


The theorems we formalized span about 2.5 pages in the _Axioms of adaptivity_
paper. In Lean it amounts to about 1700 lines of complex code.
This is at least a tenfold increase in lenght would we print out the source code.
This comparison should just underline that a formalization
is serious work. The question we can only leave open is,
if this effort is worth it to gain an ultimate answer about the correctness of the proof
in the context of computer numerics.

An interesting aspect of formal verification in the context of computational science
is that with Lean it is possible to prove correctness
of imperative programs (e.g. for the Rust programming language {citet ho2022aeneas}[]).
One could explore for example if it is possible to implement
an AFEM solver and prove the axioms of adaptivity for it.
Such a solver could have unmatched guarantees in terms of
correctness.

# Learnings About Theorem Proving in Lean

We also want to summarize a few learnings that might be helpful to others
who want to formalize similar theorems in Lean.
- The most important thing to learn is how to search for existing
  theorems and defintions in mathlib4. This takes some time getting used to,
  but has a large pay-off
- Carefully choosing the structure you work in can help reduce the effort
  needed for a proof. For example, in the `NNReal`s the closedness of the multiplication
  means that obtaining a proof of the non-negativity of a product is effortless.
  On the other hand, if theorems are formulated for `NNReal`s additional effort
  might occur when the application of the those theorems requires non-negativity
  proofs for the parameters. Thinking about how to balance these two sides
  might save programming effort.
  For {ref "estimator_convergence"}[Cor. 4.8] it might have been sound to
  use the extended non-negative real numbers (type `ENNReal`) in the `SimpleEstimatorReduction`
  part because the mathlib theorems about the $`\limsup` do not require
  proofs of boundedness for the sequences involved. This would have shortened our
  proofs considerable, but maybe at the cost of additional work
  when we want to apply the `ENNReal`-result to a real sequence.
- Structuring numerical proofs in a way that they fit into a `calc`-block
  was a robust method for our theorems at least

# Lean Repository
%%%
tag := "code"
%%%

The Lean code that accompanyies this thesis is available online in the
[Github repository](https://github.com/rapgru/axioms-of-adaptivity).
