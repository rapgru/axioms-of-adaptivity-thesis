import VersoManual
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Docs

set_option pp.rawOnError true
set_option verso.exampleProject "../axioms_of_adaptivity"
set_option verso.exampleModule "AxiomsOfAdaptivity.Basics"

#doc (Manual) "Abstract Setting" =>
%%%
htmlSplit := .never
%%%

In this chapter, we formalize the abstract setting presented in the paper
_Axioms of adaptivity_{citep axioms}[] in section 2, building on the mesh
definition from the previous chapter.

# Refinement Indicators

The setting of *AoA* is that we want to approximate the solution of our
problem in some vector space $`𝒳`. In the formalization this
space is represented by the type variable {anchorTerm RefinementIndicator}`β`.
The proofs that we formalize do not depend on the concrete structure of
{anchorTerm RefinementIndicator}`β` so we do not need to assume any additional
structure on it.

We then define the type abbreviation {anchorTerm RefinementIndicator}`RefinementIndicator`
for a function that maps from a mesh, a element of the vector space and an element of the mesh
to a real number:
```anchor RefinementIndicator
abbrev RefinementIndicator (α : Type*) [DecidableEq α] [Lattice α] [OrderBot α] (β : Type*) :=
  Mesh α → β → α → ℝ
```

In the following {anchorTerm beta}`β` will always be an arbitrary type.
```anchor beta
variable {β : Type*}
```

Based on a refinement indicator $`η` we can define the squared global error estimator $`η^2`
as
```anchor gη2
def gη2 (ri: RefinementIndicator α β) (triang: Mesh α) v :=
  ∑ t ∈ triang, (ri triang v t)^2
```
The name {anchorTerm gη2}`gη2` has a `g` prefix to signify that this is the global
error and a suffix `2` because it is the squared global error.

# Adaptive Algorithm

We summarize all assumptions from AoA in the structure {anchorTerm AdaptiveAlgorithm}`AdaptiveAlgorithm`.
This allows us to use an instance of {anchorTerm AdaptiveAlgorithm}`AdaptiveAlgorithm`
as an assumption for theorems and also to access practical lemmas and definitions
via dot access notation.

```anchor AdaptiveAlgorithm
structure AdaptiveAlgorithm (α β: Type*) [DecidableEq α] [Lattice α] [OrderBot α] where
  -- Numerical solver --
  U : Mesh α → β

  -- Limit --
  u : β

  -- Refinement indicator --
  η : RefinementIndicator α β
  hη : η ≥ 0

  -- Error measure --
  d : Mesh α → β → β → ℝ
  C_Δ : ℝ
  hC_Δ : 0 < C_Δ
  non_neg : ∀ T v w, d T v w ≥ 0
  quasi_symmetry : ∀ T v w, d T v w ≤ C_Δ * d T w v
  quasi_triangle_ineq : ∀ T v w y, C_Δ⁻¹ * d T v y ≤ d T v w + d T w y
  -- Because we assume reliability directly compatibility is not used
  -- compatibility: ∀ T v w, ∀ T' ≤ T, d T' v w = d T v w
  further_approximation : ∀ T, ∀ ε > 0, ∃ T' ≤ T, d T' u (U T') ≤ ε

  -- Triangulation sequence --
  𝒯 : ℕ → Mesh α
  h𝒯 : ∀ l, 𝒯 (Nat.succ l) ≤ 𝒯 l

  -- Dörfler marking --
  θ : ℝ
  hθ : θ ∈ Set.Ioc 0 1
  ℳ : ℕ → Mesh α
  -- Equation (2.5)
  -- Slightly stronger than AoA because it assumes the selected subset is
  -- of minimal instead of almost minimal cardinality
  hℳ : ∀ l,
    let doerfler M :=
      θ * gη2 η (𝒯 l) (U <| 𝒯 l) ≤ ∑ t ∈ M, η (𝒯 l) (U <| 𝒯 l) t ^ 2
    ℳ l ⊆ (𝒯 l \ 𝒯 (l+1))
    ∧ doerfler (ℳ l)
    ∧ ∀ M' ⊆ 𝒯 l, doerfler M' → (ℳ l).card ≤ M'.card

  -- A1: stability on non-refined element domains --
  C_stab : ℝ
  hC_stab : C_stab > 0
  a1 : ∀ T : Mesh α, ∀ T' ≤ T, ∀ S ⊆ T ∩ T', ∀ v v',
    |√(∑ t ∈ S, η T' v' t ^ 2) - √(∑ t ∈ S, η T v t ^ 2)| ≤ C_stab * d T' v' v

  -- A2: reduction property on refined elements --
  ρ_red : ℝ
  hρ_red : ρ_red ∈ Set.Ioo 0 1
  C_red : ℝ
  hC_red : 0 < C_red
  a2 : ∀ T : Mesh α, ∀ T' ≤ T,
    ∑ t ∈ T' \ T, η T' (U T') t ^ 2 ≤ ρ_red * ∑ t ∈ T \ T', η T (U T) t ^ 2 + C_red * d T' (U T') (U T) ^ 2

  -- A4: reliability --
  C_drel : ℝ
  hC_drel : 0 < C_drel
  -- This is a result from A4 and the compatibility condition of the measure d (Lemma 3.4).
  -- Because this proof is not formalized we assume this result instead of A4.
  reliability' : ∀ T, d T u (U T) ≤ C_rel' C_Δ C_drel * √(gη2 η T (U T))

  -- A3: general quasi-orthogonality --
  -- Comes last so that all constants are already available
  ε_qo : ℝ
  hε_qo' : 0 ≤ ε_qo ∧ ε_qo < ε_qos' ρ_red (C_rel' C_Δ C_drel) C_red C_stab θ
  C_qo : ℝ
  hC_qo : C_qo ≥ 1
  -- Here n + 1 is the number of summands, we don't need N ≥ l from AoA
  a3 : ∀ l n,
    ∑ k ∈ range n, (d (𝒯 <| k + l + 1) (U <| 𝒯 <| k + l + 1) (U <| 𝒯 <| k + l) ^ 2 - ε_qo * d (𝒯 <| k + l) u (U <| 𝒯 <| k + l) ^ 2)
    ≤ C_qo * gη2 η (𝒯 l) (U <| 𝒯 l)
```

Important additional definitions that appear throughout the formalization
are the abbreviations for the term $`η^2(𝒯_l, U(𝒯_l))` and
the that appears many times in *AoA*.

```anchor seq_abbrev
def gη2_seq l := gη2 alg.η (alg.𝒯 <| l) (alg.U <| alg.𝒯 <| l)
noncomputable def nn_gη_seq n := NNReal.sqrt (alg.gη2_seq n).toNNReal
```

The second line is a version that maps to the non-negative Reals and gives $`η`
as opposed to $`η^2`. This definition is used in for the proof
of estimator convergence, more in -- TODO!! cite
