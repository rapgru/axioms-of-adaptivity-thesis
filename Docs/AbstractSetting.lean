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

In this chapter, we formalize the abstract setting from the paper
_Axioms of adaptivity_{citep axioms}[], building on the mesh
definition from the previous chapter.

The setting of *AoA* is that we want to approximate the solution of our
problem in some vector space $`𝒳`. In the formalization this
space is represented by the type variable {anchorTerm RefinementIndicator}`β`.
The proofs that we formalize do not depend on the concrete structure of
{anchorTerm RefinementIndicator}`β` so we do not need to assume any additional
structure on it.

# Refinement Indicators

Before formalizing all *AoA* assumptions, we define a few convenient
abbreviations regarding refinement indicators in Lean.

We define the type abbreviation {anchorTerm RefinementIndicator}`RefinementIndicator`
for a function that maps from a mesh, a element of the vector space and an element of the mesh
to a real number:
```anchor RefinementIndicator
abbrev RefinementIndicator (α : Type*) [DecidableEq α] [Lattice α] [OrderBot α] (β : Type*) :=
  Mesh α → β → α → ℝ
```
The idea is that an instance of this type should estimate for any mesh
$`T` the local error on an element $`t∈T` for an approximation $`x ∈ 𝒳`
to the actual solution.

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

Now, we summarize all assumptions from *AoA* in the structure
{anchorTerm AdaptiveAlgorithm_1}`AdaptiveAlgorithm`.
This allows us to use an instance of {anchorTerm AdaptiveAlgorithm_1}`AdaptiveAlgorithm`
as an assumption for theorems and also to access practical lemmas and definitions
via dot access notation.

First, we define two helper functions for constants that are
calculated from other constants.
```anchor AdaptiveAlgorithm_constfuns
private noncomputable def ε_qos' (ρ_red C_rel C_red C_stab θ : ℝ) := ⨆ δ > 0, (1-(1+δ)*(1-(1-ρ_red)*θ)) / (C_rel^2 * (C_red + (1+δ⁻¹)*C_stab^2))
private def C_rel' (C_Δ C_drel : ℝ) := C_Δ * C_drel
```

Then we can go ahead and start building up the structure.
```anchor AdaptiveAlgorithm_1
structure AdaptiveAlgorithm (α β: Type*) [DecidableEq α] [Lattice α] [OrderBot α] where
```

We will now go through all the fields of the {anchorTerm AdaptiveAlgorithm_1}`AdaptiveAlgorithm`
structure. Because the documentation of the formalized proofs is accompanied by
a ready-to-formalize version of the proof in regular mathematical notation, most
fields also has a typeset notation (aligning with *AoA*) that is used in this document.
We write $`mathbb{T}` for the set of all meshes on the lattice $`X` (c.f. {ref "meshes"}[Meshes])
$`𝒳` is again the appropriate vector space for the AFEM problem, implemented with the type
{anchorTerm AdaptiveAlgorithm_1}`β`.

We suppose that a numerical solver $`U : mathbb{T} → 𝒳` exists
```anchor AdaptiveAlgorithm_2
  -- Numerical solver --
  U : Mesh α → β
```
which approximates an unkown limit or solution $`u ∈ 𝒳`:
```anchor AdaptiveAlgorithm_3
  -- Limit --
  u : β
```

Assume that $`η_t(T, ·) : 𝒳 → [0,∞)` is a computable refinement indicator for
every element $`t` and mesh $`T` that satisfy $`t ∈ T ∈ \mathbb{T}`.
```anchor AdaptiveAlgorithm_4
  -- Refinement indicator --
  η : RefinementIndicator α β
  hη : η ≥ 0
```
Here, we have to note that the type {anchorTerm AdaptiveAlgorithm_4}`RefinementIndicator`
we defined above is slightly inaccurate. The third argument, which is
the local element can only come from the mesh that is given as a first argument.
So actually we want to have a family of functions $`𝒳 → [0,∞)` for all
combinations $`t∈T∈\mathbb{T}`. In other words, the type of the local element
argument depends on which mesh has been passed to the first argument.
So {anchorTerm AdaptiveAlgorithm_4}`η` has to be defined on many more
parameter combinations than what *AoA* prescribes. However, the formalization
will never supply a mesh and an element that is not from this mesh to the refinement
indicator which is why we afford this inaccuracy.

We also suppose that we have an error measure $`\mathbb{d} : \mathbb{T} × 𝒳 × 𝒳 → [0,\infty)`
and a constant $`C_Δ > 0` such that the following conditions hold:
1. $$`\mathbb{d}[T; v_1, v_2] ≥ 0` for all $`T ∈ \mathbb{T}, v_1, v_2 ∈ 𝒳` (non-negativity)
2. $$`\mathbb{d}[T; v_1, v_2] ≤ C_Δ \mathbb{d}[T; v_2, v_1]` for all $`T ∈ \mathbb{T}, v_1, v_2 ∈ 𝒳` (quasi-symmetry)
3. $$`C_Δ^{-1} \mathbb{d}[T; v_1, v_3] ≤ \mathbb{d}[T; v_1, v_2] + \mathbb{d}[T; v_2, v_3]` for all $`T ∈ \mathbb{T}, v_1, v_2 ∈ 𝒳` (quasi-triangle inequality)

In Lean we define:
```anchor AdaptiveAlgorithm_5
  -- Error measure --
  d : Mesh α → β → β → ℝ
  C_Δ : ℝ
  hC_Δ : 0 < C_Δ
  non_neg : ∀ T v w, d T v w ≥ 0
  quasi_symmetry : ∀ T v w, d T v w ≤ C_Δ * d T w v
  quasi_triangle_ineq : ∀ T v w y, C_Δ⁻¹ * d T v y ≤ d T v w + d T w y
```

Suppose that $`𝒯 : ℕ → \mathbb{T}` is the sequence of meshes generated by
the standard AFEM algorithm (c.f. {ref "afem_alg"}[AFEM method]).
```anchor AdaptiveAlgorithm_6
  -- Triangulation sequence --
  𝒯 : ℕ → Mesh α
  h𝒯 : ∀ l, 𝒯 (Nat.succ l) ≤ 𝒯 l
```

We assume that the algorithm uses Dörfler marking with parameter $`θ ∈ (0,1)`
and $`ℳ : ℕ → \mathbb{T}` is the sequence of minimal submeshes that were selected
for refinement.
```anchor AdaptiveAlgorithm_7
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
```

Now only the actual "Axioms of Adaptivity" remain. We start with stability (A1), which states that with a constant $`C_{stab} > 0`
$$`\left|\sqrt{\sum_{t \in S} η_t(T'; v')^2} - \sqrt{\sum_{t \in S} η_t(T; v)^2}\right| ≤ C_{stab} \mathbb{d}[T'; v', v]`
for all $`T' ≤ T`, $`S ⊆ T ∩ T'` and $`v,v' ∈ 𝒳`.
```anchor AdaptiveAlgorithm_8
  -- A1: stability on non-refined element domains --
  C_stab : ℝ
  hC_stab : C_stab > 0
  a1 : ∀ T : Mesh α, ∀ T' ≤ T, ∀ S ⊆ T ∩ T', ∀ v v',
    |√(∑ t ∈ S, η T' v' t ^ 2) - √(∑ t ∈ S, η T v t ^ 2)| ≤ C_stab * d T' v' v
```

Reduction (A2) requires that for constants $`0 < ρ_{red} < 1` and $`C_{red} > 0`
$$`∑_{t ∈ T' \setminus T} η_t(T'; U(T'))^2 ≤ ρ_{red} ∑_{t ∈ T \setminus T'} η_t(T; U(T))^2 + C_{red} \mathbb{d}[T'; U(T'), U(T)]^2`.
```anchor AdaptiveAlgorithm_9
  -- A2: reduction property on refined elements --
  ρ_red : ℝ
  hρ_red : ρ_red ∈ Set.Ioo 0 1
  C_red : ℝ
  hC_red : 0 < C_red
  a2 : ∀ T : Mesh α, ∀ T' ≤ T,
    ∑ t ∈ T' \ T, η T' (U T') t ^ 2 ≤ ρ_red * ∑ t ∈ T \ T', η T (U T) t ^ 2 + C_red * d T' (U T') (U T) ^ 2
```

Reliability (A4) states that for some $`C_{rel} > 0`
$$`\mathbb{d}[T; u, U(T)] ≤ C_{rel} η(T; U(T))`
for all $`T ∈ \mathbb{T}`. Note that our formalized version uses the derived constant $`C_{rel} = C_Δ C_{drel}` with $`C_{drel} > 0`.
```anchor AdaptiveAlgorithm_10
  -- A4: reliability --
  C_drel : ℝ
  hC_drel : 0 < C_drel
  -- This is a result from A4 and the compatibility condition of the measure d (Lemma 3.4).
  -- Because this proof is not formalized we assume this result instead of A4.
  reliability' : ∀ T, d T u (U T) ≤ C_rel' C_Δ C_drel * √(gη2 η T (U T))
```

Finally, general quasi-orthogonality (A3) states that for $`C_{qo} ≥ 1` and sufficiently small $`ε_{qo} ≥ 0`
$$`∑_{k=ℓ}^{ℓ+n-1} \left(\mathbb{d}[𝒯_{k+1}; U(𝒯_{k+1}), U(𝒯_k)]^2 - ε_{qo} \mathbb{d}[𝒯_k; u, U(𝒯_k)]^2\right) ≤ C_{qo} η(𝒯_ℓ; U(𝒯_ℓ))^2`.
```anchor AdaptiveAlgorithm_11
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
are the abbreviations for the term $`η^2(𝒯_l, U(𝒯_l))`.

```anchor seq_abbrev
def gη2_seq l := gη2 alg.η (alg.𝒯 <| l) (alg.U <| alg.𝒯 <| l)
noncomputable def nn_gη_seq n := NNReal.sqrt (alg.gη2_seq n).toNNReal
```

The second line is a version that maps to the non-negative Reals and gives $`η`
as opposed to $`η^2`. This definition is used in for the proof
of estimator convergence, more in -- TODO!! cite
