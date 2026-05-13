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

In this chapter, we formalize the abstract setting from the
article *AoA*, building on our mesh
definition from a {ref "meshes"}[previous chapter].

In the setting of *AoA*, we want to approximate the solution of our
problem in some vector space $`\mathcal{X}`. In the formalization this
space is represented by the type variable {anchorTerm RefinementIndicator}`β`.
The proofs that we formalize do not depend on the concrete structure of
{anchorTerm RefinementIndicator}`β` so we do not need to assume any additional
structure on it.

In the following {anchorTerm beta}`β` will always be an arbitrary type.
```anchor beta
variable {β : Type*}
```

# Refinement Indicators

First, we define a few convenient
abbreviations concerning refinement indicators in Lean.

We define the type abbreviation {anchorTerm RefinementIndicator}`RefinementIndicator`
for a function that maps from a mesh,
an element of the vector space and an element of the mesh
to a real number:
```anchor RefinementIndicator
abbrev RefinementIndicator (α : Type*) [DecidableEq α] [Lattice α] [OrderBot α] (β : Type*) :=
  Mesh α → β → α → ℝ
```
The idea is that an instance of this type should estimate for any mesh
$`\mathcal{T}` the local error an approximation $`x ∈ \mathcal{X}`
to the actual solution makes on an element $`T∈\mathcal{T}`.

Based on a refinement indicator {anchorTerm gη2}`ri` we can define
the squared global error estimator $`η^2`
as
```anchor gη2
def gη2 (ri: RefinementIndicator α β) (𝒯: Mesh α) v :=
  ∑ T ∈ 𝒯, (ri 𝒯 v T)^2
```
The name {anchorTerm gη2}`gη2` has the prefix `g` to signify that this is the global
error and the suffix `2` because it is the squared global error.

# Adaptive Algorithm

Now, we summarize all assumptions from *AoA* in the structure
{anchorTerm AdaptiveAlgorithm_1}`AdaptiveAlgorithm`.
This allows us to use an instance of {anchorTerm AdaptiveAlgorithm_1}`AdaptiveAlgorithm`
as an assumption for theorems and also to access practical lemmas and definitions
via dot access notation.

First, we define two helper functions for constants that are
calculated from other constants.
```anchor AdaptiveAlgorithm_constfuns
private noncomputable def ε_qos' (ρ_red C_rel C_red C_stab θ : ℝ) :=
  ⨆ δ > 0, (1-(1+δ)*(1-(1-ρ_red)*θ)) / (C_rel^2 * (C_red + (1+δ⁻¹)*C_stab^2))
private def C_rel' (C_Δ C_drel : ℝ) := C_Δ * C_drel
```

Then we can go ahead and start building up the structure.
```anchor AdaptiveAlgorithm_1
structure AdaptiveAlgorithm (α β: Type*) [DecidableEq α] [Lattice α] [OrderBot α] where
```

We will now go through all the fields of the {anchorTerm AdaptiveAlgorithm_1}`AdaptiveAlgorithm`
structure. Because the documentation of the formalized proofs is accompanied by
a ready-to-formalize version of the proof in regular mathematical notation, most
fields also have a typeset notation that we use in this document (and aligns with *AoA*).
We write $`\mathbb{T}` for the set of all meshes on the lattice $`\mathcal{L}`
(c.f. {ref "meshes"}[Meshes]). $`\mathcal{X}` is again the appropriate vector space for the AFEM problem,
implemented with the type {anchorTerm AdaptiveAlgorithm_1}`β`.

## Solver

We suppose that a numerical solver $`U : \mathbb{T} → \mathcal{X}` exists
```anchor AdaptiveAlgorithm_2
  -- Numerical solver --
  U : Mesh α → β
```
which approximates an unkown limit or solution $`u ∈ \mathcal{X}`:
```anchor AdaptiveAlgorithm_3
  -- Limit --
  u : β
```

## Refinement Indicator

Assume that $`η_T(\mathcal{T}, ·) : \mathcal{X} → [0,∞)` is a computable refinement indicator for
every element $`T` and mesh $`\mathcal{T}` that satisfy $`T ∈ \mathcal{T} ∈ \mathbb{T}`.
We write this in Lean as
```anchor AdaptiveAlgorithm_4
  -- Refinement indicator --
  η : RefinementIndicator α β
  hη : η ≥ 0
```
Here, we have to note that the type {anchorTerm AdaptiveAlgorithm_4}`RefinementIndicator`
we defined above is slightly inaccurate. In the informal definition
(from *AoA*), the third argument, which is
the local element $`T`, can only stem from the mesh $`\mathcal{T}` that is given as a first argument.
So actually we want to have a family of functions $`\mathcal{X} → [0,∞)` for all
combinations $`T∈\mathcal{T}∈\mathbb{T}`.

In other words, the type of the local element
argument depends on which mesh has been passed to the first argument.
So {anchorTerm AdaptiveAlgorithm_4}`η` has to be defined on many more
parameter combinations than what *AoA* prescribes. However, the formalization
will never supply a mesh $`\mathcal{T}` and an element $`S∉\mathcal{T}` that is not from this mesh to the refinement
indicator, which is why we afford this inaccuracy.


We use the notation
$$`
η^2(\mathcal{T}, v) ≔ ∑_{T∈\mathcal{T}} η_T(\mathcal{T}, v)^2
`
for the global squared error defined by {anchorTerm gη2}`gη2`.

## Error measure

We also suppose that we have an error measure $`𝕕 : \mathbb{T} × \mathcal{X} × \mathcal{X} → [0,\infty)`
and a constant $`C_Δ > 0` such that the following conditions hold:
: Non-negativity

  For all $`\mathcal{T} ∈ \mathbb{T}, v_1, v_2 ∈ 𝒳`
   $$`𝕕(\mathcal{T}, v_1, v_2) ≥ 0`

: Quasi-symmetry

  For all $`\mathcal{T} ∈ \mathbb{T}, v_1, v_2 ∈ 𝒳`
  $$`𝕕(\mathcal{T}, v_1, v_2) ≤ C_Δ 𝕕(\mathcal{T}, v_2, v_1)`

: Quasi-triangle inequality

  For all $`\mathcal{T} ∈ \mathbb{T}, v_1, v_2 ∈ 𝒳`
  $$`C_Δ^{-1} 𝕕(\mathcal{T} v_1, v_3) ≤ 𝕕(\mathcal{T}, v_1, v_2) + 𝕕(\mathcal{T}, v_2, v_3)`

In Lean we define this as
```anchor AdaptiveAlgorithm_5
  -- Error measure --
  d : Mesh α → β → β → ℝ
  C_Δ : ℝ
  hC_Δ : 0 < C_Δ
  non_neg : ∀ T v w, d T v w ≥ 0
  quasi_symmetry : ∀ T v w, d T v w ≤ C_Δ * d T w v
  quasi_triangle_ineq : ∀ T v w y, C_Δ⁻¹ * d T v y ≤ d T v w + d T w y
```

## Mesh sequence

Suppose that $`(\mathcal{T}_n)_{n∈ℕ}` is the sequence of meshes generated by
the standard AFEM algorithm (c.f. {ref "afem_alg"}[AFEM method]).
```anchor AdaptiveAlgorithm_6
  -- Triangulation sequence --
  𝒯 : ℕ → Mesh α
  h𝒯 : ∀ l, 𝒯 (Nat.succ l) ≤ 𝒯 l
```

We assume that the algorithm uses Dörfler marking with parameter $`θ ∈ (0,1)`
and $`(ℳ_n)_{n∈ℕ}` is the sequence of minimal submeshes that were selected
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

## Axioms

Now only the actual "Axioms of Adaptivity" remain.

### Stability on Non-Refined Element Domains

We start with stability (A1), which states that for some constant $`C_{\mathrm{stab}} > 0`
$$`\left|\sqrt{\sum_{T \in \mathcal{S}} η_T(\mathcal{T}'; v')^2} - \sqrt{\sum_{T \in \mathcal{S}} η_T(\mathcal{T}; v)^2}\right| ≤ C_{\mathrm{stab}} 𝕕[\mathcal{T}'; v', v]`
for all $`\mathcal{T'},\mathcal{T}∈\mathbb{T}` with $`\mathcal{T}' ≤ \mathcal{T}`, $`\mathcal{S} ⊆ \mathcal{T} ∩ \mathcal{T}'` and any $`v,v' ∈ \mathcal{X}`.

The Lean definition is
```anchor AdaptiveAlgorithm_8
  -- A1: stability on non-refined element domains --
  C_stab : ℝ
  hC_stab : C_stab > 0
  a1 : ∀ T : Mesh α, ∀ T' ≤ T, ∀ S ⊆ T ∩ T', ∀ v v',
    |√(∑ t ∈ S, η T' v' t ^ 2) - √(∑ t ∈ S, η T v t ^ 2)| ≤ C_stab * d T' v' v
```

### Reduction Property on Refined Elements

Reduction (A2) requires that for some constants $`0 < ρ_{\mathrm{red}} < 1` and $`C_{\mathrm{red}} > 0`
$$`∑_{T ∈ \mathcal{T'} \setminus \mathcal{T}} η_T(\mathcal{T'}; U(\mathcal{T'}))^2 ≤ ρ_{\mathrm{red}} ∑_{T ∈ \mathcal{T} \setminus \mathcal{T'}} η_T(\mathcal{T}, U(T))^2 + C_{\mathrm{red}} 𝕕[\mathcal{T'}, U(\mathcal{T'}), U(\mathcal{T})]^2.`
for all $`\mathcal{T'},\mathcal{T}∈\mathbb{T}` with $`\mathcal{T'} ≤ \mathcal{T}`.

In Lean this translates as
```anchor AdaptiveAlgorithm_9
  -- A2: reduction property on refined elements --
  ρ_red : ℝ
  hρ_red : ρ_red ∈ Set.Ioo 0 1
  C_red : ℝ
  hC_red : 0 < C_red
  a2 : ∀ T : Mesh α, ∀ T' ≤ T,
    ∑ t ∈ T' \ T, η T' (U T') t ^ 2 ≤ ρ_red * ∑ t ∈ T \ T', η T (U T) t ^ 2 + C_red * d T' (U T') (U T) ^ 2
```

### Reliability

Because we do not formalize Lemma 3.4 from *AoA* which shows reliability
from the _dicrete reliability_ (A4) axiom and an additional condition on the
error measure, we directly assume reliability as an axiom instead of discrete reliability.

Reliability states that for some $`C_{\mathrm{drel}} > 0` with $`C_{\mathrm{rel}} \coloneqq C_{Δ}C_{\mathrm{drel}}`
it holds that
$$`𝕕(\mathcal{T}, u, U(\mathcal{T})) ≤ C_{\mathrm{rel}} η(\mathcal{T}, U(\mathcal{T}))`
for all $`\mathcal{T} ∈ \mathbb{T}`.

In Lean this is written as
```anchor AdaptiveAlgorithm_10
  -- A4: reliability --
  C_drel : ℝ
  hC_drel : 0 < C_drel
  -- This is a result from A4 and the compatibility condition of the measure d (Lemma 3.4).
  -- Because this proof is not formalized we assume this result instead of A4.
  reliability' : ∀ T, d T u (U T) ≤ C_rel' C_Δ C_drel * √(gη2 η T (U T))
```
where we use the helper function {anchorTerm AdaptiveAlgorithm_10}`C_rel'`.

### General quasi-orthogonality

Finally, general quasi-orthogonality (A3) states that there exist constants
$`C_{\mathrm{qo}} ≥ 1` and
$$`0 ≤ ε_{qo} < ε^*_{\mathrm{qo}}(θ) \coloneqq \sup_{δ > 0} \frac{1-(1+δ)(1-(1-ρ_{\mathrm{red}})θ)}{C_{\mathrm{rel}}^2 (C_{\mathrm{red}} + (1+δ⁻¹)C_{\mathrm{stab}}^2)}`
such that for all $`l,N∈ℕ` with $`N≥l`
$$`∑_{k=l}^{N} \left(𝕕(\mathcal{T}_{k+1}, U(\mathcal{T}_{k+1}), U(\mathcal{T}_k))^2 - ε_{qo} 𝕕(\mathcal{T}_k, u, U(\mathcal{T}_k))^2\right) ≤ C_{\mathrm{qo}} η^2(\mathcal{T}_l, U(\mathcal{T}_l))`
holds.

In Lean we write this down as
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
where we use the helper function {anchorTerm AdaptiveAlgorithm_11}`ε_qos'`
to write down the supremum thats actually behind $`ε^*_{\mathrm{qo}}`.
Note that because sums with a starting index are usually shifted to start
at zero in Lean we don't need the $`N≥l` part of the axiom. Our {anchorTerm AdaptiveAlgorithm_11}`n`
is just the number of summands ({anchorTerm AdaptiveAlgorithm_11}`range n` gives
the range $`[0,n)∩ℕ`).

## Definitions for AdaptiveAlgorithm
%%%
tag := "adaptive_alg_defs"
%%%

Important additional definitions that appear throughout the formalization
are the abbreviations for the term $`η^2(\mathcal{T}_l, U(\mathcal{T}_l))`.

```anchor seq_abbrev
def gη2_seq l := gη2 alg.η (alg.𝒯 <| l) (alg.U <| alg.𝒯 <| l)
noncomputable def nn_gη_seq n := NNReal.sqrt (alg.gη2_seq n).toNNReal
```

The second line is a version that maps to the non-negative Reals and gives $`η`
as opposed to $`η^2`. It will be used for parts of the proofs that have been
formulated for the `NNReal` type instead of `ℝ`.

Also we define nicer ways to access the constants $`ε^*_{\mathrm{qo}}` and
$`C_{\mathrm{rel}}` as well a modified proof of reliability that
uses the newly defined abbreviation for $`C_{\mathrm{rel}}`:
```anchor AdaptiveAlgorithm_redefs
-- redefinitions for general field access
def C_rel := C_rel' alg.C_Δ alg.C_drel
noncomputable def ε_qos := ε_qos' alg.ρ_red alg.C_rel alg.C_red alg.C_stab alg.θ
lemma reliability : ∀ T, alg.d T alg.u (alg.U T) ≤ alg.C_rel * √(gη2 alg.η T (alg.U T)) :=
  alg.reliability'
```
