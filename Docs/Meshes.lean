import VersoManual
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Docs

set_option pp.rawOnError true
set_option verso.exampleProject "../axioms_of_adaptivity"
set_option verso.exampleModule "AxiomsOfAdaptivity.Mesh"
set_option maxHeartbeats 20000000

#doc (Manual) "Meshes" =>
%%%
htmlSplit := .never
tag := "meshes"
%%%

At the core of the adaptive finite element method are
space discretizations of the problems domain. We call a space discretization
*mesh*. Take as typical example of a mesh the following 2D-triangulation of an L-shaped domain.

![Triangulation of an L-Shaped domain in 2D](static_files/afem/mesh_0_small.png)

In this section we will start with the formalization of meshes in Lean.
After we have an idea
of what a mesh is, the {ref "afem"}[next chapter] will then give an overview of
the adaptive finite element method using the definitions from this chapter.

*AoA* treats meshes very intuitively because the reader has sufficient understanding
of the terms "triangulation" / "refinement" and their properties.
For our formalization this is not explicit enough, we need to
precisely define meshes and refinements in Lean, taking care to be as general
as possible.

We will present both a mathematically typeset definition and the Lean implementation
of meshes. This has two reasons:
- The definition of meshes is original to this formalization and
- to highlight how the two versions translate.

# Informal definition

The idea is that a mesh consists of elements that form
the problems domain when seen as a collection. So we want a mesh
to be a finite set of "elements". In two dimensions such "elements"
making up a domain could be triangles.
The objective is to find an appropriate abstraction for the "elements"
that make up a mesh.

The natural first step is to assume that our elements are
sets (usually subsets of $`ℝ^d`). As we will see
intersection and union can be used to define a very intuitive refinement relation.
The second step we take is
abstracting away the set operations and generalising using
an arbitrary lattice structure (this choice is motivated
by the Lean implemenetation, c.f. {ref "sets_vs_lattice"}[Sets vs. Lattice]).
Taking these steps, the definition of a mesh reads as follows:

> *Definition (Mesh):* Let $`(\mathcal{L}, ⊔, ⊓, ⊥)` be a lattice that is bounded below by $`⊥`. A finite subset
  $`\mathcal{T} ⊆ \mathcal{L}` is called a _mesh_ (in $`\mathcal{L}`) iff:
  - The elements of $`\mathcal{T}` are pairwise disjoint, i.e.
    $$`∀ S, T ∈ \mathcal{T}:\quad S ≠ T → S ⊓ T = ⊥ .`
  - The bottom element is not contained in $`\mathcal{T}`, i.e. $$`⊥ ∉ \mathcal{T}.`

For the remainder of the thesis we fix a lattice $`(\mathcal{L}, ⊔, ⊓, ⊥)`
and define $`\mathbb{T}` to be the set of all meshes (on $`\mathcal{L}`).

We go ahead and define the partition relation as
> *Definition (Partition):* A mesh $`\mathcal{T}` _partitions_ an element $`S ∈ \mathcal{L}` (denoted as $`\mathcal{T} ↪ T`) iff
  $$`⨆_{T ∈ \mathcal{T}} T = S.`

Finally, we can define the refinement relation on all meshes as follows:
> *Definition (Refinement):* Let $`\mathcal{T'}` and $`\mathcal{T}` be
  two meshes. $`\mathcal{T'}` _refines_ $`\mathcal{T}`
  (denoted as $`\mathcal{T'}≤\mathcal{T}`) iff
  for any $`T ∈ \mathcal{T}` there exists a mesh $`\mathcal{M} ⊆ \mathcal{T'}` such that $`\mathcal{M} ↪ T`.

In other words, $`\mathcal{T'}` is a refinement of $`\mathcal{T}` when every element of $`\mathcal{T}` can be
constructed (in the $`⊔` sense) from elements of $`\mathcal{T'}`.
This definition will allow us to show that $`\mathbb{T}`
together with the refinement relation $`≤` forms
a partial order.

# Lean definition

Now let's see how the definition translates to Lean. We will use
the `Finset` type from Lean's mathlib4 to represent finite sets.
Because a `Finset` needs a type for its elements, we need to fix a type
{anchorTerm alpha}`α` and assume that it has the
lattice structure we need.

```anchor alpha
variable {α: Type*} [Lattice α] [OrderBot α]
```

This instruction adds {anchorTerm alpha}`α` implicitly
to all definitions that follow. Next we define abbreviations
for the two properties a mesh has to fulfil:

```anchor Mesh_Props
def disjoint (𝒯 : Finset α): Prop := Set.Pairwise (𝒯 : Set α) Disjoint
def nobot (𝒯 : Finset α) : Prop := ⊥ ∉ 𝒯
```

Because the {anchorTerm Mesh_Props}`Set.Pairwise` property is defined on
{anchorTerm Mesh_Props}`Set` we need to coerce
{anchorTerm Mesh_Props}`𝒯` to the type {anchorTerm Mesh_Props}`Set α`.
We can now go ahead and define the type {anchorTerm Mesh}`Mesh` as
a subtype of {anchorTerm Mesh}`Finset α` with the {anchorTerm Mesh_Props}`disjoint` and
{anchorTerm Mesh_Props}`nobot` properties.
This means that instances of {anchorTerm Mesh}`Mesh` are tuples
that have a {anchorTerm Mesh}`Finset` in their first component and
a proof that the finset satisfies the two mesh properties in their second
component:

```anchor Mesh
abbrev Mesh (α: Type*) [Lattice α] [OrderBot α] :=
  { 𝒯 : Finset α // disjoint 𝒯 ∧ nobot 𝒯 }
```

Just as in the mathematical definition we can now define the partition relation
with

```anchor partitions
def partitions (𝒯 : Mesh α) (S : α) : Prop :=
  Finset.sup 𝒯 id = S
infix:50 " ↪ " => partitions
```

This also defines the infix notation `↪` so we can
write `ℳ ↪ S` for `partitions ℳ S` in Lean code. Finally we define the
refines relation as

```anchor refines
def refines (𝒯' 𝒯 : Mesh α) : Prop :=
  ∀ T ∈ 𝒯, ∃ ℳ ⊆ 𝒯', ℳ ↪ T
```

Note that here the existential
quantifier ranges over the type {anchorTerm Mesh}`Mesh` because Lean can
infer the type from the use of {anchorTerm partitions}`partitions`
(confirm by hovering over {anchorTerm refines}`ℳ`).

We see that the mathematical definition translates
to the Lean version pretty much directly. Using the mathematical special characters
that Lean understands, the properties we defined
are nearly identical to the definition from the previous section, just
a bit more condensed.
The only notable difference is that Lean revolves around types, while we used
the set $`\mathcal{L}` to describe the lattice in the written version. This is due to
the type theoretical foundation of Lean.

:::paragraph
> A subset $`\mathcal{T} ⊆ \mathcal{L}` is called a mesh iff ...

translates to the creation of a new type {anchorTerm Mesh}`Mesh` that is
more or less a {anchorTerm Mesh}`Finset α` where the arbitrary type
{anchorTerm Mesh}`α` has to have an instance of the typeclass `Lattice` and
`OrderBot`.
:::

## Sets vs. Lattice
%%%
tag := "sets_vs_lattice"
%%%

The use of an arbitrary lattice instead of Sets is due to the constructive
nature of Lean:
To show that the set of all meshes with the refinement relation forms a partial order,
we need the additional assumption `[DecidableEq α]` on {anchorTerm Mesh}`α`.
The same is true for other proofs throughout the formalization.

The reason behind this is that the `Finset` type is just a
multiset combined with a proof that it does not contain duplicates.
So for example the construction of a union $`A∪B` of two `Finset`s requires to check
the elements of $`A` and $`B` for duplicates. To carry out this check, equality
on {anchorTerm Mesh}`α` has to be decidable.

Because of the constructive nature of Lean, (infinite) sets do not fulfil decidability
equality.
By default, the axioms Lean is based on do not imply the law of excluded middle.
So it is not guaranteed that we can always
find a proof of $`A = B` or $`A ≠ B` for two arbitrary sets $`A, B`.
Using, e.g., the subsets of $`ℝ^d` as {anchorTerm Mesh}`α` would not
give us the partial order result.

Circumventing this problem is possible by switching to classical logic
using the `open Classical` instruction. However, given that AFEM is
an algorithmic method, it is preferable to stay in constructive logic
when possible.
To leave this choice open, we abstract away from sets and use an arbitrary
lattice structure
on {anchorTerm Mesh}`α`. This way we can assume that the operations we need are
available and
just pose the decidability of equality on {anchorTerm Mesh}`α` as an assumption.

Polygons are an example of a lattice that
is bounded below when we include an "empty polygon". The intersection of
two finite polygons is also a polygon and the same holds for the union, given
that we allow disconnected polygons. It is a sublattice of the sets on $`ℝ^2`.
This type can be implemented in a way such that equality is algorithmically
decidable (e.g. by storing the points that make up the polygon).

Because sets are a special case of a lattice, we can still use sets as
the arbitrary lattice {anchorTerm Mesh}`α` if we
want to. For example, we can define the mesh $`\{ℝ\}` on the subsets of $`ℝ`
```anchor Mesh_Set_Example
def real_line_singleton_mesh : Mesh (Set ℝ) :=
  singletonMesh Set.univ (by
    simp only [
      Set.bot_eq_empty,
      ne_eq,
      Set.univ_eq_empty_iff,
      not_isEmpty_of_nonempty,
      not_false_eq_true
    ]
  )
```
supplying a proof that the set $`ℝ` is non-empty. The operations and theorems
that need decidable equality can be used by adding the `open Classical` instruction:
```anchor Mesh_Classical
open Classical
noncomputable def example_union :=
  real_line_singleton_mesh ∩ real_line_singleton_mesh
```
Without the `open Classical` instruction that allows the law of excluded middle, we
would get an error regarding the intersection operation being unable to decide
equality on sets.

# Partial Order

With these definitions the structure $`(\mathbb{T}, ≤)` forms a partial order.
We will omit the proof here, it is done in Lean and can be read through in the
{ref "code"}[Lean repository]. The important part is that we can add
typeclass instances for the typeclasses `LE`, `LT` and `PartialOrder` to
the `Mesh` type:
```anchor Mesh_partialorder
instance : LE (Mesh α) := ⟨refines⟩
instance : LT (Mesh α) := ⟨fun f g => f ≤ g ∧ f ≠ g⟩

instance Mesh.partialOrder [DecidableEq α]: PartialOrder (Mesh α) where
  le := (· ≤ ·)
  lt := (· < ·)
  le_antisymm := refines_antisymm
  lt_iff_le_not_le a b := by
    constructor
    · intros h
      refine ⟨h.1, ?_⟩
      by_contra h₂
      have hc₁ := refines_antisymm a b h.1 h₂
      have hc₂ := h.2
      contradiction
    · intros h
      refine ⟨h.1, ?_⟩
      by_contra h₂
      rw [← h₂] at h
      rcases h with ⟨hc₁, hc₂⟩
      contradiction
  le_refl M t h := by
    use (singletonMesh t (mesh_mem_not_bot h))
    constructor
    · apply Finset.singleton_subset_set_iff.mpr h
    · unfold partitions
      simp only [Finset.sup_singleton, id_eq]
  le_trans := refines_trans
```

This allows us to write `∀ T' ≤ T, <..>` in Lean when
we want to universally quantify over all refinements `T'` of a mesh `T`.
