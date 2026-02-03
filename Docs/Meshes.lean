import VersoManual
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Docs

set_option pp.rawOnError true
set_option verso.exampleProject "../axioms_of_adaptivity"
-- TODO structure fix, make this lean file only about meshes or put
-- all definitions in here?
set_option verso.exampleModule "AxiomsOfAdaptivity.Mesh"

#doc (Manual) "Meshes" =>
%%%
htmlSplit := .never
%%%

At the core of the adaptive finite element method are
space discretizations of the problems domain. We call a space discretization
*mesh*. Take as typical example of a mesh the following 2D-triangulation of an L-shaped domain.

![Triangulation of an L-Shaped domain in 2D](../static_files/afem/mesh_0_small.png)

*AoA* treats meshes very intuitively because the reader has sufficient understanding
of the terms "triangulation" / "refinement" and their properties.
For our formalization this is not explicit enough, we need to
precisely define meshes and refinements in Lean, taking care to be as general
as possible.

We will present both a mathematically typeset definition and the Lean implementation
of meshes for two reasons:
- The definition of meshes is original to this formalization and
cannot be looked up in *AoA* and
- to highlight how the two versions translate.

# Mathematical definition

The idea for the definition is that a mesh consists of elements that form
the problems domain when seen as a collection. So we want a mesh
to be a finite set of "elements". In two dimensions
triangles could be such "elements" making up a domain.
Then the objective is to find an appropriate abstraction for the "elements"
that make up a mesh.

The natural first step is to assume that our elements are
sets (usually subsets of $`ℝ^d`). As we will see
intersection and union can be used to define a very intuitive refinement relation.
The second step to our definition is to
abstract away the concrete versions of the set operations and generalise using
an arbitrary lattice structure (this choice is motivated
by the Lean implemenetation, c.f. {ref "sets_vs_lattice"}[Sets vs. Lattice]).
Taking these steps, the definition of a mesh reads as follows:

> *Definition (Mesh):* Let $`(X, ⊔, ⊓, ⊥)` be a lattice that is bounded below by $`⊥`. A finite subset
  $`M ⊆ X` is called a _mesh_ (in $`X`) iff:
  - The elements of $`M` are pairwise disjoint, i.e.
    $$`∀ s, t ∈ M, s ≠ t → s ⊓ t = ⊥ .`
  - The bottom element is not contained in $`M`, i.e. $`⊥ ∉ M`.

Fix for the remaining section the lattice $`(X, ⊔, ⊓, ⊥)`. We go ahead and
define the partition relation as

> *Definition (Partition):* A mesh $`M` _partitions_ an element $`t ∈ X` (denoted as $`M ↪ t`) iff
  $$`⨆_{m ∈ M} m = t.`

And finally we can define the refimenent relation on all meshes as follows:

> *Definition (Refinement):* Let $`A` and $`B` be two meshes. $`A` _refines_ $`B` (denoted as $`A≤B`) iff
  for any $`t ∈ B` there exists a mesh $`M ⊆ A` such that $`M ↪ t`.

In other words, A is a refinement of B when every element of B can be
constructed (in the $`⊔` sense) from elements of A.
As we will see this definition will allow us to show that the set
of all meshes in $`X` together with the refinement relation $`≤` forms
a partial order.

# Lean definition

Now let's see how the definition translates to Lean. We will use
the `Finset` type from Lean's mathlib4 to represent finite sets.
Because finsets need a type for its elements, we need to fix a type $`α` and assume that it has the
lattice structure we need.

```anchor alpha
variable {α: Type*} [Lattice α] [OrderBot α]
```

This instruction adds {anchorTerm alpha}`α` implicitly
to all definitions that follow. Next we define abbreviations
for the two properties a mesh has to fulfil:

```anchor Mesh_Props
def disjoint (m : Finset α): Prop := Set.Pairwise (m : Set α) Disjoint
def nobot (m : Finset α) : Prop := ⊥ ∉ m
```

Because the {anchorTerm Mesh_Props}`Set.Pairwise` property is defined on
{anchorTerm Mesh_Props}`Set` we need to coerce
{anchorTerm Mesh_Props}`m` to the type {anchorTerm Mesh_Props}`Set α`.
We can now go ahead and define the type {anchorTerm Mesh}`Mesh` as
a subtype of {anchorTerm Mesh}`Finset α` with the {anchorTerm Mesh_Props}`disjoint` and
{anchorTerm Mesh_Props}`nobot` properties.
This means that instances of {anchorTerm Mesh}`Mesh` are tuples
that have a {anchorTerm Mesh}`Finset` in their first component and
a proof that the finset satisfies the two mesh properties in their second
component:

```anchor Mesh
abbrev Mesh (α: Type*) [Lattice α] [OrderBot α] :=
  { x : Finset α // disjoint x ∧ nobot x }
```

Just as in the mathematical definition we can now define the partition relation
with

```anchor partitions
def partitions (T : Mesh α) (t : α) : Prop :=
  Finset.sup T id = t
infix:50 " ↪ " => partitions
```

This also defines the infix notation `↪` so we can
write `M ↪ t` for `partitions M t` in Lean code. Finally we define the
refines relation as

```anchor refines
def refines (A B : Mesh α) : Prop :=
  ∀ t ∈ B, ∃ M ⊆ A, M ↪ t
```

Note that here the existential
quantifier ranges over the type {anchorTerm Mesh}`Mesh` because Lean can
infer the type from the use of {anchorTerm partitions}`partitions`
(confirm by hovering over {anchorTerm refines}`M`).

We see that the mathematical definition translates
to the Lean version pretty much directly. Especially with
use of the mathematical special characters, the properties we defined
are nearly identical to the definition from the previous section, just
a bit more condensed.
The only notable difference is that Lean revolves around types, while we used
the set $`X` to describe the lattice in the written version. This is due to
the type theoretical foundation of Lean.

:::paragraph
> A subset $`M ⊆ X` is called a mesh iff ...

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
multiset with a proof that it does not contain duplicates.
So for example the construction of a union $`A∪B` of two `Finset`s has to check
the elements of $`A` and $`B` for duplicates. This check requires that the equality
on {anchorTerm Mesh}`α` is decidable.

This is not the case for sets however because of the constructive nature of Lean.
By default the axioms Lean is based on do not imply the law of excluded middle.
So it is not guaranteed that for two arbitrary sets $`A, B` we can always
find a proof of $`A = B` or $`A ≠ B`. Using, for example, the subsets of
$`ℝ^d` as {anchorTerm Mesh}`α` would not give us the partial order result.

Circumventing this problem is possible by switching to classical logic
using the `open Classical` instruction. However, given that AFEM is
an algorithmic method, it is preferable to stay in constructive logic
where possible.
To leave this choice open, we abstract away from sets and use an arbitrary lattice structure
on {anchorTerm Mesh}`α`. This way we can assume that the operations we need are available and
just pose the decidability of equality on {anchorTerm Mesh}`α` as an assumption.

Because sets are a special case of a lattice, we can still use sets as {anchorTerm Mesh}`α` if we
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
noncomputable def example_union := real_line_singleton_mesh ∩ real_line_singleton_mesh
```
Without the `open Classical` instruction that allows the law of excluded middle, we
would get an error regarding the intersection operation being unable to decide
equality on sets.
