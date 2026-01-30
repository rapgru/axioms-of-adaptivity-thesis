import VersoManual
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Docs

set_option pp.rawOnError true
set_option verso.exampleProject "../axioms_of_adaptivity"
set_option verso.exampleModule "AxiomsOfAdaptivity.Basics"

#doc (Manual) "Definitions" =>
%%%
htmlSplit := .never
%%%

In this chapter, we formalize the definitions and notation used in the paper
_Axioms of adaptivity_{citep axioms}[].

# Meshes

:::paragraph
A mesh is formally represented as a finite set of elements that makes up the domain.
The definition reads as follows:

```anchor Mesh
abbrev Mesh (α : Type*) := Finset α
```
:::

:::paragraph
To give these elements of arbitrary type {anchorTerm Mesh}`α` some structure, we
require {anchorTerm Mesh}`α` to have the type class
{anchorTerm Partitionable}`Partitionable`:

```anchor Partitionable
class Partitionable (α : Type _) [DecidableEq α] where
  part : Finset α → α → Prop
  self_part : ∀ t : α, part {t} t
  union_part :
    ∀ {s : α} (m : Finset α) (ms : α → Finset α),
      (∀ t ∈ m, part (ms t) t) ∧ part m s → part (m.biUnion ms) s
  unique_part :
    ∀ {s : α} (p m : Finset α),
      p ⊆ m ∧ part p s → p = {s}
  unique_element : ∀ (s t : α),
      part {s} t → t = s
```

It encodes the ability of elements to form larger elements by
unification of smaller elements. An example implementation could be to let
{anchorTerm Mesh}`α` the type `Triangle`, where each triangle is represented
by the coordinates of its three vertices.
:::

## Refinements

Now that we have defined meshes, we can define refinements of meshes.

:::paragraph
A refinement of a mesh is another mesh where each element of the original mesh
is partitioned into elements of the refinement.
This is formalized using the following property:

```anchor refines
def refines (A B : Mesh α) : Prop :=
  ∀ t ∈ B, ∃ ts ⊆ A, ts ⇒ t
```

Here, the notation `ts ⇒ t` means that the elements in the finset `ts`
partition the element `t`, i.e., `part ts t` holds.
:::

:::paragraph

Using this definition, the a {anchorTerm Mesh}`Mesh` with a {anchorTerm Partitionable}`Partitionable` type
{anchorTerm Mesh}`α` is partially ordered by the {anchorTerm refines}`refines` relation.

For example the following proof shows that refinement is transitive:

```anchor refines_trans
theorem refines_trans (X Y Z : Mesh α) (hxy: refines X Y) (hyz: refines Y Z) :
    refines X Z := by {
  intros t ht
  rcases hyz t ht with ⟨S,hS,hU⟩
  choose f hf using fun t ht => hxy t (hS ht)

  -- trick: use empty set when element is not in S because biUnion does
  -- not supply membership proof
  let U := S.biUnion fun x =>
    if hx : x ∈ S then f x hx else ∅
  use U

  constructor
  · apply Finset.biUnion_subset.mpr
    exact fun _ hs ↦ by simp [hs, hf]
  · apply Partitionable.union_part
    exact ⟨fun _ hs ↦ by simp [hs, hf], hU⟩
}
```
:::
