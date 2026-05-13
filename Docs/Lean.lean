import VersoManual

import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Docs

set_option pp.rawOnError true

#doc (Manual) "Formal Verification" =>
%%%
htmlSplit := .never
%%%

In this thesis, we will use the Lean _theorem prover_ or _proof assistant_, to
formally verify mathematical theorems from *AoA* by providing it with
formalized versions of the theorem statements and proofs.
This chapter will elaborate on the idea behind this venture.

Modern logic has shown that very slim logical calculi exists that are
still powerful enough to prove most (i.e. all provable) theorems.
Take for example the Hilbert calculus:
A formal proof in this system is a sequence of formulas, where each formula is either
an axiom or follows from previous formulas by modus ponens.
So the only inference rule is modus ponens, which can be written as
$$`
\frac{A \to B \quad A}{B}
`
which means that if we have a formula of the form $`A \to B` and a formula $`A`, then we can infer $`B`.
This is already a very powerful system that has been shown to be able to prove any
true statement in first-order logic.

The key here is the simplicity of these systems: By reducing proofs to this level, computers
get a chance at helping with both finding and verifying mathematical proofs.
This is exactly where proof assistants come into play. They
allow us to write proofs in a formal language that can be checked for correctness
by a computer.

In the field of automated reasoning, there are two terms associated
with such computer systems:
: Automated theorem proving

  concentrates on the proof-finding aspect. Given that mathematics is mostly concerned with
  finding proofs, this can obviously be helpful.

  Looking back at our example, when using the Hilbert calculus, the method of resolution is
  a relatively simple algorithm that can be used to automatically find proofs in this system
  (see {citet leitsch1997resolution}[] for a standard treatment).
  It is a complete method for first-order logic, which means that if a formula is provable,
  the algorithm will find a proof for it.

: Interactive theorem proving

  concerns _proof assistants_ that help a human user to write and verify formal
  proofs in a suitable
  calculus. Accepting only the validity of the calculus and that the software
  is correctly implemented, any statement proven correct in a proof assistant
  has to be, without any reason for objection, true. Errors in a proof
  can remain unnoticed even if many mathematicians reviewed it. In this view,
  interactive proof systems are helpful to detect and prevent such mistakes.
  (Take {citet hales2017proof}[] as an example where a major error was
  discovered using a proof assistant)

Starting from around 1967 the first interactive theorem provers where developed
and over the course of the years many notable theorems were formally
verified using such tools. Examples of proof assistants are
Isabelle, HOL Light, Lean, Rocq, Metamath and Mizar.

# Reasons for the Formalization of Proofs

{citep avigad2024formal}[] gives eighteen ways how formal computer systems can
contribute to the field of mathematics.
The most notable are that formalizations of theorems in a proof assistant
guarantee correctness of the proofs and can be used to discover mistakes.
However, there are many more benefits to a formal proof:
- We gain insight into why a proof works and might find new approaches
  because of the level of detail a formal proof requires.
- It allows us to refactor proofs. When we e.g. change the assumptions
  of a theorem in a proof assistant it will instantly tell you where the proof now breaks.
  Shuffling around a proof and checking if it is still valid is pretty much effortless
  with a formal proof.
- They can be used as a collaboration tool between mathematicians.
  Proving a theorem as a large community effort is possible with
  standard open-source practice that is known from software engineering.
- In computational sciences we can use formal verication systems to prove
  correctness of imperative programs. In numerics, the output of a
  computer program is often used as evidence, which means that we
  need to be very sure that the program does what it is intended to do.
  Using tools like Lean we could give very strong correctness guarantees
  about such computer programs.
- Combinations of AI systems like LLMs and theorem provers show very promising
  results at mathematical tasks. Take for example the silver medal performance
  at the 2024 IMO of an AI system by Google DeepMind {citep hubert2025olympiad}[]

# Lean4

Lean is an open-source proof assistant and programming language developed primarily
by Leonardo de Moura. Starting as a project at Microsoft Research in 2013, Lean has
is now mainly maintained by the non-profit organisation Lean FRO LLC and the Lean community.

Lean aims to unify interactive and automated theorem proving.
It is based on the _Calculus of Constructions with inductive types_, which can be
used as a foundation for mathematics, and allows
to write proofs in this system in a highly interactive and
convenient way. At the same time, the language includes automations that
help the user with finding steps of a proof.

## Mathlib4
%%%
tag := "mathlib"
%%%

Writing mathematical proofs in Lean with reasonable effort is possible
due to the user-maintained mathematic library [mathlib4](https://github.com/leanprover-community/mathlib4).
It contains a large collection of predefined objects and theorems
that can be used to base own definitions and proofs on. In the
context of numerics preexisting building blocks would be functions, limits (topology),
finite sums, series and their accompanying theorems. An example
of such a basic theorem is that the sum of two convergent sequences converges to the sum of the limits.
Having this framework considerably shortens the formalized proofs in Lean. Central maintainance of the library ensures
that it is of high quality and its widespread use guarantees that
basing own code on the work of others does not lead to compatibility issues.
