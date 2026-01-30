import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Theorem Proving in Lean 4" =>
%%%
htmlSplit := .never
%%%

-- 1) Was ist Lean, warum verwendet man Theorem Proofer.

Lean is an open-source proof assistant and programming language developed primarily
by Leonardo de Moura. Starting as a project at Microsoft Research in 2013, Lean has
is now mainly maintained by the Lean community and the non-profit organisation Lean FRO LLC.
The way in which Lean is used in this thesis is as a _theorem prover_ or _proof assistant_.
This means that users can formally verify mathematical theorems by supplying
a statement and a proof in the Lean language.

The developments in logic show that there are very slim logical calculi that are
still powerful enough to prove most theorems. The key here is the simplicity
of these systems. For example, Hilbert calculus allows only modus ponens
as an inference rule but can still prove any true statement in propositional logic.
By reducing proofs to this level, computers get a chance of helping with
both finding and verifying mathematical proofs.

There are two terms associated with such computer systems: _Automated theorem proving_
concentrates on the proof-finding aspect. Looking back to our example,
when using a Hilbert calculus, the method of resolution can be used to
automatically find proofs. Given that mathematics is mostly concerned with
finding proofs, this can obviously be helpful. _Interactive theorem proving_ concerns
proof assistants that help a human user to write and verify formal proofs in a suitable
calculus. Accepting only the validity of the calculus and that the software
is correctly implemented, any statement proven correct in a proof assistant
has to be, without any reason for objection, true. As history has shown,
human errors in proofs can remain unnoticed for a long time. In this view,
interactive proof systems are helpful to detect and prevent such mistakes.

Lean aims to unify interactive and automated theorem proving.
It is based on the _Calculus of Constructions with inductive types_, which can be
used as a foundation for mathematics, and allows
to write proofs in this system in a highly interactive and
convenient way. At the same time, the language includes automations that
help the user with finding steps of a proof.
