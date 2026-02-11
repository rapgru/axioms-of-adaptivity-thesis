import VersoManual

import Docs.Papers

import Docs.Lean
import Docs.Meshes
import Docs.AFEM
import Docs.AbstractSetting
import Docs.Lemma47
import Docs.Lemma49
import Docs.Cor48
import Docs.Prop410
import Docs.Conclusio

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

open Docs

set_option pp.rawOnError true

#doc (Manual) "Formalizing Optimal Convergence of Adaptive FEM in Lean" =>
%%%
authors := ["Raphael Gruber"]
shortTitle := "Formalizing Optimal Convergence of Adaptive FEM in Lean"
%%%

This document serves as my bachelor thesis in mathematics at TU Wien.
It documents how I formalized parts of the optimality theory of adaptive finite element methods in Lean based
on the paper _Axioms of adaptivity_{citep axioms}[] by Carstensen, Feischl, Page, and Praetorius.
We will refer to this article with the shorthand *AoA* in the following.

The initial chapters provide a brief introduction to theorem proving in Lean 4
and adaptive finite element methods. The remainder of the document focuses on the
Lean formalization of the assumptions and proofs presented in the referenced paper.
Familiarity with the finite element method is assumed.

{include 1 Docs.Lean}

{include 1 Docs.Meshes}

{include 1 Docs.AFEM}

{include 1 Docs.AbstractSetting}

{include 1 Docs.Lemma47}

{include 1 Docs.Cor48}

{include 1 Docs.Lemma49}

{include 1 Docs.Prop410}

{include 1 Docs.Conclusio}
