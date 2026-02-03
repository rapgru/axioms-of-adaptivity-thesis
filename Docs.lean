import VersoManual

import Docs.Papers
import Docs.DocFeatures
import Docs.AFEM
import Docs.Lean
import Docs.Conclusio
import Docs.AbstractSetting
import Docs.Meshes

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

open Docs

set_option pp.rawOnError true

-- This is the source of code examples to be shown in the document. It should be relative to the
-- current Lake workspace. One good way to set up the files is in a Git repository that contains one
-- Lake package for example code and another for the docs, as sibling directories.
set_option verso.exampleProject "../axioms_of_adaptivity"

-- This is the module that will be consulted for example code. It can be overridden using the
-- `(module := ...)` argument to most elements that show code.
set_option verso.exampleModule "AxiomsOfAdaptivity.Basics"

#doc (Manual) "Formalizing Optimal Convergence of Adaptive FEM in Lean" =>
%%%
authors := ["Raphael Gruber"]
shortTitle := "Formalizing Optimal Convergence of Adaptive FEM in Lean"
%%%

This document serves as my bachelor thesis in mathematics at TU Wien.
It documents how I formalized parts of the optimality theory of adaptive finite element methods in Lean based
on the paper _Axioms of adaptivity_{citep axioms}[] by Carstensen, Feischl, Page, and Praetorius.
We will refer to this paper as *AoA* in the following.

The initial chapters provide a brief introduction to theorem proving in Lean 4
and adaptive finite element methods. The remainder of the document focuses on the
Lean formalization of the assumptions and proofs presented in the referenced paper.
Familiarity with the finite element method is assumed.

-- TODO could collapse Lean and AFEM into an introduction
{include 1 Docs.Lean}

{include 1 Docs.AFEM}

{include 1 Docs.Meshes}

{include 1 Docs.AbstractSetting}

{include 1 Docs.Conclusio}
