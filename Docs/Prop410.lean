import VersoManual
import Docs.Papers

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External
open Docs

set_option pp.rawOnError true
set_option verso.exampleProject "../axioms_of_adaptivity"
set_option verso.exampleModule "AxiomsOfAdaptivity.Basics"
set_option maxHeartbeats 20000000

#doc (Manual) "Summability" =>
%%%
htmlSplit := .never
%%%

This chapter formalizes the proof of Proposition 4.10 from *AoA* which reads as

> *Proposition 4.10*: ABC
