/-
Copyright (c) 2024-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import Std.Data.HashMap
import VersoManual

import Docs

open Verso Doc
open Verso.Genre Manual

open Std (HashMap)

open Docs

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraFiles := [("static_files", "static_files")]
  extraCss := [":root { --verso-code-keyword-color: #D32F2F; --verso-code-const-color: #6f42c1; }"]

def main := manualMain (%doc Docs) (config := config)
