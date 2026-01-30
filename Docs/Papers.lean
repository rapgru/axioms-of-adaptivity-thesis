import VersoManual
open Verso.Genre.Manual

namespace Docs


-- Here, `inlines!` is a macro that parses a string constant into Verso inline elements
def someThesis : Thesis where
  title := inlines!"A Great Thesis"
  author := inlines!"A. Great Student"
  year := 2025
  university := inlines!"A University"
  degree := inlines!"Something"

def somePaper : InProceedings where
  title := inlines!"Grommulation of Flying Lambdas"
  authors := #[inlines!"A. Great Student"]
  year := 2025
  booktitle := inlines!"Proceedings of the Best Conference Ever"

def someArXiv : ArXiv where
  title := inlines!"Grommulation of Flying Lambdas"
  authors := #[inlines!"A. Great Student"]
  year := 2025
  id := "...insert arXiv id here..."

def axioms : Article where
  title := inlines!"Axioms of adaptivity"
  authors := #[inlines!"Carstensen, C.", inlines!"Feischl, M.", inlines!"Page, M.", inlines!"Praetorius, D."]
  journal := inlines!"Computers & Mathematics with Applications"
  year := 2014
  month := some inlines!"April"
  volume := inlines!"67"
  number := inlines!"6"
  pages := some (1195, 1253)
