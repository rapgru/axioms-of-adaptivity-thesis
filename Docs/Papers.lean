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
  authors := #[inlines!"C. Carstensen", inlines!"M. Feischl", inlines!"M. Page", inlines!"D. Praetorius"]
  journal := inlines!"Computers & Mathematics with Applications"
  year := 2014
  month := some inlines!"April"
  volume := inlines!"67"
  number := inlines!"6"
  pages := some (1195, 1253)
  url := "https://doi.org/10.1016/j.camwa.2013.12.003"

def leitsch1997resolution : Article where
  title := inlines!"The Resolution Calculus"
  authors := #[inlines!"Alexander Leitsch"]
  year := 1997
  journal := inlines!"Texts in Theoretical Computer Science. An EATCS Series"
  url := "https://doi.org/10.1007/978-3-642-60605-2"
  month := none
  volume := inlines!""
  number := inlines!""

def ho2022aeneas : Article where
  title := inlines!"Aeneas: Rust verification by functional translation"
  authors := #[inlines!"Son Ho", inlines!"Jonathan Protzenko"]
  journal := inlines!"Proc. ACM Program. Lang."
  year := 2022
  month := some inlines!"August"
  volume := inlines!"6"
  number := inlines!"ICFP"
  url := "https://doi.org/10.1145/3547647"

def hales2017proof : Article where
  title := inlines!"A formal proof of the Kepler conjecture"
  authors := #[
    inlines!"Thomas Hales",
    inlines!"Mark Adams",
    inlines!"Gertrud Bauer",
    inlines!"Tat Dat Dang",
    inlines!"John Harrison",
    inlines!"Le Truong Hoang",
    inlines!"Cezary Kaliszyk",
    inlines!"Victor Magron",
    inlines!"Sean McLaughlin",
    inlines!"Tat Thang Nguyen",
    inlines!"Truong Quang Nguyen",
    inlines!"Tobias Nipkow",
    inlines!"Steven Obua",
    inlines!"Joseph Pleso",
    inlines!"Jason Rute",
    inlines!"Alexey Solovyev",
    inlines!"An Hoai Thi Ta",
    inlines!"Trung Nam Tran",
    inlines!"Diep Thi Trieu",
    inlines!"Josef Urban",
    inlines!"Ky Khac Vu",
    inlines!"Roland Zumkeller"
  ]
  journal := inlines!"Forum of Mathematics, Pi"
  year := 2017
  month := none
  volume := inlines!"5"
  number := inlines!"e2"
  url := "https://doi.org/10.1017/fmp.2017.1"

def avigad2024formal : Article where
  title := inlines!"Mathematics and the formal turn"
  authors := #[inlines!"Jeremy Avigad"]
  journal := inlines!"Bull. Amer. Math. Soc."
  year := 2024
  month := some inlines!"April"
  volume := inlines!"61"
  number := inlines!"2"
  pages := some (225, 240)
  url := "https://doi.org/10.1090/bull/1832"

def hubert2025olympiad : Article where
  title := inlines!"Olympiad-level formal mathematical reasoning with reinforcement learning"
  authors := #[
    inlines!"Thomas Hubert",
    inlines!"Rishi Mehta",
    inlines!"Laurent Sartran",
    inlines!"Miklós Z. Horváth",
    inlines!"Goran Žužić",
    inlines!"Eric Wieser",
    inlines!"Aja Huang",
    inlines!"Julian Schrittwieser",
    inlines!"Yannick Schroecker",
    inlines!"Hussain Masoom",
    inlines!"Ottavia Bertolli",
    inlines!"Tom Zahavy",
    inlines!"Amol Mandhane",
    inlines!"Jessica Yung",
    inlines!"Iuliya Beloshapka",
    inlines!"Borja Ibarz",
    inlines!"Vivek Veeriah",
    inlines!"Lei Yu",
    inlines!"Oliver Nash",
    inlines!"Paul Lezeau",
    inlines!"Salvatore Mercuri",
    inlines!"Calle Sönne",
    inlines!"Bhavik Mehta",
    inlines!"Alex Davies",
    inlines!"Daniel Zheng",
    inlines!"Fabian Pedregosa",
    inlines!"Yin Li",
    inlines!"Ingrid von Glehn",
    inlines!"Mark Rowland",
    inlines!"Samuel Albanie",
    inlines!"Ameya Velingker",
    inlines!"Simon Schmitt",
    inlines!"Edward Lockhart",
    inlines!"Edward Hughes",
    inlines!"Henryk Michalewski",
    inlines!"Nicolas Sonnerat",
    inlines!"Demis Hassabis",
    inlines!"Pushmeet Kohli",
    inlines!"David Silver"
  ]
  journal := inlines!"Nature"
  year := 2025
  month := some inlines!"November"
  volume := inlines!""
  number := inlines!""
  url := "https://doi.org/10.1038/s41586-025-09833-y"

def feischl2025fem : InProceedings where
  title := inlines!"Numerics of Partial Differential Equations: Stationary Problems"
  authors := #[inlines!"Michael Feischl", inlines!"Dirk Praetorius"]
  year := 2025
  booktitle := inlines!"Lecture Notes, TU Wien"
  url := "https://michaelfeischl.github.io/lecturenotes/FEM_VO.pdf"
