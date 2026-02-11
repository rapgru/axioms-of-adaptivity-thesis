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
  url := "https://doi.org/10.1016/j.camwa.2013.12.003"

def ho2022aeneas : Article where
  title := inlines!"Aeneas: Rust verification by functional translation"
  authors := #[inlines!"Ho, Son", inlines!"Protzenko, Jonathan"]
  journal := inlines!"Proc. ACM Program. Lang."
  year := 2022
  month := some inlines!"August"
  volume := inlines!"6"
  number := inlines!"ICFP"
  url := "https://doi.org/10.1145/3547647"

def hales2017proof : Article where
  title := inlines!"A formal proof of the Kepler conjecture"
  authors := #[
    inlines!"Hales, Thomas",
    inlines!"Adams, Mark",
    inlines!"Bauer, Gertrud",
    inlines!"Dang, Tat Dat",
    inlines!"Harrison, John",
    inlines!"Hoang, Le Truong",
    inlines!"Kaliszyk, Cezary",
    inlines!"Magron, Victor",
    inlines!"McLaughlin, Sean",
    inlines!"Nguyen, Tat Thang",
    inlines!"Nguyen, Truong Quang",
    inlines!"Nipkow, Tobias",
    inlines!"Obua, Steven",
    inlines!"Pleso, Joseph",
    inlines!"Rute, Jason",
    inlines!"Solovyev, Alexey",
    inlines!"Ta, An Hoai Thi",
    inlines!"Tran, Trung Nam",
    inlines!"Trieu, Diep Thi",
    inlines!"Urban, Josef",
    inlines!"Vu, Ky Khac",
    inlines!"Zumkeller, Roland"
  ]
  journal := inlines!"Forum of Mathematics, Pi"
  year := 2017
  month := none
  volume := inlines!"5"
  number := inlines!"e2"
  url := "https://doi.org/10.1017/fmp.2017.1"

def avigad2024formal : Article where
  title := inlines!"Mathematics and the formal turn"
  authors := #[inlines!"Avigad, Jeremy"]
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
    inlines!"Hubert, Thomas",
    inlines!"Mehta, Rishi",
    inlines!"Sartran, Laurent",
    inlines!"Horváth, Miklós Z.",
    inlines!"Žužić, Goran",
    inlines!"Wieser, Eric",
    inlines!"Huang, Aja",
    inlines!"Schrittwieser, Julian",
    inlines!"Schroecker, Yannick",
    inlines!"Masoom, Hussain",
    inlines!"Bertolli, Ottavia",
    inlines!"Zahavy, Tom",
    inlines!"Mandhane, Amol",
    inlines!"Yung, Jessica",
    inlines!"Beloshapka, Iuliya",
    inlines!"Ibarz, Borja",
    inlines!"Veeriah, Vivek",
    inlines!"Yu, Lei",
    inlines!"Nash, Oliver",
    inlines!"Lezeau, Paul",
    inlines!"Mercuri, Salvatore",
    inlines!"Sönne, Calle",
    inlines!"Mehta, Bhavik",
    inlines!"Davies, Alex",
    inlines!"Zheng, Daniel",
    inlines!"Pedregosa, Fabian",
    inlines!"Li, Yin",
    inlines!"von Glehn, Ingrid",
    inlines!"Rowland, Mark",
    inlines!"Albanie, Samuel",
    inlines!"Velingker, Ameya",
    inlines!"Schmitt, Simon",
    inlines!"Lockhart, Edward",
    inlines!"Hughes, Edward",
    inlines!"Michalewski, Henryk",
    inlines!"Sonnerat, Nicolas",
    inlines!"Hassabis, Demis",
    inlines!"Kohli, Pushmeet",
    inlines!"Silver, David"
  ]
  journal := inlines!"Nature"
  year := 2025
  month := some inlines!"November"
  volume := inlines!""
  number := inlines!""
  url := "https://doi.org/10.1038/s41586-025-09833-y"
