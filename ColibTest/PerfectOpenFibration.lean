module

import Colib.AlgebraicGeometry.KTheory.PerfectOpenLongExactSequence

open CategoryTheory AlgebraicGeometry Topology
open Scheme.Modules

universe u

noncomputable section

variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

example : Waldhausen.Fibration.ExtensionAxiom (perfectOpenWeakWaldhausen j) :=
  perfectOpenWeak_extensionAxiom j

example : IsWeakHomotopyEquivalence (Waldhausen.Fibration.canonicalFiberMap
    (perfectOpenNested j)) := perfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence j

example (n : ℕ) : Function.Bijective (perfectSupportedFiberKMap j n) :=
  perfectSupportedFiberKMap_bijective j n

example (n : ℕ) :
    (perfectOpenKMap j (n + 1)).range = (perfectOpenConnectingHom j n).ker ∧
    (perfectOpenConnectingHom j n).range = (perfectSupportedKMap j n).ker ∧
    (perfectSupportedKMap j n).range = (perfectOpenKMap j n).ker :=
  perfectOpen_positiveLongExactSequence j n

example : Function.Surjective (perfectOpenKMap j 0) := perfectOpenKMap_zero_surjective j

end
