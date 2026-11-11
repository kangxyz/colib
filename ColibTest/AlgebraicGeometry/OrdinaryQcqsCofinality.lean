module
public import Colib.AlgebraicGeometry.KTheory.PerfectOrdinaryQcqsCofinality
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
universe u
variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j]
example (n : ℕ) : Function.Bijective (perfectOpenKRestrict j (n + 1)) :=
  qcqs_perfectOpenKRestrict_succ_bijective j n
example (n : ℕ) : Function.Injective (perfectOpenKRestrict j n) :=
  qcqs_perfectOpenKRestrict_injective j n
