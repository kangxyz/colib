/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionModel
public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSupportedSectionUnit
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumIsoNaturality

/-!
# The actual supported scalar action on original coefficient prespectra

The already constructed original supported global-unit automorphism acts on the actual exact
coefficient Model map. Its value on the original chosen zero is the identity by the genuine zero
universal property. Realization retains the complete original transformation, including level
zero and every structure parameter. No new action or zero-compatibility premise is supplied.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)

/-- The original target unit acts pointwise on the unchanged supported coefficient functor. -/
def boundedAboveFlatAffineSupportedSectionPullbackUnitIso (r : (Γ(Spec S, ⊤))ˣ) :
    (boundedAboveFlatAffineSupportedSectionModelMap j j' f l h).hom.toFunctor ≅
      (boundedAboveFlatAffineSupportedSectionModelMap j j' f l h).hom.toFunctor :=
  Functor.IdentityAutomorphism.onFunctor
    (boundedAboveFlatAffineSupportedSectionsMap j j' f l h)
    (boundedAboveFlatAffineSupportedSectionUnitIso j' r)

/-- At the original section zero the actual scalar automorphism is the identity. -/
theorem boundedAboveFlatAffineSupportedSectionPullbackUnitIso_zero (r : (Γ(Spec S, ⊤))ˣ) :
    (boundedAboveFlatAffineSupportedSectionPullbackUnitIso j j' f l h r).hom.app
        (boundedAboveFlatAffineSupportedSectionWaldhausen j).zero = 𝟙 _ :=
  ((boundedAboveFlatAffineSupportedSectionsMap_exact j j' f l h).zero
    (boundedAboveFlatAffineSupportedSectionWaldhausen j).isZero).eq_of_src _ _

/-- The actual supported scalar automorphism supplies the whole original prespectrum loop. -/
def boundedAboveFlatAffineSupportedSectionUnitHomotopy (r : (Γ(Spec S, ⊤))ˣ) :
    LoopPrespectrum.Homotopy (boundedAboveFlatAffineSupportedSectionPrespectrumMap j j' f l h)
      (boundedAboveFlatAffineSupportedSectionPrespectrumMap j j' f l h) :=
  prespectrumIsoHomotopy (boundedAboveFlatAffineSupportedSectionModelMap j j' f l h)
    (boundedAboveFlatAffineSupportedSectionPullbackUnitIso j j' f l h r)

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SupportedSectionUnitHomotopy.lean:31-50"
  "adaptation" "Actual supported unit, original chosen zero and full prespectrum homotopy"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionPullbackUnitIso
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionPullbackUnitIso_zero
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionUnitHomotopy
