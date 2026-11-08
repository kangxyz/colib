module

import Colib.AlgebraicGeometry.Intersection.AffineStalkModules

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

example (f : R →+* S) (hf : Function.Surjective f) (q : PrimeSpectrum S) :
    (ModuleCat.extendScalars (algebraMap R (Localization.AtPrime (q.comap f).asIdeal))).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) ≅
    (ModuleCat.restrictScalars
      (Localization.localRingHom (q.comap f).asIdeal q.asIdeal f rfl)).obj
      (ModuleCat.of (Localization.AtPrime q.asIdeal) (Localization.AtPrime q.asIdeal)) :=
  ModuleCat.extendScalarsTargetAtPrimeIso f hf q

example (f : R →+* S) (hf : Function.Surjective f) (q : PrimeSpectrum S)
    (p : PrimeSpectrum R) (hp : p = q.comap f) :
    (ModuleCat.restrictScalars
      (((Spec (.of R)).presheaf.stalkCongr (.of_eq hp)).hom ≫
        (Spec.map (CommRingCat.ofHom f)).stalkMap q).hom).obj
      (ModuleCat.of ((Spec (.of S)).presheaf.stalk q) ((Spec (.of S)).presheaf.stalk q)) ≅
    (ModuleCat.restrictScalars (Spec.stalkIso (.of R) p).hom.hom).obj
      ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime p.asIdeal))).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))) :=
  Scheme.specStalkModuleIsoOfEq f q p hp ≪≫
    (ModuleCat.restrictScalars (Spec.stalkIso (.of R) p).hom.hom).mapIso
      (ModuleCat.extendScalarsTargetAtPrimeIsoOfEq f hf q p hp).symm
