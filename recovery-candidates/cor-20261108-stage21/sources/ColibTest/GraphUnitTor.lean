module

import Colib.Algebra.Category.ModuleCat.Tor.GraphUnit

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ModuleCat.Tor

universe u

variable {R S : Type u} [CommRing R] [CommRing S]
  (a : R →+* S) (q : S →+* R) (hqa : q.comp a = RingHom.id R)

-- No flatness or finite-generation assumption is imposed on the support module.
example (ha : a.Flat) (M : ModuleCat.{u} R) (n : ℕ) :
    IsZero (((CategoryTheory.Tor (ModuleCat.{u} S) (n + 1)).obj
      ((ModuleCat.restrictScalars q).obj (ModuleCat.of R R))).obj
        ((ModuleCat.extendScalars a).obj M)) :=
  isZero_graphUnitTor_succ a q hqa ha M n

-- Degree zero is S-linear, not just an identification of underlying additive groups.
example (M : ModuleCat.{u} R) :
    ((CategoryTheory.Tor (ModuleCat.{u} S) 0).obj
      ((ModuleCat.restrictScalars q).obj (ModuleCat.of R R))).obj
        ((ModuleCat.extendScalars a).obj M) ≅
      (ModuleCat.restrictScalars q).obj M :=
  graphUnitTorZeroIso a q hqa M

-- Neither the tensor cancellation nor Tor zero needs the section to be flat.
example (M : ModuleCat.{u} R) :
    ((ModuleCat.restrictScalars q).obj (ModuleCat.of R R)) ⊗
        ((ModuleCat.extendScalars a).obj M) ≅
      (ModuleCat.restrictScalars q).obj M :=
  graphUnitTensorIso a q hqa M

example (M : ModuleCat.{u} R) :
    (graphUnitTorZeroIso a q hqa M).hom ≫ (graphUnitTorZeroIso a q hqa M).inv = 𝟙 _ :=
  (graphUnitTorZeroIso a q hqa M).hom_inv_id

example (M : ModuleCat.{u} R) (s : S)
    (x : ((CategoryTheory.Tor (ModuleCat.{u} S) 0).obj
      ((ModuleCat.restrictScalars q).obj (ModuleCat.of R R))).obj
        ((ModuleCat.extendScalars a).obj M)) :
    (graphUnitTorZeroIso a q hqa M).hom (s • x) =
      q s • (show M from (graphUnitTorZeroIso a q hqa M).hom x) :=
  (graphUnitTorZeroIso a q hqa M).hom.hom.map_smul s x

-- Arbitrary quotient support is allowed; it is not assumed flat or a field.
example (ha : a.Flat) (I : Ideal R) (n : ℕ) :
    IsZero (((CategoryTheory.Tor (ModuleCat.{u} S) (n + 1)).obj
      ((ModuleCat.restrictScalars q).obj (ModuleCat.of R R))).obj
        ((ModuleCat.extendScalars a).obj (ModuleCat.of R (R ⧸ I)))) :=
  isZero_graphUnitTor_succ a q hqa ha (ModuleCat.of R (R ⧸ I)) n
