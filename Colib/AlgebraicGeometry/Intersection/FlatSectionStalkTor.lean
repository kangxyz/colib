/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.Tor.GraphUnit
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Length
public import StacksFrontier.RingTheory.Tor.Balancing.Naturality
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Basic

/-!
# Actual stalk Tor for an open section of a flat morphism

Let `i : C ⟶ T` and `p : T ⟶ X`, with `i ≫ p` an open immersion. At an actual
point `c : C`, the inverse of the actual projection stalk isomorphism followed
by the actual `p` stalk map gives a ring section of `i.stalkMap c`. If `p` is
flat, this section is flat. Thus the graph-unit algebra applies to the literal
`C` stalk with its full `T` stalk action, and an arbitrary module extended along
this constructed section. The degree-zero isomorphisms require no flatness.

No ring retraction, flatness of a support module, Tor independence or comparison
is assumed. The second module is scalar extension, not yet an identified stalk
of another geometric support. This is the local geometric input to the original
`motivic_source_a6805c4`, `Composition/Identity/Tor.lean`, not the full incidence
coefficient theorem or unit assembly of `Composition/Identity/Units.lean`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {C T X : Scheme.{u}} (i : C ⟶ T) (p : T ⟶ X)
  [IsOpenImmersion (i ≫ p)] (c : C)

/-- The actual local ring section obtained by inverting the open projection stalk map. -/
def openSectionStalkExtension : C.presheaf.stalk c →+* T.presheaf.stalk (i c) :=
  (inv ((i ≫ p).stalkMap c) ≫ p.stalkMap (i c)).hom

/-- The actual inclusion stalk map retracts the constructed local ring extension. -/
@[simp]
theorem stalkMap_comp_openSectionStalkExtension :
    (i.stalkMap c).hom.comp (openSectionStalkExtension i p c) =
      RingHom.id (C.presheaf.stalk c) := by
  change (inv ((i ≫ p).stalkMap c) ≫ p.stalkMap (i c) ≫ i.stalkMap c).hom = _
  rw [← Scheme.Hom.stalkMap_comp]
  simp

/-- Flatness comes from the actual ambient projection, not from the support module. -/
theorem flat_openSectionStalkExtension [Flat p] :
    (openSectionStalkExtension i p c).Flat := by
  exact (RingHom.Flat.of_bijective
    (ConcreteCategory.bijective_of_isIso (inv ((i ≫ p).stalkMap c)))).comp
    (Flat.stalkMap p (i c))

/-- Degree-zero Tor identifies the actual section stalk tensor with the input module. -/
def openSectionStalkTorZeroIso (M : ModuleCat (C.presheaf.stalk c)) :
    (((Tor (ModuleCat (T.presheaf.stalk (i c))) 0).obj
      ((ModuleCat.restrictScalars (i.stalkMap c).hom).obj
        (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))).obj
      ((ModuleCat.extendScalars (openSectionStalkExtension i p c)).obj M)) ≅
    (ModuleCat.restrictScalars (i.stalkMap c).hom).obj M :=
  ModuleCat.Tor.graphUnitTorZeroIso (openSectionStalkExtension i p c)
    (i.stalkMap c).hom (stalkMap_comp_openSectionStalkExtension i p c) M

/-- The actual section stalk has zero positive Tor against an extended arbitrary module. -/
theorem isZero_openSectionStalkTor_succ [Flat p]
    (M : ModuleCat (C.presheaf.stalk c)) (n : ℕ) :
    IsZero (((Tor (ModuleCat (T.presheaf.stalk (i c))) (n + 1)).obj
      ((ModuleCat.restrictScalars (i.stalkMap c).hom).obj
        (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))).obj
      ((ModuleCat.extendScalars (openSectionStalkExtension i p c)).obj M)) :=
  ModuleCat.Tor.isZero_graphUnitTor_succ (openSectionStalkExtension i p c)
    (i.stalkMap c).hom (stalkMap_comp_openSectionStalkExtension i p c)
    (flat_openSectionStalkExtension i p c) M n

/-- The degree-zero identification also preserves the support-first Tor ordering. -/
def openSectionStalkTorZeroIsoFlip (M : ModuleCat (C.presheaf.stalk c)) :
    (((Tor (ModuleCat (T.presheaf.stalk (i c))) 0).obj
      ((ModuleCat.extendScalars (openSectionStalkExtension i p c)).obj M)).obj
      ((ModuleCat.restrictScalars (i.stalkMap c).hom).obj
        (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))) ≅
    (ModuleCat.restrictScalars (i.stalkMap c).hom).obj M := by
  let N := (ModuleCat.extendScalars (openSectionStalkExtension i p c)).obj M
  let G := (ModuleCat.restrictScalars (i.stalkMap c).hom).obj
    (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c))
  exact (((Tor_iso_Tor' (T.presheaf.stalk (i c)) 0).app N).app G ≪≫
    (((torFlip_iso_Tor' (T.presheaf.stalk (i c)) 0).app N).app G).symm) ≪≫
    openSectionStalkTorZeroIso i p c M

/-- Positive Tor vanishing also holds in the support-first ordering. -/
theorem isZero_openSectionStalkTor_succ_flip [Flat p]
    (M : ModuleCat (C.presheaf.stalk c)) (n : ℕ) :
    IsZero (((Tor (ModuleCat (T.presheaf.stalk (i c))) (n + 1)).obj
      ((ModuleCat.extendScalars (openSectionStalkExtension i p c)).obj M)).obj
      ((ModuleCat.restrictScalars (i.stalkMap c).hom).obj
        (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))) := by
  let N := (ModuleCat.extendScalars (openSectionStalkExtension i p c)).obj M
  let G := (ModuleCat.restrictScalars (i.stalkMap c).hom).obj
    (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c))
  exact IsZero.of_iso (isZero_openSectionStalkTor_succ i p c M n)
    (((Tor_iso_Tor' (T.presheaf.stalk (i c)) (n + 1)).app N).app G ≪≫
      (((torFlip_iso_Tor' (T.presheaf.stalk (i c)) (n + 1)).app N).app G).symm)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom

variable {C T X : Scheme.{u}} (i : C ⟶ T) (p : T ⟶ X)
  [IsOpenImmersion (i ≫ p)] (c : C)

/-- Degree-zero length equals the full length of the support module, including infinity. -/
theorem length_openSectionStalkTor_zero
    (M : ModuleCat (C.presheaf.stalk c)) :
    Module.length (T.presheaf.stalk (i c))
      (((Tor (ModuleCat (T.presheaf.stalk (i c))) 0).obj
        ((ModuleCat.restrictScalars (i.stalkMap c).hom).obj
          (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))).obj
        ((ModuleCat.extendScalars (openSectionStalkExtension i p c)).obj M)) =
      Module.length (C.presheaf.stalk c) M := by
  rw [(openSectionStalkTorZeroIso i p c M).toLinearEquiv.length_eq]
  let q := (i.stalkMap c).hom
  let := q.toAlgebra
  let : IsScalarTower (T.presheaf.stalk (i c)) (C.presheaf.stalk c)
      ((ModuleCat.restrictScalars q).obj M) := ⟨fun r s x => by
    change (q r * s) • x = q r • (s • x)
    exact mul_smul (q r) s x⟩
  apply Module.length_eq_of_surjective (R := C.presheaf.stalk c)
    (M := (ModuleCat.restrictScalars q).obj M)
  intro r
  exact ⟨openSectionStalkExtension i p c r,
    DFunLike.congr_fun (stalkMap_comp_openSectionStalkExtension i p c) r⟩

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom

variable {A C T X : Scheme.{u}} (i : C ⟶ T) (p : T ⟶ X)
  [IsOpenImmersion (i ≫ p)] (j : A ⟶ C) [IsClosedImmersion j]

/-- For an actual reduced closed support at a generic point, degree-zero length is one.
The other Tor input is its scalar-extended actual stalk module; no pulled-stalk
identification is included in this statement. -/
theorem length_openSectionStalkTor_zero_closedSupport_eq_one [IsReduced A]
    (a : A) (ha : IsMax a) :
    Module.length (T.presheaf.stalk (i (j a)))
      (((Tor (ModuleCat (T.presheaf.stalk (i (j a)))) 0).obj
        ((ModuleCat.restrictScalars (i.stalkMap (j a)).hom).obj
          (ModuleCat.of (C.presheaf.stalk (j a)) (C.presheaf.stalk (j a))))).obj
        ((ModuleCat.extendScalars (openSectionStalkExtension i p (j a))).obj
          ((ModuleCat.restrictScalars (j.stalkMap a).hom).obj
            (ModuleCat.of (A.presheaf.stalk a) (A.presheaf.stalk a))))) = 1 := by
  rw [length_openSectionStalkTor_zero]
  let q := (j.stalkMap a).hom
  let M := ModuleCat.of (A.presheaf.stalk a) (A.presheaf.stalk a)
  let := q.toAlgebra
  let : IsScalarTower (C.presheaf.stalk (j a)) (A.presheaf.stalk a)
      ((ModuleCat.restrictScalars q).obj M) := ⟨fun r s x => by
    change (q r * s) • x = q r • (s • x)
    exact mul_smul (q r) s x⟩
  exact (Module.length_eq_of_surjective (R := A.presheaf.stalk a)
    (M := (ModuleCat.restrictScalars q).obj M) (j.stalkMap_surjective a)).trans
    (length_stalk_eq_one_of_isMax ha)

end AlgebraicGeometry.Scheme.Hom
