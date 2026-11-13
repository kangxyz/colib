/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.CoherentAffineLocalization
public import Colib.RingTheory.KTheory.GTheory.Dedekind.FiniteResidue

/-!
# Original coherent generic G₂ injectivity with finite residue fields

The actual affine global-sections square transports the native finite-module
injectivity theorem to the literal public coherent pullback. The final form
retains a supplied fraction field and its original algebra map. No generic
G₁ injectivity premise is assumed or concluded.

Implementation source: `Quillen/GTheory/Dedekind/FiniteResidueLocalization.lean`,
the two `spec_genericGTwo` consumers, at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.ExactCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Coherent
open scoped nonZeroDivisors
namespace FGModuleCat.DedekindFiniteResidue
variable (R : Type u) [CommRing R] [IsDedekindDomain R]

/-- The literal public coherent G2 pullback along the canonical generic
localization spectrum map is injective under actual residue-field finiteness. -/
theorem spec_genericGTwo_pullback_injective
    (hfinite : ∀ p : IsDedekindDomain.HeightOneSpectrum R, Finite p.asIdeal.ResidueField) :
    Function.Injective (Scheme.pullbackG
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization (nonZeroDivisors R))))) 2) := by
  intro a b hab
  apply (publicSpecGRingEquiv (CommRingCat.of R) 2).injective
  apply genericGTwo_injective R hfinite
  have h := congrArg
    (publicSpecGRingEquiv (CommRingCat.of (Localization (nonZeroDivisors R))) 2) hab
  have ha := DFunLike.congr_fun
    (publicSpecGRingEquiv_localization_pullback (nonZeroDivisors R) 2) a
  have hb := DFunLike.congr_fun
    (publicSpecGRingEquiv_localization_pullback (nonZeroDivisors R) 2) b
  exact ha.symm.trans (h.trans hb)

private theorem pullbackG_iso_injective {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (e : X ≅ Y) (n : ℕ) :
    Function.Injective (Scheme.pullbackG e.hom n) := by
  have hc : (Scheme.pullbackG e.inv n).comp (Scheme.pullbackG e.hom n) =
      MonoidHom.id (Scheme.G Y n) := by
    simp only [← Scheme.pullbackG_comp, e.inv_hom_id, Scheme.pullbackG_id]
  exact (show Function.LeftInverse (Scheme.pullbackG e.inv n)
    (Scheme.pullbackG e.hom n) from fun a => DFunLike.congr_fun hc a).injective

section SuppliedFractionField
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

private def fractionSpecIso : Spec (CommRingCat.of K) ≅
    Spec (CommRingCat.of (Localization (nonZeroDivisors R))) :=
  Scheme.Spec.mapIso
    ((IsLocalization.algEquiv (nonZeroDivisors R)
      (Localization (nonZeroDivisors R)) K).toRingEquiv.toCommRingCatIso.op)

local instance fractionSpecMap_flat :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R)))

omit [IsDedekindDomain R] in
private theorem fractionSpecIso_triangle :
    (fractionSpecIso R K).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization (nonZeroDivisors R)))) =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := by
  change Spec.map (CommRingCat.ofHom
      (IsLocalization.algEquiv (nonZeroDivisors R) (Localization (nonZeroDivisors R)) K).toRingHom)
      ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization (nonZeroDivisors R)))) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext r
  exact (IsLocalization.algEquiv (nonZeroDivisors R)
    (Localization (nonZeroDivisors R)) K).commutes r

/-- For a supplied actual fraction field, the original public G2 pullback
along its original algebra map is injective under actual residue-field finiteness. -/
theorem spec_genericGTwo_pullback_field_injective
    (hfinite : ∀ p : IsDedekindDomain.HeightOneSpectrum R, Finite p.asIdeal.ResidueField) :
    Function.Injective (Scheme.pullbackG (Spec.map (CommRingCat.ofHom (algebraMap R K))) 2) := by
  have hi := (pullbackG_iso_injective (fractionSpecIso R K) 2).comp
    (spec_genericGTwo_pullback_injective R hfinite)
  change Function.Injective ((Scheme.pullbackG (fractionSpecIso R K).hom 2).comp
    (Scheme.pullbackG (Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization (nonZeroDivisors R))))) 2)) at hi
  simpa only [← Scheme.pullbackG_comp, fractionSpecIso_triangle R K,
    CommRingCat.of_carrier] using hi

end SuppliedFractionField

end FGModuleCat.DedekindFiniteResidue

attribute [colib_tag "COL-0614",
  colib_ref "quillen"
    "Quillen/GTheory/Dedekind/FiniteResidueLocalization.lean, spec_genericGTwo clauses"
    "adaptation" "Original public generic G2 pullback with finite actual residue fields"]
  FGModuleCat.DedekindFiniteResidue.spec_genericGTwo_pullback_injective
  FGModuleCat.DedekindFiniteResidue.spec_genericGTwo_pullback_field_injective
