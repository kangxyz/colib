/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.ExtensionByZeroComplex
public import Colib.AlgebraicGeometry.Modules.PerfectCoverDescent

/-!
# Extension by zero with prescribed support

If an open immersion and an open subset cover a scheme, extension by zero carries perfect
complexes supported away from the inverse-image open to perfect complexes supported away
from the original open. The actual adjunction counit is then a quasi-isomorphism.

The proof uses homology stalks, the genuine adjunction unit on the open image, and vanishing
off that image. Perfectness is descended on the two-open cover. No compactness, separation,
quasicoherence hypothesis, or replacement of the original module-sheaf complexes is used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits HomologicalComplex
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- Extension by zero preserves acyclicity on the prescribed open, using its inverse image
on the source. This statement does not require the two opens to cover. -/
theorem extensionByZero_restrictAcyclic (K : CochainComplex U.Modules ℤ)
    (hK : (((restrictFunctor (j ⁻¹ᵁ T).ι).mapHomologicalComplex (.up ℤ)).obj K).Acyclic) :
    (((restrictFunctor T.ι).mapHomologicalComplex (.up ℤ)).obj
      ((Complex.extensionByZero j).obj K)).Acyclic := by
  rw [restrictAcyclic_iff_stalkHomology] at hK ⊢
  intro n x
  let S := toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (T.ι x)
  let e : ((Complex.extensionByZero j).obj K).homology n ≅
      (extensionByZero j).obj (K.homology n) :=
    (K.sc n).mapHomologyIso (extensionByZero j)
  apply ((S.mapIso e).isZero_iff).2
  by_cases hx : T.ι x ∈ Set.range j
  · obtain ⟨y, hy⟩ := hx
    have hyT : y ∈ j ⁻¹ᵁ T := by
      change j y ∈ T
      rw [hy]
      exact x.property
    let S' := toPresheaf U ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
    have hz : IsZero (S'.obj ((restrictFunctor j).obj
        ((extensionByZero j).obj (K.homology n)))) :=
      ((S'.mapIso ((extensionByZeroRestrictIso j).app (K.homology n))).isZero_iff).2
        (hK n ⟨y, hyT⟩)
    have hz' := (((restrictStalkNatIso j y).app
      ((extensionByZero j).obj (K.homology n))).isZero_iff).1 hz
    simpa only [hy] using hz'
  · exact isZero_stalk_extensionByZero j (K.homology n) (T.ι x) hx

/-- An acyclic complex of module sheaves is perfect, since it is quasi-isomorphic to zero. -/
theorem Complex.isPerfectComplex_of_acyclic {Y : Scheme.{u}}
    (K : CochainComplex Y.Modules ℤ) (hK : K.Acyclic) :
    RingedSpace.IsPerfectComplex (X := Y.toRingedSpace) K := by
  have hzero : RingedSpace.IsPerfectComplex (X := Y.toRingedSpace)
      (0 : CochainComplex Y.Modules ℤ) :=
    RingedSpace.isPerfectComplex_of_forall_isZero fun n =>
      (HomologicalComplex.eval _ _ n).map_isZero (isZero_zero _)
  have hq : QuasiIso (0 : (0 : CochainComplex Y.Modules ℤ) ⟶ K) := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_exactAt' _ n (hK n)).2
      (acyclic_of_isZero _ (isZero_zero _) n)
  exact hzero.of_quasiIso 0 hq

/-- On a two-open cover, extension by zero preserves perfect complexes with the specified
support. The source support is on the actual inverse-image open. -/
theorem perfectSupported_extensionByZero_of_cover
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)
    {K : CochainComplex U.Modules ℤ} (hK : perfectSupported (j ⁻¹ᵁ T).ι K) :
    perfectSupported T.ι ((Complex.extensionByZero j).obj K) := by
  have hT := extensionByZero_restrictAcyclic j T K hK.2
  refine ⟨?_, hT⟩
  apply Complex.isPerfectComplex_of_two_openImmersions j T.ι
    (fun x => (hcover x).imp id (fun hx => ⟨⟨x, hx⟩, rfl⟩))
  · exact hK.1.of_iso ((Complex.extensionByZeroRestrictIso j).app K).symm
  · exact Complex.isPerfectComplex_of_acyclic _ hT

/-- The genuine extension-by-zero counit is a quasi-isomorphism on complexes supported
away from the other open of a two-open cover. -/
theorem extensionByZero_supported_counit_quasiIso
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)
    {K : CochainComplex X.Modules ℤ} (hK : perfectSupported T.ι K) :
    QuasiIso ((Complex.extensionByZeroAdjunction j).counit.app K) := by
  let R := (restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)
  let RT := (restrictFunctor T.ι).mapHomologicalComplex (ComplexShape.up ℤ)
  have hsource := extensionByZero_restrictAcyclic j T (R.obj K)
    (restrictAcyclic_preimage j T K hK.2)
  have hq : QuasiIso (RT.map ((Complex.extensionByZeroAdjunction j).counit.app K)) := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_exactAt' _ n (hK.2 n)).2 (hsource n)
  exact Complex.quasiIso_of_two_openImmersions j T.ι
    (fun x => (hcover x).imp id (fun hx => ⟨⟨x, hx⟩, rfl⟩)) _

end AlgebraicGeometry.Scheme.Modules
