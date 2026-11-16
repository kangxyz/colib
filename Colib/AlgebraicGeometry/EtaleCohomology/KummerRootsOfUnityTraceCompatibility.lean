/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleKummerBoundary
public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleKummerDirectImage
public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleZModTraceRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSectionsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.TwistNegOneModuleInverseImage

/-! # Actual inverse-image, restriction, and roots-of-unity comparisons

All comparisons below are the existing native morphisms. The final equality identifies
the actual module trace with the coefficient trace of the actual Kummer sequence.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Stacks.EtaleCohomology
open Stacks.Kummer
variable {X Y : Scheme.{u}} (g : Y ⟶ X)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse of the coefficient comparison through the constructed inverse image
is the inverse comparison through the abstract inverse image followed by its native iso. -/
theorem kummerTrace_forgetPullback_inv (Λ : Type) [CommRing Λ]
    (M : EtaleModules.{u, 0} Λ X) :
    (traceForgetPullbackAbIso Λ g).inv.app M ≫
        (smallEtalePullbackAbIsoInverseImage g).hom.app
          ((etaleModuleForgetAb Λ X).obj M) =
      (etaleModuleUnderlyingAbelianInverseImageIso Λ g).inv.app M := by
  rfl

variable [Etale g]

set_option backward.isDefEq.respectTransparency false in
/-- The restriction adjunction unit on Gm is the actual base-change comparison. -/
theorem kummerTrace_restrictionUnit_Gm :
    (etaleRestrictionAbelianDirectImageAdj.{u, 0} g).unit.app
        (multiplicativeSheaf.{u, 0} X) ≫
      (etaleAbelianDirectImage.{u, 0} g).map
        (etaleRestrictionMultiplicativeSheafIso g).hom =
      multiplicativeDirectImageComparison.{u, 0} g := by
  ext U : 3
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The original Gm inverse-image comparison agrees with the native restriction comparison. -/
theorem kummerTrace_inverseImage_Gm :
    multiplicativeInverseImageComparison.{u, 0} g =
      (etaleAbelianInverseImageRestrictionIso.{u, 0} g).hom.app
          (multiplicativeSheaf.{u, 0} X) ≫
        (etaleRestrictionMultiplicativeSheafIso g).hom := by
  apply ((etaleAbelianInverseImageDirectImageAdj.{u, 0} g).homEquiv _ _).injective
  have h : (etaleAbelianInverseImageDirectImageAdj.{u, 0} g).homEquiv _ _
      ((etaleAbelianInverseImageRestrictionIso.{u, 0} g).hom.app
        (multiplicativeSheaf.{u, 0} X)) =
      (etaleRestrictionAbelianDirectImageAdj.{u, 0} g).unit.app
        (multiplicativeSheaf.{u, 0} X) :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _
  rw [multiplicativeInverseImageComparison_transpose,
    Adjunction.homEquiv_naturality_right, h]
  exact (kummerTrace_restrictionUnit_Gm g).symm

set_option backward.isDefEq.respectTransparency false in
/-- The original roots-of-unity inverse-image comparison agrees with the native
restriction comparison, as detected by its actual kernel inclusion. -/
theorem kummerTrace_inverseImage_roots (n : ℕ) :
    rootsOfUnityInverseImageComparison.{u, 0} g n =
      (etaleAbelianInverseImageRestrictionIso.{u, 0} g).hom.app
          (rootsOfUnitySheaf.{u, 0} X n) ≫
        (etaleRestrictionRootsOfUnityIso g n).hom := by
  have hμ : (etaleRestrictionRootsOfUnityIso g n).hom ≫ rootsOfUnityι.{u, 0} Y n =
      (etaleRestriction.{u, 0} g).map (rootsOfUnityι.{u, 0} X n) ≫
        (etaleRestrictionMultiplicativeSheafIso g).hom :=
    (etaleRestrictionKummerIso g n).hom.comm₁₂
  apply (cancel_mono (rootsOfUnityι.{u, 0} Y n)).1
  rw [rootsOfUnityInverseImageComparison_comp_rootsOfUnityι, Category.assoc, hμ,
    ← Category.assoc,
    ← (etaleAbelianInverseImageRestrictionIso.{u, 0} g).hom.naturality,
    Category.assoc, ← kummerTrace_inverseImage_Gm g]

omit [Etale g] in
set_option backward.isDefEq.respectTransparency false in
/-- Forgetting the existing module roots comparison exposes its existing abelian comparison. -/
theorem kummerTrace_forget_rootsModule_comparison (n : ℕ) [NeZero n]
    (hX : IsUnit (n : Γ(X, ⊤))) :
    (etaleModuleForgetAb (ZMod n) Y).map
        (rootsOfUnityModuleInverseImageIso g n hX).hom =
      (etaleModuleUnderlyingAbelianInverseImageIso (ZMod n) g).inv.app
          (rootsOfUnityModule.{u, 0} X n) ≫
        rootsOfUnityInverseImageComparison.{u, 0} g n := by
  dsimp only [rootsOfUnityModuleInverseImageIso, Functor.FullyFaithful.preimageIso]
  rw [(ArtinSchreier.etaleModuleForgetZModFullyFaithful Y n).map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
    rootsOfUnityModuleForgetIso, Iso.refl_hom, Iso.refl_inv,
    rootsOfUnityInverseImageIso_hom]
  change (etaleModuleUnderlyingAbelianInverseImageIso (ZMod n) g).inv.app
      (rootsOfUnityModule.{u, 0} X n) ≫
      (etaleAbelianInverseImage.{u, 0} g).map (𝟙 (rootsOfUnitySheaf.{u, 0} X n)) ≫
      rootsOfUnityInverseImageComparison.{u, 0} g n ≫
      𝟙 (rootsOfUnitySheaf.{u, 0} Y n) = _
  erw [(etaleAbelianInverseImage.{u, 0} g).map_id, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The actual module roots comparison is the actual restriction comparison after
forgetting coefficients and transporting between the two native inverse images. -/
theorem kummerTrace_forget_rootsModule_restriction (n : ℕ) [NeZero n]
    (hX : IsUnit (n : Γ(X, ⊤))) :
    (etaleModuleForgetAb (ZMod n) Y).map
        (rootsOfUnityModuleInverseImageIso g n hX).hom =
      (traceForgetPullbackAbIso (ZMod n) g).inv.app
          (rootsOfUnityModule.{u, 0} X n) ≫
        ((smallEtaleAdjunctionAb g).leftAdjointUniq
          (etaleRestrictionAbelianDirectImageAdj.{u, 0} g)).hom.app
            (rootsOfUnitySheaf.{u, 0} X n) ≫
        (etaleRestrictionRootsOfUnityIso g n).hom := by
  have htrans :
      (smallEtalePullbackAbIsoInverseImage g).hom.app (rootsOfUnitySheaf.{u, 0} X n) ≫
        (etaleAbelianInverseImageRestrictionIso.{u, 0} g).hom.app
          (rootsOfUnitySheaf.{u, 0} X n) =
      ((smallEtaleAdjunctionAb g).leftAdjointUniq
        (etaleRestrictionAbelianDirectImageAdj.{u, 0} g)).hom.app
          (rootsOfUnitySheaf.{u, 0} X n) :=
    Adjunction.leftAdjointUniq_trans_app _ _ _ _
  rw [kummerTrace_forget_rootsModule_comparison,
    ← kummerTrace_forgetPullback_inv g (ZMod n), kummerTrace_inverseImage_roots]
  change
    ((traceForgetPullbackAbIso (ZMod n) g).inv.app (rootsOfUnityModule.{u, 0} X n) ≫
      (smallEtalePullbackAbIsoInverseImage g).hom.app (rootsOfUnitySheaf.{u, 0} X n)) ≫
        ((etaleAbelianInverseImageRestrictionIso.{u, 0} g).hom.app
          (rootsOfUnitySheaf.{u, 0} X n) ≫
          (etaleRestrictionRootsOfUnityIso g n).hom) = _
  have hp := congrArg
    (fun f : (smallEtalePullbackAb g).obj (rootsOfUnitySheaf.{u, 0} X n) ⟶
        (etaleRestriction.{u, 0} g).obj (rootsOfUnitySheaf.{u, 0} X n) =>
      (traceForgetPullbackAbIso (ZMod n) g).inv.app
          (rootsOfUnityModule.{u, 0} X n) ≫ f ≫
        (etaleRestrictionRootsOfUnityIso g n).hom) htrans
  simpa only [Category.assoc] using hp

set_option backward.isDefEq.respectTransparency false in
/-- The native module trace on roots of unity is the actual Kummer coefficient
trace after the existing module inverse-image comparison. -/
theorem kummerTrace_forget_rootsModule_trace [IsFinite g] (n : ℕ) [NeZero n]
    (hX : IsUnit (n : Γ(X, ⊤))) :
    (etaleModuleForgetAb (ZMod n) X).map
        (finiteEtaleZModTrace n g (rootsOfUnityModule.{u, 0} X n)) =
      (etaleAbelianDirectImage.{u, 0} g).map
          ((etaleModuleForgetAb (ZMod n) Y).map
            (rootsOfUnityModuleInverseImageIso g n hX).hom) ≫
        finiteEtaleRootsOfUnityTrace g n := by
  have htrace : finiteEtaleRootsOfUnityTrace g n =
      (etaleAbelianDirectImage.{u, 0} g).map
          (etaleRestrictionRootsOfUnityIso g n).inv ≫
        finiteEtaleTrace g (rootsOfUnitySheaf.{u, 0} X n) := rfl
  have hcancel :
      (etaleAbelianDirectImage.{u, 0} g).map
          (etaleRestrictionRootsOfUnityIso g n).hom ≫
        (etaleAbelianDirectImage.{u, 0} g).map
          (etaleRestrictionRootsOfUnityIso g n).inv = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  rw [forget_finiteEtaleZModTrace, kummerTrace_forget_rootsModule_restriction,
    htrace]
  dsimp only [finiteEtaleTraceOnPullbackAb]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← Category.assoc
    ((etaleAbelianDirectImage.{u, 0} g).map
      (etaleRestrictionRootsOfUnityIso g n).hom), hcancel, Category.id_comp]
  rfl

end Stacks.EtaleCohomology
end
