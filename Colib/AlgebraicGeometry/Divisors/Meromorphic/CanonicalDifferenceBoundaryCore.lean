/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalDifferenceTensor
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalIdealOne
public import StacksFrontier.AlgebraicGeometry.Divisors.PullbackTensorTrivialization

/-!
# The canonical Cartier difference in its specified full-boundary frame

The original positive canonical section and the original ideal section one are
transported through the native Cartier pullback comparisons. Their evaluation is
one on the entire boundary, without passing to its reduction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace MonoidalCategory
open scoped TensorProduct

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace Stacks.Divisors

/-- The literal tensor of the original positive canonical section and an original ideal section. -/
def canonicalDifferenceTensorSection {B : Scheme.{u}} (D E : B.IdealSheafData)
    (W : B.Opens) (b : Γ(negativeTwist' E, W)) : Γ(differenceSheaf D E, W) :=
  Stacks.SheafOfModules.tensorSectionsAt B.sheaf.obj B.ringCatSheaf.property (op W)
    (divisorSheaf D) (negativeTwist' E) ((canonicalSection' D).eval (op W)) b

private theorem transport_section_property {B : Scheme.{u}} {ι κ β : Type u}
    (F : ι → κ → B.Modules) (G : κ → Type u) (W : B.Opens)
    (s : ∀ a b, G b → (F a b).val.obj (op W)) (p : ∀ b, G b → Prop)
    {a a₀ : ι} {b b₀ : κ} (f : (F a₀ b₀).val.obj (op W) → β) (z : β)
    (hf : ∀ t, p b₀ t → f (s a₀ b₀ t) = z)
    (ha : a = a₀) (hb : b = b₀) (e : F a b ≅ F a₀ b₀)
    (he : e = eqToIso (congrArg₂ F ha hb)) (t : G b) (ht : p b t) :
    f (e.hom.val.app (op W) (s a b t)) = z := by
  subst e
  cases ha
  cases hb
  exact hf t ht

private theorem tensorSections_curriedMapLeft (B : Scheme.{u}) (F F' G : B.Modules)
    (e : F ≅ F') (W : B.Opens) (a : Γ(F, W)) (b : Γ(G, W)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor B.sheaf).mapIso e).app G).hom.val.app (op W)
      (Stacks.SheafOfModules.tensorSectionsAt B.sheaf.obj B.ringCatSheaf.property (op W)
        F G a b) =
    Stacks.SheafOfModules.tensorSectionsAt B.sheaf.obj B.ringCatSheaf.property (op W)
      F' G (e.hom.app W a) b := by
  let f := PresheafOfModules.tensorHom (O := B.sheaf.obj) e.hom.val (𝟙 G.val)
  refine (Stacks.SheafOfModules.toSheafify_app_map_obj (O := B.sheaf.obj)
    (hO := B.ringCatSheaf.property) (f := f) (op W) (a ⊗ₜ b)).trans ?_
  exact congrArg
    ((Stacks.SheafOfModules.TensorSheafification.toSheafify B.sheaf.obj
      B.ringCatSheaf.property (F'.val ⊗ G.val)).app (op W))
    (PresheafOfModules.tensorHom_tmul e.hom.val (𝟙 G.val) (op W) a b)

private theorem tensorSections_curriedMapRight (B : Scheme.{u}) (F G G' : B.Modules)
    (e : G ≅ G') (W : B.Opens) (a : Γ(F, W)) (b : Γ(G, W)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor B.sheaf).obj F).mapIso e).hom.val.app (op W)
      (Stacks.SheafOfModules.tensorSectionsAt B.sheaf.obj B.ringCatSheaf.property (op W)
        F G a b) =
    Stacks.SheafOfModules.tensorSectionsAt B.sheaf.obj B.ringCatSheaf.property (op W)
      F G' a (e.hom.app W b) := by
  let f := PresheafOfModules.tensorHom (O := B.sheaf.obj) (𝟙 F.val) e.hom.val
  refine (Stacks.SheafOfModules.toSheafify_app_map_obj (O := B.sheaf.obj)
    (hO := B.ringCatSheaf.property) (f := f) (op W) (a ⊗ₜ b)).trans ?_
  exact congrArg
    ((Stacks.SheafOfModules.TensorSheafification.toSheafify B.sheaf.obj
      B.ringCatSheaf.property (F.val ⊗ G'.val)).app (op W))
    (PresheafOfModules.tensorHom_tmul (𝟙 F.val) e.hom.val (op W) a b)

private theorem canonicalDifferenceTensorSection_top {B : Scheme.{u}}
    (W : B.Opens) (b : Γ(negativeTwist' (⊤ : B.IdealSheafData), W))
    (hb : idealSheafSection (⊤ : B.IdealSheafData) b = (1 : Γ(B, W))) :
    (differenceSheafTopIso B).hom.val.app (op W)
      (canonicalDifferenceTensorSection (⊤ : B.IdealSheafData) ⊤ W b) =
      (1 : Γ(B, W)) :=
  differenceSheafTopIso_tensor_canonical_of_eq_one B W b hb

/-- Evaluation after identifying the two original empty inverse-image ideals. -/
theorem differenceSheafTopIso_eqToIso_tensor_canonical {B : Scheme.{u}}
    (D E : B.IdealSheafData) (hD : D = ⊤) (hE : E = ⊤) (W : B.Opens)
    (e : differenceSheaf D E ≅ differenceSheaf (⊤ : B.IdealSheafData) ⊤)
    (he : e = eqToIso (congrArg₂ differenceSheaf hD hE))
    (b : Γ(negativeTwist' E, W)) (hb : idealSheafSection E b = (1 : Γ(B, W))) :
    (differenceSheafTopIso B).hom.val.app (op W)
      (e.hom.val.app (op W) (canonicalDifferenceTensorSection D E W b)) =
      (1 : Γ(B, W)) := by
  exact transport_section_property differenceSheaf (fun E => Γ(negativeTwist' E, W)) W
    (fun D E => canonicalDifferenceTensorSection D E W)
    (fun E b => idealSheafSection E b = (1 : Γ(B, W)))
    ((differenceSheafTopIso B).hom.val.app (op W)) (1 : Γ(B, W))
    (canonicalDifferenceTensorSection_top W) hD hE e he b hb

variable {X B : Scheme.{u}} (i : B ⟶ X) (D E : X.IdealSheafData)
  [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]

/-- The canonical positive section pulls back correctly over every full inverse-image open. -/
theorem invertibleSheafPullbackIso_canonicalSection_preimage [IsPullbackDefined i D]
    (U : X.Opens) :
    (invertibleSheafPullbackIso i D).hom.app (i ⁻¹ᵁ U)
      (pullbackSectionHom i (divisorSheaf D) U (i ⁻¹ᵁ U) le_rfl
        ((canonicalSection' D).eval (op U))) =
      (canonicalSection' (D.comap i)).eval (op (i ⁻¹ᵁ U)) := by
  refine (congrArg (fun s => (invertibleSheafPullbackIso i D).hom.app (i ⁻¹ᵁ U)
    (pullbackSectionHom i (divisorSheaf D) U (i ⁻¹ᵁ U) le_rfl s))
    ((canonicalSection' D).property (homOfLE (le_top : U ≤ ⊤)).op).symm).trans ?_
  refine (congrArg ((invertibleSheafPullbackIso i D).hom.app (i ⁻¹ᵁ U))
    (pullbackSectionHom_resTop i (divisorSheaf D) U (divisorSheafGlobalSection D))).trans ?_
  refine (PresheafOfModules.naturality_apply (invertibleSheafPullbackIso i D).hom.val
    (homOfLE (le_top : i ⁻¹ᵁ U ≤ ⊤)).op (pullbackCanonicalSection i D)).trans ?_
  exact (congrArg ((divisorSheaf (D.comap i)).presheaf.map
    (homOfLE (le_top : i ⁻¹ᵁ U ≤ ⊤)).op)
    (invertibleSheafPullbackIso_canonicalSection i D)).trans
    ((canonicalSection' (D.comap i)).property (homOfLE (le_top : i ⁻¹ᵁ U ≤ ⊤)).op)

/-- Pulling back the original ideal's section one still has ambient value one. -/
theorem idealSheafSection_pullbackIdealOne_preimage [IsPullbackDefined i E]
    (U : X.Opens) (b : Γ(negativeTwist' E, U))
    (hb : idealSheafSection E b = (1 : Γ(X, U))) :
    idealSheafSection (E.comap i)
      ((pullbackIdealSheafComapIso i E inferInstance).hom.val.app (op (i ⁻¹ᵁ U))
        (pullbackSectionHom i (negativeTwist' E) U (i ⁻¹ᵁ U) le_rfl b)) =
      (1 : Γ(B, i ⁻¹ᵁ U)) := by
  refine (idealSheafSection_pullbackIdealSheafComapMap i E (i ⁻¹ᵁ U) _).trans ?_
  refine (congrArg (pullbackIdealSection i E (i ⁻¹ᵁ U))
    (pullbackSectionHom_preimage_self i (negativeTwist' E) U b)).trans ?_
  exact (pullbackIdealSection_pullbackUnit i E U b).trans
    ((congrArg (i.app U).hom hb).trans (map_one _))

/-- The fixed difference pullback comparison transports the two original tensor factors. -/
theorem differenceSheafPullbackIso_tensorSection_preimage
    [IsPullbackDefined i D] [IsPullbackDefined i E]
    (U : X.Opens) (a : Γ(divisorSheaf D, U)) (b : Γ(negativeTwist' E, U)) :
    (differenceSheafPullbackIso i D E).hom.app (i ⁻¹ᵁ U)
      (pullbackSectionHom i (differenceSheaf D E) U (i ⁻¹ᵁ U) le_rfl
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
          (divisorSheaf D) (negativeTwist' E) a b)) =
      Stacks.SheafOfModules.tensorSectionsAt B.sheaf.obj B.ringCatSheaf.property (op (i ⁻¹ᵁ U))
        (divisorSheaf (D.comap i)) (negativeTwist' (E.comap i))
        ((invertibleSheafPullbackIso i D).hom.app (i ⁻¹ᵁ U)
          (pullbackSectionHom i (divisorSheaf D) U (i ⁻¹ᵁ U) le_rfl a))
        ((pullbackIdealSheafComapIso i E inferInstance).hom.val.app (op (i ⁻¹ᵁ U))
          (pullbackSectionHom i (negativeTwist' E) U (i ⁻¹ᵁ U) le_rfl b)) := by
  let T : B.Modules ⥤ B.Modules ⥤ B.Modules := Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨B.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ B.presheaf
      (forget₂ CommRingCat RingCat) B.ringCatSheaf.property⟩
  let eD := (T.mapIso (invertibleSheafPullbackIso i D)).app
    ((Scheme.Modules.pullback i).obj (negativeTwist' E))
  let eE := (T.obj (divisorSheaf (D.comap i))).mapIso
    (pullbackIdealSheafComapIso i E inferInstance)
  change eE.hom.val.app (op (i ⁻¹ᵁ U)) (eD.hom.val.app (op (i ⁻¹ᵁ U))
    ((Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso i _ _).hom.app (i ⁻¹ᵁ U) _)) = _
  refine (congrArg (fun z => eE.hom.val.app (op (i ⁻¹ᵁ U))
    (eD.hom.val.app (op (i ⁻¹ᵁ U)) z))
    (Stacks.PullbackTensorIso.pullbackSectionHom_tensorSectionsAt i _ _ U a b)).trans ?_
  refine (congrArg (eE.hom.val.app (op (i ⁻¹ᵁ U)))
    (tensorSections_curriedMapLeft B _ _ _
      (invertibleSheafPullbackIso i D) (i ⁻¹ᵁ U) _ _)).trans ?_
  exact tensorSections_curriedMapRight B _ _ _
    (pullbackIdealSheafComapIso i E inferInstance) (i ⁻¹ᵁ U) _ _

private theorem differenceSheafBoundaryIso_tensor_canonical_preimage_of_iso
    [IsPullbackDefined i D] [IsPullbackDefined i E]
    (hD : D.comap i = ⊤) (hE : E.comap i = ⊤)
    (eT : differenceSheaf (D.comap i) (E.comap i) ≅
      differenceSheaf (⊤ : B.IdealSheafData) ⊤)
    (heT : eT = eqToIso (congrArg₂ differenceSheaf hD hE))
    (U : X.Opens) (b : Γ(negativeTwist' E, U))
    (hb : idealSheafSection E b = (1 : Γ(X, U))) :
    (differenceSheafPullbackIso i D E ≪≫ eT ≪≫ differenceSheafTopIso B).hom.app
      (i ⁻¹ᵁ U)
      (pullbackSectionHom i (differenceSheaf D E) U (i ⁻¹ᵁ U) le_rfl
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
          (divisorSheaf D) (negativeTwist' E) ((canonicalSection' D).eval (op U)) b)) =
      (1 : Γ(B, i ⁻¹ᵁ U)) := by
  let W := i ⁻¹ᵁ U
  let outer := (eT ≪≫ differenceSheafTopIso B).hom
  change outer.app W ((differenceSheafPullbackIso i D E).hom.app W _) = _
  refine (congrArg (outer.app W)
    (differenceSheafPullbackIso_tensorSection_preimage i D E U _ b)).trans ?_
  refine (congrArg (fun a => outer.app W
    (Stacks.SheafOfModules.tensorSectionsAt B.sheaf.obj B.ringCatSheaf.property (op W)
      (divisorSheaf (D.comap i)) (negativeTwist' (E.comap i)) a
      ((pullbackIdealSheafComapIso i E inferInstance).hom.val.app (op W)
        (pullbackSectionHom i (negativeTwist' E) U W le_rfl b))))
    (invertibleSheafPullbackIso_canonicalSection_preimage i D U)).trans ?_
  exact differenceSheafTopIso_eqToIso_tensor_canonical (D.comap i) (E.comap i)
    hD hE W eT heT _ (idealSheafSection_pullbackIdealOne_preimage i E U b hb)

/-- The exact boundary frame reads the pulled-back original pure tensor as one. -/
theorem differenceSheafBoundaryIso_tensor_canonical_preimage
    (hD : D.comap i = ⊤) (hE : E.comap i = ⊤)
    (U : X.Opens) (b : Γ(negativeTwist' E, U))
    (hb : idealSheafSection E b = (1 : Γ(X, U))) :
    (differenceSheafBoundaryIsoOfComapEqTop i D E hD hE).hom.app (i ⁻¹ᵁ U)
      (pullbackSectionHom i (differenceSheaf D E) U (i ⁻¹ᵁ U) le_rfl
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
          (divisorSheaf D) (negativeTwist' E) ((canonicalSection' D).eval (op U)) b)) =
      (1 : Γ(B, i ⁻¹ᵁ U)) := by
  let : IsPullbackDefined i D := by
    change IsEffectiveCartierDivisor (D.comap i)
    rw [hD]
    exact isEffectiveCartierDivisor_top
  let : IsPullbackDefined i E := by
    change IsEffectiveCartierDivisor (E.comap i)
    rw [hE]
    exact isEffectiveCartierDivisor_top
  let eT := eqToIso (congrArg₂ differenceSheaf hD hE)
  have hframe : differenceSheafBoundaryIsoOfComapEqTop i D E hD hE =
      differenceSheafPullbackIso i D E ≪≫ eT ≪≫ differenceSheafTopIso B := rfl
  refine (congrArg (fun e : (Scheme.Modules.pullback i).obj (differenceSheaf D E) ≅
      SheafOfModules.unit B.ringCatSheaf => e.hom.app (i ⁻¹ᵁ U)
        (pullbackSectionHom i (differenceSheaf D E) U (i ⁻¹ᵁ U) le_rfl
          (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
            (divisorSheaf D) (negativeTwist' E) ((canonicalSection' D).eval (op U)) b)))
    hframe).trans ?_
  exact differenceSheafBoundaryIso_tensor_canonical_preimage_of_iso i D E hD hE eT rfl U b hb

/-- The original ordinary representative of the same meromorphic `c` has coordinate one
in the specified difference boundary frame, over the full inverse-image open. -/
theorem frame_canonicalDifferenceRegularSection_preimage
    (hD : D.comap i = ⊤) (hE : E.comap i = ⊤) :
    (differenceSheafBoundaryIsoOfComapEqTop i D E hD hE).hom.app
      (i ⁻¹ᵁ canonicalDifferenceRegularOpen E)
      (pullbackSectionHom i (differenceSheaf D E) (canonicalDifferenceRegularOpen E)
        (i ⁻¹ᵁ canonicalDifferenceRegularOpen E) le_rfl
        (canonicalDifferenceRegularSection D E)) =
      (1 : Γ(B, i ⁻¹ᵁ canonicalDifferenceRegularOpen E)) := by
  let := isTensorInvertible_invertibleSheaf E
  let := Stacks.SheafOfModules.Scheme.isIso_over_nonvanishingOpen X
    (divisorSheaf E) (canonicalSection' E)
  have hpure : canonicalDifferenceRegularSection D E =
      Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
        (op (canonicalDifferenceRegularOpen E)) (divisorSheaf D) (negativeTwist' E)
        ((canonicalSection' D).eval (op (canonicalDifferenceRegularOpen E))) (idealOneSection E) :=
    regularCanonicalQuotient_eq_tensor D E (canonicalDifferenceRegularOpen E)
      (idealOneSection E) (idealSheafSection_idealOneSection E)
  exact (congrArg (fun s => (differenceSheafBoundaryIsoOfComapEqTop i D E hD hE).hom.app
    (i ⁻¹ᵁ canonicalDifferenceRegularOpen E)
    (pullbackSectionHom i (differenceSheaf D E) (canonicalDifferenceRegularOpen E)
      (i ⁻¹ᵁ canonicalDifferenceRegularOpen E) le_rfl s)) hpure).trans
    (differenceSheafBoundaryIso_tensor_canonical_preimage i D E hD hE
      (canonicalDifferenceRegularOpen E) (idealOneSection E) (idealSheafSection_idealOneSection E))

/-- Avoiding the negative divisor puts the entire original boundary in the regular open. -/
theorem preimage_canonicalDifferenceRegularOpen_eq_top
    (hE : ∀ y : B, i y ∉ E.support) : i ⁻¹ᵁ canonicalDifferenceRegularOpen E = ⊤ := by
  apply top_unique
  intro y _
  exact mem_nonvanishingOpen_canonicalSection_of_notMem_support E (i y) (hE y)

/-- Pull back the actual ordinary representative to the whole, possibly nonreduced boundary. -/
abbrev canonicalDifferenceBoundaryRegularSection (hE : ∀ y : B, i y ∉ E.support) :
    Γ((Scheme.Modules.pullback i).obj (differenceSheaf D E), ⊤) :=
  pullbackSectionHom i (differenceSheaf D E) (canonicalDifferenceRegularOpen E) ⊤
    (preimage_canonicalDifferenceRegularOpen_eq_top i E hE).ge
    (canonicalDifferenceRegularSection D E)

omit [IsEffectiveCartierDivisor D] in
/-- The chosen boundary representative is the actual pullback of the original local section. -/
theorem canonicalDifferenceBoundaryRegularSection_eq_pullback
    (hE : ∀ y : B, i y ∉ E.support) :
    canonicalDifferenceBoundaryRegularSection i D E hE =
      pullbackSectionHom i (differenceSheaf D E) (canonicalDifferenceRegularOpen E) ⊤
        (preimage_canonicalDifferenceRegularOpen_eq_top i E hE).ge
        (canonicalDifferenceRegularSection D E) := rfl

/-- The support-avoiding boundary frame is the specified native empty-comap frame. -/
theorem differenceSheafBoundaryIso_eq_ofComap
    (hD : ∀ y : B, i y ∉ D.support) (hE : ∀ y : B, i y ∉ E.support) :
    differenceSheafBoundaryIso i D E hD hE =
      differenceSheafBoundaryIsoOfComapEqTop i D E
        (comap_eq_top_of_avoids_support i D hD) (comap_eq_top_of_avoids_support i E hE) := rfl

/-- A coordinate identity on a full preimage restricts to the whole boundary. -/
theorem frame_pullbackSectionHom_top_of_preimage {X B : Scheme.{u}}
    (i : B ⟶ X) (L : X.Modules) (U : X.Opens)
    (e : (Scheme.Modules.pullback i).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (a : Γ(L, U)) (h : (⊤ : B.Opens) ≤ i ⁻¹ᵁ U)
    (ha : e.hom.app (i ⁻¹ᵁ U)
      (pullbackSectionHom i L U (i ⁻¹ᵁ U) le_rfl a) = (1 : Γ(B, i ⁻¹ᵁ U))) :
    e.hom.app ⊤ (pullbackSectionHom i L U ⊤ h a) = (1 : Γ(B, ⊤)) := by
  let N := (Scheme.Modules.pullback i).obj L
  have hres : N.presheaf.map (homOfLE h).op
      (pullbackSectionHom i L U (i ⁻¹ᵁ U) le_rfl a) = pullbackSectionHom i L U ⊤ h a :=
    congrArg (N.presheaf.map (homOfLE h).op) (pullbackSectionHom_preimage_self i L U a)
  refine (congrArg (e.hom.app ⊤) hres.symm).trans ?_
  refine (PresheafOfModules.naturality_apply e.hom.val (homOfLE h).op
    (pullbackSectionHom i L U (i ⁻¹ᵁ U) le_rfl a)).trans ?_
  exact (congrArg (B.presheaf.map (homOfLE h).op).hom ha).trans (map_one _)

end Stacks.Divisors
