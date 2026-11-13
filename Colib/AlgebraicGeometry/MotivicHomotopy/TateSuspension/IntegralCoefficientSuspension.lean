/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.SmashCohomology
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.TorusSmashCohomology
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TatePowerIntegralBond

/-!
# The integral coefficient comparison for Tate suspension

The reduced torus bond gives a coefficient isomorphism through the
original signed shift. Its ordinary reduced Hom comparison is then
followed by the actual Tate boundary on the smashed Laurent sequence.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers

universe u w₁ w₂ w₃ w₄ w₅

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w₁} (LargePresheaves k)]
  [HasDerivedCategory.{w₂} (LargeSheaves k)]
  [HasDerivedCategory.{w₃}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₄} ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w₅} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "Rₖ" => CommRingCat.of k
local notation "Sₖ" => Spec Rₖ
local notation "Cₖ" => SmoothSite Sₖ
local notation "Jₖ" => SmoothSite.nisnevichTopology Sₖ

omit [PerfectField k] [HasDerivedCategory (LargePresheaves k)]
  [HasDerivedCategory (LargeSheaves k)]
  [HasDerivedCategory ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})]
  [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
/-- The original reduced derived chains in the universe of the motivic coefficients. -/
abbrev motivicReducedDerivedChains :
    PointedSimplicialPresheaf.{u + 1} Cₖ ⥤ DerivedCategory (Sheaf Jₖ (LargeAb k)) :=
  reducedDerivedChains.{w₃, u + 1} Cₖ Jₖ

local notation "E" => motivicReducedDerivedChains k
local notation "N" => reducedTorusSectionsDerivedFunctor k
local notation "F" =>
  (Functor.mapDerivedCategory (toSheaf k) :
    DerivedCategory (LargeSheaves k) ⥤ DerivedCategory (Sheaf Jₖ (LargeAb k)))
local notation "Qₜ" =>
  (DerivedCategory.Q : CochainComplex (LargeSheaves k) ℤ ⥤ DerivedCategory (LargeSheaves k))

omit [HasDerivedCategory
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})] in
/-- The signed integral coefficient map identifies the actual reduced
torus coefficient after the original derived quotient. -/
def integralTorusBondIso (q : ℕ) :
    (Qₜ).obj (motivicComplex k q) ≅
      (N).obj ((Qₜ).obj ((motivicComplex k (q + 1))⟦(1 : ℤ)⟧)) :=
  let f := motivicDerivedTransferParameterProduct k q ≫
    (reducedTorusSectionsDerivedProjection k).app _
  @asIso _ _ _ _ f (isIso_motivicDerivedReducedTransferParameterProduct k q)

omit [PerfectField k] [HasDerivedCategory (LargePresheaves k)]
  [HasDerivedCategory ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})]
  [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
/-- The derived quotient commutes with the underlying sheaf of an actual transfer complex. -/
def ordinaryCoefficientDerivedIso
    (K : CochainComplex (LargeSheaves k) ℤ) :
    (F).obj ((Qₜ).obj K) ≅
      DerivedCategory.Q.obj (((toSheaf k).mapHomologicalComplex (.up ℤ)).obj K) :=
  (toSheaf k).mapDerivedCategoryFactors.app K

omit [PerfectField k] in
/-- The original torus comparison followed by the original Tate boundary,
for any actual coefficient isomorphism and vanishing of the middle term. -/
@[no_expose]
def tateSuspensionDerivedHomEquiv
    (X : PointedSimplicialPresheaf.{u + 1} Cₖ)
    {K L : DerivedCategory (LargeSheaves k)} (m : ℤ)
    (a : K ≅ (N).obj L)
    (b : Subsingleton ((E).obj (Under.smash X (liftedPointedAffineLine Rₖ)) ⟶
      ((F).obj L)⟦m + 1⟧))
    (b' : Subsingleton (((E).obj (Under.smash X (liftedPointedAffineLine Rₖ)))⟦(1 : ℤ)⟧ ⟶
      ((F).obj L)⟦m + 1⟧)) :
    ((E).obj X ⟶ ((F).obj K)⟦m⟧) ≃
      ((E).obj (Under.smash X (liftedTateSphere Rₖ)) ⟶ ((F).obj L)⟦m + 1⟧) := by
  let D := DerivedCategory (LargeSheaves k)
  let D₀ := DerivedCategory (Sheaf Jₖ (LargeAb k))
  let M := (E).obj (Under.smash X (liftedPointedTorus k))
  let e₁ := (shiftFunctor D₀ m).mapIso ((F).mapIso a) ≪≫
    ((F).commShiftIso m).symm.app ((N).obj L) ≪≫
    (F).mapIso (((N).commShiftIso m).symm.app L)
  let e₂ := ((F).commShiftIso m).app L
  let e₃ := ((shiftFunctorAdd D₀ m (1 : ℤ)).app ((F).obj L)).symm
  let S := shiftFunctor D₀ (1 : ℤ)
  let e₄ := Equiv.ofBijective (S.map : (M ⟶ ((F).obj L)⟦m⟧) → _)
    ⟨S.map_injective, S.map_surjective⟩
  let e₅ := Equiv.ofBijective (fun f => tateSmashConnecting Rₖ X ≫ f)
    (bijective_precomp_tateSmashConnecting Rₖ X _ b b')
  exact e₁.homToEquiv.trans
    ((torusSmashDerivedHomEquiv k X ((shiftFunctor D m).obj L)).symm.trans
      (e₂.homToEquiv.trans (e₄.trans (e₃.homToEquiv.trans e₅))))

omit [PerfectField k] in
/-- The Tate-boundary comparison is natural in the original pointed presheaf. -/
theorem tateSuspensionDerivedHomEquiv_precomp
    {X Y : PointedSimplicialPresheaf.{u + 1} Cₖ} (f : X ⟶ Y)
    {K L : DerivedCategory (LargeSheaves k)} (m : ℤ)
    (a : K ≅ (N).obj L)
    (bX : Subsingleton ((E).obj (Under.smash X (liftedPointedAffineLine Rₖ)) ⟶
      ((F).obj L)⟦m + 1⟧))
    (bX' : Subsingleton (((E).obj (Under.smash X (liftedPointedAffineLine Rₖ)))⟦(1 : ℤ)⟧ ⟶
      ((F).obj L)⟦m + 1⟧))
    (bY : Subsingleton ((E).obj (Under.smash Y (liftedPointedAffineLine Rₖ)) ⟶
      ((F).obj L)⟦m + 1⟧))
    (bY' : Subsingleton (((E).obj (Under.smash Y (liftedPointedAffineLine Rₖ)))⟦(1 : ℤ)⟧ ⟶
      ((F).obj L)⟦m + 1⟧))
    (g : (E).obj Y ⟶ ((F).obj K)⟦m⟧) :
    tateSuspensionDerivedHomEquiv k X m a bX bX' ((E).map f ≫ g) =
      (E).map (Under.smashMap f (𝟙 (liftedTateSphere Rₖ))) ≫
        tateSuspensionDerivedHomEquiv k Y m a bY bY' g := by
  let D := DerivedCategory (LargeSheaves k)
  let D₀ := DerivedCategory (Sheaf Jₖ (LargeAb k))
  let L' := (shiftFunctor D m).obj L
  let e₁ := (shiftFunctor D₀ m).mapIso ((F).mapIso a) ≪≫
    ((F).commShiftIso m).symm.app ((N).obj L) ≪≫
    (F).mapIso (((N).commShiftIso m).symm.app L)
  let e₂ := ((F).commShiftIso m).app L
  let e₃ := ((shiftFunctorAdd D₀ m (1 : ℤ)).app ((F).obj L)).symm
  let S := shiftFunctor D₀ (1 : ℤ)
  let t := (E).map f
  let u := (E).map (Under.smashMap f (𝟙 (liftedPointedTorus k)))
  let v := (E).map (Under.smashMap f (𝟙 (liftedTateSphere Rₖ)))
  let δX := tateSmashConnecting Rₖ X
  let δY := tateSmashConnecting Rₖ Y
  let h := (torusSmashDerivedHomEquiv k Y L').symm (g ≫ e₁.hom)
  have hτ : (torusSmashDerivedHomEquiv k X L').symm (t ≫ (g ≫ e₁.hom)) = u ≫ h := by
    apply (torusSmashDerivedHomEquiv k X L').injective
    rw [Equiv.apply_symm_apply, torusSmashDerivedHomEquiv_precomp, Equiv.apply_symm_apply]
  have hδ : v ≫ δY = δX ≫ S.map u := tateSmashConnecting_naturality Rₖ f
  unfold tateSuspensionDerivedHomEquiv
  simp only [Equiv.trans_apply, Iso.homToEquiv_apply, Equiv.ofBijective_apply]
  change δX ≫ S.map ((torusSmashDerivedHomEquiv k X L').symm
      ((t ≫ g) ≫ e₁.hom) ≫ e₂.hom) ≫ e₃.hom =
    v ≫ δY ≫ S.map (h ≫ e₂.hom) ≫ e₃.hom
  calc
    _ = δX ≫ S.map (u ≫ (h ≫ e₂.hom)) ≫ e₃.hom := by
      rw [Category.assoc t, hτ, Category.assoc u]
    _ = (δX ≫ S.map u) ≫ S.map (h ≫ e₂.hom) ≫ e₃.hom := by
      rw [S.map_comp, Category.assoc (S.map u), Category.assoc δX]
    _ = _ := by rw [← hδ, Category.assoc]

omit [PerfectField k] in
/-- Postcomposing at both ends transports a natural comparison of derived Hom sets. -/
theorem tateSuspensionDerivedHomEquiv_congr_precomp
    {X Y : PointedSimplicialPresheaf.{u + 1} Cₖ} (f : X ⟶ Y)
    {K L : DerivedCategory (LargeSheaves k)} (m : ℤ)
    (a : K ≅ (N).obj L)
    (bX : Subsingleton ((E).obj (Under.smash X (liftedPointedAffineLine Rₖ)) ⟶
      ((F).obj L)⟦m + 1⟧))
    (bX' : Subsingleton (((E).obj (Under.smash X (liftedPointedAffineLine Rₖ)))⟦(1 : ℤ)⟧ ⟶
      ((F).obj L)⟦m + 1⟧))
    (bY : Subsingleton ((E).obj (Under.smash Y (liftedPointedAffineLine Rₖ)) ⟶
      ((F).obj L)⟦m + 1⟧))
    (bY' : Subsingleton (((E).obj (Under.smash Y (liftedPointedAffineLine Rₖ)))⟦(1 : ℤ)⟧ ⟶
      ((F).obj L)⟦m + 1⟧))
    {A B : DerivedCategory (Sheaf Jₖ (LargeAb k))}
    (i : A ⟶ ((F).obj K)⟦m⟧) (j : ((F).obj L)⟦m + 1⟧ ⟶ B)
    (g : (E).obj Y ⟶ A) :
    tateSuspensionDerivedHomEquiv k X m a bX bX' (((E).map f ≫ g) ≫ i) ≫ j =
      (E).map (Under.smashMap f (𝟙 (liftedTateSphere Rₖ))) ≫
        (tateSuspensionDerivedHomEquiv k Y m a bY bY' (g ≫ i) ≫ j) := by
  rw [Category.assoc, tateSuspensionDerivedHomEquiv_precomp]
  exact Category.assoc _ _ _

/-- The integral Tate suspension on the actual reduced motivic cohomology groups. -/
@[no_expose]
def integralTateSuspensionHomEquiv (X : PointedSimplicialPresheaf.{u + 1} Cₖ)
    (m : ℤ) (q : ℕ) :
    ((E).obj X ⟶ (DerivedCategory.Q.obj (motivicSheafComplex k q))⟦m⟧) ≃
      ((E).obj (Under.smash X (liftedTateSphere Rₖ)) ⟶
        (DerivedCategory.Q.obj (motivicSheafComplex k (q + 1)))⟦m + 2⟧) := by
  let K := motivicComplex k q
  let L := motivicComplex k (q + 1)
  let D := DerivedCategory (Sheaf Jₖ (LargeAb k))
  let s := shiftFunctor D m
  let t := shiftFunctor D (m + 1)
  let L₀ := DerivedCategory.Q.obj (motivicSheafComplex k (q + 1))
  let e₁ : s.obj ((F).obj ((Qₜ).obj K)) ≅
      s.obj (DerivedCategory.Q.obj (motivicSheafComplex k q)) :=
    s.mapIso (ordinaryCoefficientDerivedIso k K)
  let F₀ := (toSheaf k).mapHomologicalComplex (.up ℤ)
  let e₂ := ordinaryCoefficientDerivedIso k (L⟦(1 : ℤ)⟧) ≪≫
    DerivedCategory.Q.mapIso ((F₀.commShiftIso (1 : ℤ)).app L) ≪≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).app (motivicSheafComplex k (q + 1))
  let e₃ := t.mapIso e₂ ≪≫
    ((shiftFunctorAdd' D 1 (m + 1) (m + 2) (by omega)).app L₀).symm
  have h (i : ℤ) := subsingleton_derivedHom_smashPointedAffineLine k
    (motivicSheafComplex k (q + 1)) i (motivicAffineLineRepresentative k i (q + 1))
    (motivicAffineLineRepresentativeHomEquiv k i (q + 1)) X
  let Y := (E).obj (Under.smash X (liftedPointedAffineLine Rₖ))
  let b := e₃.homToEquiv (Z := Y)
  let b' := e₃.homToEquiv (Z := Y⟦(1 : ℤ)⟧)
  let : Subsingleton (Y ⟶ L₀⟦m + 2⟧) := h (m + 2)
  let : Subsingleton (Y⟦(1 : ℤ)⟧ ⟶ L₀⟦m + 2⟧) :=
    subsingleton_shiftedHom_of_subsingleton _ _ (m + 2) (h (m + 2 - 1))
  exact e₁.symm.homToEquiv.trans
    ((tateSuspensionDerivedHomEquiv k X m (integralTorusBondIso k q)
      b.injective.subsingleton b'.injective.subsingleton).trans
        e₃.homToEquiv)

set_option maxHeartbeats 400000 in
-- Compare the cochain-shift and derived-shift presentations of both coefficient complexes.
/-- Integral suspension commutes with restriction along the original pointed map. -/
theorem integralTateSuspensionHomEquiv_precomp
    {X Y : PointedSimplicialPresheaf.{u + 1} Cₖ} (f : X ⟶ Y) (m : ℤ) (q : ℕ)
    (g : (E).obj Y ⟶ (DerivedCategory.Q.obj (motivicSheafComplex k q))⟦m⟧) :
    integralTateSuspensionHomEquiv k X m q ((E).map f ≫ g) =
      (E).map (Under.smashMap f (𝟙 (liftedTateSphere Rₖ))) ≫
        integralTateSuspensionHomEquiv k Y m q g := by
  unfold integralTateSuspensionHomEquiv
  simp only [Equiv.trans_apply, Iso.homToEquiv_apply]
  exact tateSuspensionDerivedHomEquiv_congr_precomp k f m (integralTorusBondIso k q)
    _ _ _ _ _ _ g

end AlgebraicGeometry.MotivicHomotopy
