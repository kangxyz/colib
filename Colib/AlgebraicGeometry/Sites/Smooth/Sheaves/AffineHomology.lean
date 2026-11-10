/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.SheafifiedChains
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Detecting zero homology sheaves on affine smooth objects

Adapted from a6805c4 `Sites/Smooth/Affine/SheafIso.lean` and
`Sites/Smooth/Sheaves/IntegralAffineHomology.lean`. The genuine boundary-one
producer vanishes on every affine, so the actual affine open cover suffices;
no normal-component decomposition is needed. This is a detection bridge,
not a proof of the boundary-one coefficient's acyclicity.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped ZeroObject

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]

/-- A sieve containing all affine-source arrows covers, by the genuine affine open cover. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Affine/SheafIso.lean"
  "adaptation" "Actual affine open covers generate covering sieves"]
theorem sieve_mem_of_affine_arrows (X : SmoothSite (Spec (.of k))) (T : Sieve X)
    (h : ∀ (U : SmoothSite (Spec (.of k))) [IsAffine U.left] (f : U ⟶ X), T f) :
    T ∈ nisnevichTopology (Spec (.of k)) X := by
  let U (i : X.left.affineCover.I₀) : SmoothSite (Spec (.of k)) :=
    mk (X.left.affineCover.f i ≫ X.hom)
  let f (i : X.left.affineCover.I₀) : U i ⟶ X :=
    homMk (X.left.affineCover.f i) rfl
  apply (mem_nisnevichTopology_iff).mpr
  refine ⟨Presieve.ofArrows U f, ?_, ?_⟩
  · change (Presieve.ofArrows U f).map (forgetScheme (Spec (.of k))) ∈ Nisnevich.precoverage X.left
    rw [Presieve.map_ofArrows]
    exact Nisnevich.zariskiPrecoverage_le_precoverage _ X.left.affineCover.mem₀
  · rw [Presieve.ofArrows_le_iff]
    intro i
    let : IsAffine (U i).left := by dsimp [U]; infer_instance
    exact h (U i) (f i)


/-- A presheaf vanishing on affine sources has zero ordinary Nisnevich sheafification. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Sheaves/IntegralAffineHomology.lean"
  "adaptation" "Vanishing on every affine implies zero sheafification"]
theorem isZero_sheafify_of_affine
    (F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (h : ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left],
      IsZero (F.obj (op X))) :
    IsZero ((presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj F) := by
  let J := nisnevichTopology (Spec (.of k))
  let z : F ⟶ 0 := 0
  have hi : Presheaf.IsLocallyInjective J z := by
    constructor
    intro X x y _
    apply sieve_mem_of_affine_arrows k
    intro U _ f
    have := AddCommGrpCat.subsingleton_of_isZero (h U)
    exact Subsingleton.elim _ _
  have hs : Presheaf.IsLocallySurjective J z := by
    constructor
    intro X x
    apply sieve_mem_of_affine_arrows k
    intro U _ f
    have hz : IsZero ((0 : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤
        AddCommGrpCat.{u + 1}).obj (op U)) :=
      ((_root_.CategoryTheory.evaluation _ _).obj (op U)).map_isZero (isZero_zero _)
    have := AddCommGrpCat.subsingleton_of_isZero hz
    exact ⟨0, Subsingleton.elim _ _⟩
  have hz : IsIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map z) :=
    (J.W_iff z).mp (J.W_of_isLocallyBijective z)
  exact ((presheafToSheaf J AddCommGrpCat.{u + 1}).map_isZero (isZero_zero _)).of_iso
    (asIso ((presheafToSheaf J AddCommGrpCat.{u + 1}).map z))

/-- Vanishing of evaluated homology on affines implies vanishing of
ordinary homology sheaves, in every chain degree. -/
theorem isZero_sheafified_homology_of_affine
    (K : ChainComplex ((SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ℕ)
    (n : ℕ)
    (h : ∀ (X : SmoothSite (Spec (.of k))) [IsAffine X.left],
      IsZero ((K.homology n).obj (op X))) :
    IsZero ((((presheafToSheaf (nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).mapHomologicalComplex (.down ℕ)).obj K).homology n) :=
  (isZero_sheafify_of_affine k (K.homology n) h).of_iso
    ((K.sc n).mapHomologyIso
      (presheafToSheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}))

end AlgebraicGeometry.Scheme.SmoothSite

