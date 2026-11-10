/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.AffineLineLocalization
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension
public import Colib.CategoryTheory.Sites.Simplicial.ReducedConeContraction

/-!
# The Tate cone-to-quotient comparison at site fibers

Each native fiber preserves the two pushout squares and the monomorphism
given by the Laurent open. The contraction of the attached simplicial cone
therefore gives the weak equivalence of the original comparison map.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry.MotivicHomotopy

open Scheme SmoothSite CategoryTheory.PointedSimplicialPresheaf

variable (R : CommRingCat.{u})

/-- The actual pointed Laurent inclusion is degreewise a monomorphism. -/
private theorem mono_pointedLaurentOpen_right : Mono (pointedLaurentOpen R).right := by
  let : Mono (torusToAffineLine R) :=
    (forgetScheme (Spec R)).mono_of_mono_map
      (inferInstanceAs (Mono (PolynomialLaurent.laurentToPolynomial R)))
  apply (NatTrans.mono_iff_mono_app _).2
  intro U
  apply (NatTrans.mono_iff_mono_app _).2
  intro n
  apply (CategoryTheory.mono_iff_injective _).2
  intro f g h
  exact (cancel_mono (torusToAffineLine R)).1 h

private theorem reducedConeToTateCone_tateConeToSphere :
    reducedConeToMappingCofiber (pointedLaurentOpen R) ≫ tateConeToSphere R =
      toPoint (SmoothSite (Spec R)) (reducedCone (pointedTorus R)) ≫ tateSpherePoint R :=
  pushout.inr_desc _ _ _

/-- Collapsing the attached cone to the point gives the original
cone-to-quotient comparison as a stalkwise weak equivalence. -/
theorem stalkwiseWeakEquivalences_tateConeToSphere :
    stalkwiseWeakEquivalences (SmoothSite (Spec R)) (nisnevichTopology (Spec R))
      (tateConeToSphere R) := by
  intro Φ
  let C := SmoothSite (Spec R)
  let F := fiberAtPoint C Φ
  let : PreservesColimitsOfShape WalkingSpan F := by
    dsimp only [F, fiberAtPoint, PointedSimplicialPresheaf.forget]
    infer_instance
  let : Mono (F.map (pointedLaurentOpen R)) := by
    change Mono (Φ.presheafFiber.map (pointedLaurentOpen R).right)
    let : Mono (pointedLaurentOpen R).right := mono_pointedLaurentOpen_right R
    exact preserves_mono_of_preservesLimit _ _
  change SSet.IsRealizationWeakEquivalence (F.map (tateConeToSphere R))
  refine SSet.IsRealizationWeakEquivalence.pushout
    ((reducedMappingCofiber_isPushout (pointedLaurentOpen R)).map F)
    ((tateSphere_isPushout R).map F)
    (𝟙 _) (𝟙 _) (F.map (toPoint C (reducedCone (pointedTorus R)))) (F.map (tateConeToSphere R))
    (by simp) ?_ ?_ ?_ (SSet.IsRealizationWeakEquivalence.id _)
    (SSet.IsRealizationWeakEquivalence.id _)
    (isRealizationWeakEquivalence_fiberAtPoint_reducedConeToPoint Φ (pointedTorus R))
  · rw [Category.id_comp, ← F.map_comp]
    exact congrArg F.map ((point_isZero C).eq_of_tgt _ _)
  · rw [Category.id_comp, ← F.map_comp, toTateCone_tateConeToSphere]
  · rw [← F.map_comp, ← F.map_comp, reducedConeToTateCone_tateConeToSphere]

/-- The right leg of the Tate roof is inverted by the original affine-line localization. -/
theorem isIso_toAffineLineHomotopyCategory_map_tateConeToSphere :
    IsIso ((toAffineLineHomotopyCategory R).map (tateConeToSphere R)) :=
  (intervalWeakEquivalences _ _ (affineLineParameter R)).Q_inverts _
    (stalkwiseWeakEquivalences_le_intervalWeakEquivalences _ _ (affineLineParameter R) _
      (stalkwiseWeakEquivalences_tateConeToSphere R))

end AlgebraicGeometry.MotivicHomotopy

attribute [colib_tag "COL-0386"]
  AlgebraicGeometry.MotivicHomotopy.stalkwiseWeakEquivalences_tateConeToSphere
  AlgebraicGeometry.MotivicHomotopy.isIso_toAffineLineHomotopyCategory_map_tateConeToSphere
