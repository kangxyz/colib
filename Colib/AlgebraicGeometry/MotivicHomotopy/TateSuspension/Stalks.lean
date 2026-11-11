/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
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
  let : Mono (multiplicativeGroupOpen (Spec R)) :=
    (forgetScheme (Spec R)).mono_of_mono_map
      (inferInstanceAs (Mono (multiplicativeGroupBaseChangeToAdditive (Spec R))))
  apply (NatTrans.mono_iff_mono_app _).2
  intro U
  apply (NatTrans.mono_iff_mono_app _).2
  intro n
  apply (CategoryTheory.mono_iff_injective _).2
  intro f g h
  exact (cancel_mono (multiplicativeGroupOpen (Spec R))).1 h

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

/-- The collapse becomes an isomorphism in the pointed Nisnevich localization. -/
theorem isIso_toStalkwiseHomotopyCategory_map_tateConeToSphere :
    IsIso ((toStalkwiseHomotopyCategory (SmoothSite (Spec R))
      (nisnevichTopology (Spec R))).map (tateConeToSphere R)) :=
  (stalkwiseWeakEquivalences (SmoothSite (Spec R)) (nisnevichTopology (Spec R))).Q_inverts _
    (stalkwiseWeakEquivalences_tateConeToSphere R)

attribute [colib_tag "COL-1020"]
  stalkwiseWeakEquivalences_tateConeToSphere
  isIso_toStalkwiseHomotopyCategory_map_tateConeToSphere

attribute [colib_ref "MorelVoevodsky1999" "Section 3.2, proof of Lemma 2.15, p. 111"
  "adaptation" "The collapse to the pointed Tate quotient as a simplicial weak equivalence"]
  stalkwiseWeakEquivalences_tateConeToSphere

end AlgebraicGeometry.MotivicHomotopy
