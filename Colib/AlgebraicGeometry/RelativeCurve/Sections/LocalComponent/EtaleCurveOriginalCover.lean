/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleLimit
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.ActualClopenAffineChart
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.ClopenModelProjectiveChart

/-! # The original finite cover on the actual small-stage clopen -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {C N : Scheme.{u}} (p : C ⟶ X.left)
  {A : Type u} [CommRing A] (v : C ⟶ N) (q : N ⟶ Spec (.of A))
  (b : X.left ⟶ Spec (.of A)) (h : IsPullback v p q b)
  (i : SmallEtaleNeighborhood X s)

include h in
/-- Compose the two actual base-change squares, without replacing the stage curve. -/
theorem etaleCurveStage_original_isPullback :
    IsPullback (pullback.snd ((smallEtaleNeighborhoodOver X s).obj i).hom p ≫ v)
      ((etaleCurveStructure X s p).app i) q
      (((smallEtaleNeighborhoodOver X s).obj i).hom ≫ b) :=
  (IsPullback.of_hasPullback ((smallEtaleNeighborhoodOver X s).obj i).hom p).flip.paste_horiz h

include v h in
/-- The scalar map belongs to the actual native affine stage; only its ring-map
presentation is chosen. The original finite cover is then restricted to the same clopen. -/
theorem exists_etaleCurve_clopen_original_cover
    (U : ((etaleCurveDiagram X s p).obj i).Opens) [IsClosedImmersion U.ι]
    (π : N ⟶ projectiveLine A) [IsFinite π]
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = q) :
    let R := ((smallEtaleNeighborhoodInclusion X s).obj i).obj.left.unop
    ∃ (f : A →+* R)
      (_hf : Spec.map (CommRingCat.ofHom f) =
        ((smallEtaleNeighborhoodOver X s).obj i).hom ≫ b)
      (hpb : IsPullback
        (pullback.snd ((smallEtaleNeighborhoodOver X s).obj i).hom p ≫ v)
        ((etaleCurveStructure X s p).app i) q (Spec.map (CommRingCat.ofHom f))),
      let πU := U.ι ≫ projectiveLineCoverOfActualCartesian q f _ _ hpb π hπ
      IsFinite πU ∧ πU ≫ (projectiveLine R ↘ Spec (.of R)) =
        U.ι ≫ (etaleCurveStructure X s p).app i := by
  intro R
  obtain ⟨f, hf⟩ := Spec.map_surjective (((smallEtaleNeighborhoodOver X s).obj i).hom ≫ b)
  have hpb : IsPullback
      (pullback.snd ((smallEtaleNeighborhoodOver X s).obj i).hom p ≫ v)
      ((etaleCurveStructure X s p).app i) q (Spec.map f) := by
    rw [hf]
    exact etaleCurveStage_original_isPullback X s p v q b h i
  let πi := projectiveLineCoverOfActualCartesian q f.hom _ _ hpb π hπ
  have hπi : IsFinite πi :=
    projectiveLineCoverOfActualCartesian_isFinite q f.hom _ _ hpb π hπ
  refine ⟨f.hom, hf, hpb,
    @finite_projectiveLineCover_clopenModel R _ _ _ U.ι πi inferInstance hπi, ?_⟩
  exact projectiveLineCover_clopenModel_structure U.ι _ πi
    (projectiveLineCoverOfActualCartesian_structure q f.hom _ _ hpb π hπ)

end AlgebraicGeometry.Scheme.SmoothSite
