/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleIntegralBase
public import Mathlib.CategoryTheory.Filtered.Final

/-! # Returning an actual integral neighborhood to the small index

Initiality does not mean fullness. The comparison with a prescribed old small
stage is obtained by a common cone in a costructured-arrow category, not by
pretending an original-neighborhood morphism lifts verbatim to the small model.
The returned small stage is not asserted to be integral.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} [QuasiSeparatedSpace S]
  (X : SmoothSite S) (s : GeometricPoint X.left)

omit [QuasiSeparatedSpace S] in
/-- A genuine small refinement over the prescribed stage, factoring through the
specified original neighborhood with an exact equality of original arrows. -/
theorem exists_smallEtale_refinement_through
    (i : SmallEtaleNeighborhood X s) (A : EtaleNeighborhood X s.hom)
    (v : A ⟶ (smallEtaleNeighborhoodInclusion X s).obj i) :
    ∃ (a : Over i)
      (t : (smallEtaleNeighborhoodInclusion X s).obj a.left ⟶ A),
      t ≫ v = (smallEtaleNeighborhoodInclusion X s).map a.hom := by
  let F := smallEtaleNeighborhoodInclusion X s
  let j := Functor.Initial.lift F A
  let t₀ : F.obj j ⟶ A := Functor.Initial.homToLift F A
  let : IsCofiltered (CostructuredArrow F (F.obj i)) :=
    (Functor.initial_iff_isCofiltered_costructuredArrow F).mp inferInstance (F.obj i)
  obtain ⟨k, f, g, h⟩ :=
    exists_eq_of_isCofiltered_costructuredArrow F (t₀ ≫ v) (𝟙 (F.obj i))
  refine ⟨Over.mk g, F.map f ≫ t₀, ?_⟩
  simpa only [Category.assoc, Category.comp_id, Over.mk_left, Over.mk_hom] using h

/-- The lifted small arrow preserves the actual marked point; no replacement
geometric point or new affine presentation is chosen. -/
theorem smallEtale_refinement_through_mark
    {i : SmallEtaleNeighborhood X s} {A : EtaleNeighborhood X s.hom}
    (a : Over i) (t : (smallEtaleNeighborhoodInclusion X s).obj a.left ⟶ A) :
    etaleNeighborhoodMark X s.hom ((smallEtaleNeighborhoodInclusion X s).obj a.left) ≫
        ((etaleNeighborhoodToSmooth X s.hom).map t).left =
      etaleNeighborhoodMark X s.hom A :=
  etaleNeighborhoodMark_map X s.hom t

/-- The native strict-local cone factors through the same chosen small-to-original
arrow, exactly, before any component-open preimages are formed. -/
theorem smallEtale_refinement_through_cone
    (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
    {i : SmallEtaleNeighborhood X s} {A : EtaleNeighborhood X s.hom}
    (a : Over i) (t : (smallEtaleNeighborhoodInclusion X s).obj a.left ⟶ A) :
    (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app a.left ≫
        ((etaleNeighborhoodToSmooth X s.hom).map t).left =
      (etaleNeighborhoodStrictHenselizationCone X B hX s).π.app A :=
  (etaleNeighborhoodStrictHenselizationCone X B hX s).w t

/-- First choose the genuine integral marked base, then a small index mapping
through it over the old stage. Integrality belongs to A, not to a.left. -/
theorem exists_integral_etaleNeighborhood_with_small_refinement
    [IsNormal X.left] [IsLocallyNoetherian X.left]
    (i : SmallEtaleNeighborhood X s) :
    ∃ (A : EtaleNeighborhood X s.hom)
      (v : A ⟶ (smallEtaleNeighborhoodInclusion X s).obj i),
      IsIntegral ((etaleNeighborhoodToSmooth X s.hom).obj A).left ∧
      IsNoetherian ((etaleNeighborhoodToSmooth X s.hom).obj A).left ∧
      IsOpenImmersion (((etaleNeighborhoodToSmooth X s.hom).map v).left) ∧
      IsClosedImmersion (((etaleNeighborhoodToSmooth X s.hom).map v).left) ∧
      ∃ (a : Over i)
        (t : (smallEtaleNeighborhoodInclusion X s).obj a.left ⟶ A),
        t ≫ v = (smallEtaleNeighborhoodInclusion X s).map a.hom := by
  obtain ⟨A, v, hInt, hNoeth, hOpen, hClosed, e, he⟩ :=
    exists_integral_etaleNeighborhood_refinement X s.hom
      ((smallEtaleNeighborhoodInclusion X s).obj i)
  obtain ⟨a, t, ht⟩ := exists_smallEtale_refinement_through X s i A v
  exact ⟨A, v, hInt, hNoeth, hOpen, hClosed, a, t, ht⟩

end AlgebraicGeometry.Scheme.SmoothSite
