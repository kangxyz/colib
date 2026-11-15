/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Triangle
public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.AffineContraction
public import Colib.AlgebraicGeometry.Sites.Smooth.AffineLine.CylinderRestriction
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineSectionNaturality

/-! # Affine-line contraction of open pairs -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction

universe u w w'

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} {U X : SmoothSite S}

/-- The projection of the literal affine-line cylinder of an open pair. -/
def affinePairProjectionSquare (j : U ⟶ X) : Square (SmoothSite S) where
  f₁₂ := (projection (additiveGroupObject S)).app U
  f₁₃ := affineLineCylinder.map j
  f₂₄ := j
  f₃₄ := (projection (additiveGroupObject S)).app X
  fac := ((projection (additiveGroupObject S)).naturality j).symm

instance (j : U ⟶ X) [IsOpenImmersion j.left] :
    IsOpenImmersion (affinePairProjectionSquare j).f₁₃.left :=
  MorphismProperty.of_isPullback (affineLineCylinder_map_isPullback j).flip inferInstance

/-- The constant affine section of the actual cylinder of an open pair. -/
def affinePairSectionSquare (R : CommRingCat.{u}) {U X : SmoothSite (Spec R)}
    (j : U ⟶ X) (a : R) : Square (SmoothSite (Spec R)) where
  f₁₂ := nativeAffineSection R U a
  f₁₃ := j
  f₂₄ := affineLineCylinder.map j
  f₃₄ := nativeAffineSection R X a
  fac := nativeAffineSection_naturality R j a

end AlgebraicGeometry.Scheme.SmoothSite

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

attribute [local irreducible] Cor.graphFunctor transferRepresentable

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [hExt : HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Projection from the affine-line cylinder of an open pair induces an
isomorphism on its original relative motive. -/
theorem isIso_effectivePairMotiveMap_affinePairProjection
    {U X : SmoothSite (Spec (.of k))} (j : U ⟶ X) [IsOpenImmersion j.left] :
    IsIso (effectivePairMotiveMap k (SmoothSite.affinePairProjectionSquare j)) := by
  let : IsOpenImmersion (SmoothSite.affinePairProjectionSquare j).f₂₄.left :=
    inferInstanceAs (IsOpenImmersion j.left)
  apply effectivePairMotiveMap_isIso_of_isIso_components k (SmoothSite.affinePairProjectionSquare j)
  · exact @isIso_effectiveSmoothMotive_affineLineProjection k _ _ _ _ hExt U
  · exact @isIso_effectiveSmoothMotive_affineLineProjection k _ _ _ _ hExt X

/-- The constant section is the inverse to projection on relative motives. -/
theorem isIso_effectivePairMotiveMap_affinePairSection
    {U X : SmoothSite (Spec (.of k))} (j : U ⟶ X) [IsOpenImmersion j.left] (a : k) :
    IsIso (effectivePairMotiveMap k (SmoothSite.affinePairSectionSquare (.of k) j a)) := by
  let P := effectivePairMotiveFunctor k
  let J : Arrow (SmoothSite (Spec (.of k))) := Arrow.mk j
  let K : Arrow (SmoothSite (Spec (.of k))) := Arrow.mk (affineLineCylinder.map j)
  let s : J ⟶ K := Arrow.homMk' (nativeAffineSection (.of k) U a)
    (nativeAffineSection (.of k) X a) (nativeAffineSection_naturality (.of k) j a)
  let p : K ⟶ J := Arrow.homMk' ((projection (additiveGroupObject (Spec (.of k)))).app U)
    ((projection (additiveGroupObject (Spec (.of k)))).app X)
    ((projection (additiveGroupObject (Spec (.of k)))).naturality j).symm
  have hs : s ≫ p = 𝟙 J := by
    apply Arrow.hom_ext
    · exact nativeAffineSection_projection (.of k) U a
    · exact nativeAffineSection_projection (.of k) X a
  let : IsIso (P.map p) := isIso_effectivePairMotiveMap_affinePairProjection k j
  have h : IsIso (P.map s ≫ P.map p) := by
    rw [← P.map_comp, hs, P.map_id]
    infer_instance
  exact IsIso.of_isIso_comp_right (P.map s) (P.map p)

end AlgebraicGeometry.MotivicHomotopy
