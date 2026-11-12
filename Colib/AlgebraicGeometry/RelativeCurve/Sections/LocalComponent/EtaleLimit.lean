/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.LimitDescent
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.StrictLocal
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.StrictHenselization
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal

/-!
# The original curve over the actual small etale-neighborhood limit

The original smooth-site affine neighborhoods and their canonical strict-henselization cone
are used unchanged. Pulling back the original curve gives a genuine Cartesian diagram with
affine transitions and the actual strict-local curve as limit. An actual normal component
then descends after any specified stage. Neither the strict henselization nor the proper curve
is declared to be an object of the smooth site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

attribute [local instance] IsCofiltered.isConnected

variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (B : BigEtaleSite.{u}) (hX : B.Contains X.left) (s : GeometricPoint X.left)

/-- The original small affine-neighborhood diagram, viewed over the original smooth object. -/
def smallEtaleNeighborhoodOver : SmallEtaleNeighborhood X s ⥤ Over X.left :=
  (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).toOver X.left
    (fun i => (etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i)).left)
    (fun f => etaleNeighborhoodMap_hom X s.hom ((smallEtaleNeighborhoodInclusion X s).map f))

/-- The actual strict-henselization cone, with its exact original structure map. -/
def smallEtaleNeighborhoodOverCone : Cone (smallEtaleNeighborhoodOver X s) where
  pt := Over.mk (strictHenselizationToBase B X.left hX s)
  π :=
    { app := fun i => Over.homMk
        ((smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app i)
        (smallEtaleNeighborhoodStrictHenselizationCone_π_comp_hom X B hX s i)
      naturality := fun i j f => by
        apply Over.OverMorphism.ext
        exact (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.naturality f }

/-- The original small affine neighborhoods have the actual strict henselization as limit over
its original base, not merely as an unspecified isomorphic scheme. -/
def smallEtaleNeighborhoodOverConeIsLimit : IsLimit (smallEtaleNeighborhoodOverCone X B hX s) :=
  isLimitOfReflects (Over.forget X.left)
    (smallEtaleNeighborhoodStrictHenselizationConeIsLimit X B hX s)

variable {N : Scheme.{u}} (p : N ⟶ X.left)

/-- The original curve pulled back to each original affine etale neighborhood. -/
def etaleCurveDiagram : SmallEtaleNeighborhood X s ⥤ Scheme.{u} :=
  smallEtaleNeighborhoodOver X s ⋙ Over.pullback p ⋙ Over.forget N

/-- The cone on actual curve pullbacks, with strict-local base-change vertex. -/
def etaleCurveCone : Cone (etaleCurveDiagram X s p) :=
  (Over.forget N).mapCone ((Over.pullback p).mapCone (smallEtaleNeighborhoodOverCone X B hX s))

/-- The original strict-local curve is the limit of its actual original-neighborhood models. -/
def etaleCurveConeIsLimit : IsLimit (etaleCurveCone X B hX s p) :=
  isLimitOfPreserves (Over.forget N)
    (isLimitOfPreserves (Over.pullback p) (smallEtaleNeighborhoodOverConeIsLimit X B hX s))

/-- The cone vertex is exactly the native pullback, in the native over-category ordering. -/
theorem etaleCurveCone_pt :
    (etaleCurveCone X B hX s p).pt = pullback (strictHenselizationToBase B X.left hX s) p := rfl

/-- The canonical symmetry identifies this cone vertex with the original strict-local model. -/
def etaleCurveConeOriginalIso :
    pullback p (strictHenselizationToBase B X.left hX s) ≅ (etaleCurveCone X B hX s p).pt :=
  pullbackSymmetry _ _

/-- The exact original curve projection is retained by every cone leg. -/
@[simp, reassoc] theorem etaleCurveCone_π_snd (i : SmallEtaleNeighborhood X s) :
    (etaleCurveCone X B hX s p).π.app i ≫
      pullback.snd ((smallEtaleNeighborhoodOver X s).obj i).hom p =
        pullback.snd (strictHenselizationToBase B X.left hX s) p :=
  pullback.lift_snd _ _ _

/-- The original base cone leg is retained by every curve cone leg. -/
@[simp, reassoc] theorem etaleCurveCone_π_fst (i : SmallEtaleNeighborhood X s) :
    (etaleCurveCone X B hX s p).π.app i ≫
      pullback.fst ((smallEtaleNeighborhoodOver X s).obj i).hom p =
        pullback.fst (strictHenselizationToBase B X.left hX s) p ≫
          (smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app i :=
  pullback.lift_fst _ _ _

/-- The actual transitions of the curve diagram are affine. -/
instance etaleCurveDiagram_map_isAffineHom {i j : SmallEtaleNeighborhood X s} (f : i ⟶ j) :
    IsAffineHom ((etaleCurveDiagram X s p).map f) :=
  MorphismProperty.overPullbackMap (P := @IsAffineHom) p
    ((smallEtaleNeighborhoodOver X s).map f) (by
      change IsAffineHom (((smallEtaleNeighborhoodToSmooth X s).map f).left)
      infer_instance)

/-- Each original etale-neighborhood curve model is normal. -/
instance etaleCurveDiagram_isNormal [IsNormal N] (i : SmallEtaleNeighborhood X s) :
    IsNormal ((etaleCurveDiagram X s p).obj i) := by
  let f := (etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i)).left
  have : Etale f := inferInstance
  have hEt : Etale (pullback.snd f p) :=
    MorphismProperty.of_isPullback (P := @Etale)
      (IsPullback.of_hasPullback f p) ‹Etale f›
  change IsNormal (pullback f p)
  exact @isNormal_of_etale _ _ (pullback.snd f p) hEt inferInstance

/-- Properness over the original locally Noetherian base gives actual Noetherian curve stages. -/
instance etaleCurveDiagram_isNoetherian [IsLocallyNoetherian X.left] [IsProper p]
    (i : SmallEtaleNeighborhood X s) : IsNoetherian ((etaleCurveDiagram X s p).obj i) := by
  let f := (etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i)).left
  have : Etale f := inferInstance
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f p)
  have : CompactSpace (pullback f p : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f p)
  change IsNoetherian (pullback f p)
  exact ⟨⟩

/-- The actual strict-local curve limit is locally Noetherian. -/
instance etaleCurveCone_isLocallyNoetherian [IsLocallyNoetherian X.left]
    [LocallyOfFiniteType p] : IsLocallyNoetherian (etaleCurveCone X B hX s p).pt := by
  have := isNoetherian_strictHenselization B X.left hX s
  have hft : LocallyOfFiniteType
      (pullback.fst (strictHenselizationToBase B X.left hX s) p) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (IsPullback.of_hasPullback (strictHenselizationToBase B X.left hX s) p).flip
      ‹LocallyOfFiniteType p›
  change IsLocallyNoetherian (pullback (strictHenselizationToBase B X.left hX s) p)
  exact @LocallyOfFiniteType.isLocallyNoetherian _ _
    (pullback.fst (strictHenselizationToBase B X.left hX s) p) hft inferInstance

/-- The actual strict-local curve limit is normal, without an integrality assumption. -/
instance etaleCurveCone_isNormal [IsNormal N] : IsNormal (etaleCurveCone X B hX s p).pt := by
  have : IsNormal (pullback p (strictHenselizationToBase B X.left hX s)) :=
    isNormal_pullback_strictHenselizationToBase B hX s p
  exact isNormal_of_iso (etaleCurveConeOriginalIso X B hX s p).symm

/-- On the actual small etale diagram, the same strict-local component is the exact preimage of
an actual integral normal component at a stage after any prescribed initial neighborhood. -/
theorem exists_etaleCurve_normalComponent_preimage_eq_over
    [IsLocallyNoetherian X.left] [IsProper p] [IsNormal N]
    (x : (etaleCurveCone X B hX s p).pt) (i₀ : SmallEtaleNeighborhood X s) :
    let c := etaleCurveCone X B hX s p
    ∃ (i : SmallEtaleNeighborhood X s) (_ : i ⟶ i₀),
      c.π.app i ⁻¹ᵁ normalComponentOpen (c.π.app i x) = normalComponentOpen x :=
  exists_normalComponentOpen_preimage_eq_over (etaleCurveDiagram X s p)
    (etaleCurveCone X B hX s p) (etaleCurveConeIsLimit X B hX s p) x i₀


/-- The actual curve structures form a morphism to the unchanged smooth-site base diagram. -/
def etaleCurveStructure : etaleCurveDiagram X s p ⟶
    smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S where
  app i := pullback.fst ((smallEtaleNeighborhoodOver X s).obj i).hom p
  naturality _ _ _ := pullback.lift_fst _ _ _

/-- The curve limit square at every stage is the actual Cartesian base-change square. -/
theorem etaleCurveCone_isPullback (i : SmallEtaleNeighborhood X s) :
    IsPullback ((etaleCurveCone X B hX s p).π.app i)
      (pullback.fst (strictHenselizationToBase B X.left hX s) p)
      ((etaleCurveStructure X s p).app i)
      ((smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app i) := by
  refine IsPullback.of_right ?_ (etaleCurveCone_π_fst X B hX s p i)
    (IsPullback.of_hasPullback ((smallEtaleNeighborhoodOver X s).obj i).hom p).flip
  rw [etaleCurveCone_π_snd]
  change IsPullback _ _ p
    ((smallEtaleNeighborhoodStrictHenselizationCone X B hX s).π.app i ≫
      (etaleNeighborhoodHom X s.hom ((smallEtaleNeighborhoodInclusion X s).obj i)).left)
  rw [smallEtaleNeighborhoodStrictHenselizationCone_π_comp_hom]
  exact (IsPullback.of_hasPullback (strictHenselizationToBase B X.left hX s) p).flip

/-- Every transition square is Cartesian over the same original base transition. -/
theorem etaleCurveDiagram_isPullback {i j : SmallEtaleNeighborhood X s} (f : i ⟶ j) :
    IsPullback ((etaleCurveDiagram X s p).map f) ((etaleCurveStructure X s p).app i)
      ((etaleCurveStructure X s p).app j)
      ((smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).map f) := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _)
    (IsPullback.of_hasPullback ((smallEtaleNeighborhoodOver X s).obj j).hom p).flip
  change IsPullback
    (((Over.pullback p).map ((smallEtaleNeighborhoodOver X s).map f)).left ≫
      pullback.snd _ p) (pullback.fst _ p) p
    (((smallEtaleNeighborhoodOver X s).map f).left ≫
      ((smallEtaleNeighborhoodOver X s).obj j).hom)
  rw [Over.w]
  change IsPullback (pullback.lift _ _ _ ≫ pullback.snd _ _) _ _ _
  rw [pullback.lift_snd]
  exact (IsPullback.of_hasPullback ((smallEtaleNeighborhoodOver X s).obj i).hom p).flip

/-- The finite-stage component comparison keeps the original strict-local pullback ordering
through its specified canonical symmetry, and identifies the actual original component. -/
theorem exists_originalComponent_etaleCurve_preimage_eq_over
    [IsLocallyNoetherian X.left] [IsProper p] [IsNormal N]
    (x : (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u}))
    (i₀ : SmallEtaleNeighborhood X s) :
    let c := etaleCurveCone X B hX s p
    let e := etaleCurveConeOriginalIso X B hX s p
    ∃ (i : SmallEtaleNeighborhood X s) (_ : i ⟶ i₀),
      (((e.hom ≫ c.π.app i) ⁻¹ᵁ normalComponentOpen ((e.hom ≫ c.π.app i) x)) :
        Set (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u})) =
          _root_.irreducibleComponent x := by
  intro c e
  have := isNormal_pullback_strictHenselizationToBase B hX s p
  have := isLocallyNoetherian_pullback_strictHenselizationToBase B hX s p
  obtain ⟨i, f, hi⟩ := exists_etaleCurve_normalComponent_preimage_eq_over X B hX s p
    (e.hom x) i₀
  refine ⟨i, f, ?_⟩
  change ((e.hom ⁻¹ᵁ (c.π.app i ⁻¹ᵁ normalComponentOpen (c.π.app i (e.hom x)))) :
    Set (pullback p (strictHenselizationToBase B X.left hX s) : Scheme.{u})) = _
  rw [hi, normalComponentOpen_preimage_of_isOpenImmersion]
  rfl

end AlgebraicGeometry.Scheme.SmoothSite
