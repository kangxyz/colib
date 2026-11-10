/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.ReducedGraphNaturality
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.SpecSectionsExact

/-!
# Naturality with the actual spectrum global-section coefficients

The canonical first-power graph isomorphism and cokernel projection transport
actual graph naturality of the boundary divisor. The affine counits then give
naturality in the original boundary-one and ordinary unit section groups.
Source structure maps are allowed to agree propositionally, not definitionally.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers

variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]

section Coefficient

variable (f : Spec (.of R) ⟶ Spec (.of k)) (a : R →+* A)
  [Smooth f] [IsSeparated f] [QuasiCompact f]
  [Smooth (Spec.map (CommRingCat.ofHom a) ≫ f)]
  [IsSeparated (Spec.map (CommRingCat.ofHom a) ≫ f)]
  [QuasiCompact (Spec.map (CommRingCat.ofHom a) ≫ f)]
  [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]

/-- The existing first-power comparison transports actual boundary graph naturality. -/
theorem powerOneBoundaryDivisor_graph_comp
    (m : Additive (Polynomial.BoundaryOneRationalFunctions.group R)) :
    (Cor.graphFunctor k).map (coefficientGraph f a) ≫ powerOneBoundaryDivisor f m =
      powerOneBoundaryDivisor (Spec.map (CommRingCat.ofHom a) ≫ f)
        ((Polynomial.BoundaryOneRationalFunctions.map a).toAdditive m) := by
  apply (powerOneCycleEquiv (Spec.map (CommRingCat.ofHom a) ≫ f)).injective
  rw [powerOneCycleEquiv_graph_comp]
  simpa only [powerOneCycleEquiv_boundaryDivisor] using
    boundaryDivisor_graphRestriction f a m

/-- The literal canonical quotient retains the genuine boundary graph restriction. -/
theorem reducedBoundaryDivisor_coefficientGraph
    (m : ULift.{u + 1} (Additive (Polynomial.BoundaryOneRationalFunctions.group R))) :
    transfer (reducedTorus k 1) ((Cor.graphFunctor k).map (coefficientGraph f a))
        (reducedBoundaryDivisor f m) =
      reducedBoundaryDivisor (Spec.map (CommRingCat.ofHom a) ≫ f)
        (ULift.up ((Polynomial.BoundaryOneRationalFunctions.map a).toAdditive m.down)) := by
  change transfer (reducedTorus k 1)
      ((Cor.graphFunctor k).map (coefficientGraph f a))
      ((toReducedTorus k 1).hom.app (op (Cor.mk (mk f)))
        (ULift.up (powerOneBoundaryDivisor f m.down))) =
    (toReducedTorus k 1).hom.app
      (op (Cor.mk (mk (Spec.map (CommRingCat.ofHom a) ≫ f))))
      (ULift.up (powerOneBoundaryDivisor (Spec.map (CommRingCat.ofHom a) ≫ f)
        ((Polynomial.BoundaryOneRationalFunctions.map a).toAdditive m.down)))
  rw [toReducedTorus_coefficientGraph, powerOneBoundaryDivisor_graph_comp]

end Coefficient

section SpectrumMaps

variable (f : Spec (.of R) ⟶ Spec (.of k)) (g : Spec (.of A) ⟶ Spec (.of k))
  [Smooth f] [IsSeparated f] [QuasiCompact f]
  [Smooth g] [IsSeparated g] [QuasiCompact g]
  (a : R →+* A) (h : mk g ⟶ mk f) (ha : h.left = Spec.map (CommRingCat.ofHom a))

include ha

/-- Actual section pullback and the boundary affine counit commute. -/
theorem specBoundaryOneIso_naturality :
    (largeBoundaryOnePresheaf k).map h.op ≫ (specBoundaryOneIso g).hom =
      (specBoundaryOneIso f).hom ≫
        (Polynomial.BoundaryOneRationalFunctions.functor ⋙
          AddCommGrpCat.uliftFunctor.{u + 1, u}).map (CommRingCat.ofHom a) := by
  let F := Polynomial.BoundaryOneRationalFunctions.functor ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}
  change F.map h.left.appTop ≫ F.map _ = F.map _ ≫ F.map _
  rw [ha, ← F.map_comp, ← F.map_comp, Scheme.ΓSpecIso_naturality]

/-- Actual ordinary unit pullback commutes with the same affine counit. -/
theorem specUnitsIso_naturality :
    (largeUnitsPresheaf (Spec (.of k))).map h.op ≫ (specUnitsIso g).hom =
      (specUnitsIso f).hom ≫
        (ringUnitsFunctor ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}).map
          (CommRingCat.ofHom a) := by
  let F := ringUnitsFunctor ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}
  change F.map h.left.appTop ≫ F.map _ = F.map _ ≫ F.map _
  rw [ha, ← F.map_comp, ← F.map_comp, Scheme.ΓSpecIso_naturality]

variable [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
  [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]

/-- The graph formula is valid with the original, propositionally equal source structure. -/
theorem reducedNormApp_spectrumMap
    (z : sections (reducedTorus k 1) (Cor.mk (mk f))) :
    reducedNormApp g (transfer (reducedTorus k 1) ((Cor.graphFunctor k).map h) z) =
      ULift.up ((Units.map a.toMonoidHom).toAdditive (reducedNormApp f z).down) := by
  have hg : g = Spec.map (CommRingCat.ofHom a) ≫ f := by
    rw [← ha]
    exact (MorphismProperty.Over.w h).symm
  subst g
  have hh : h = coefficientGraph f a := by
    apply MorphismProperty.Over.Hom.ext
    exact ha
  subst h
  exact reducedNormApp_coefficientGraph f a z

/-- Boundary graph naturality likewise preserves the original source structure. -/
theorem reducedBoundaryDivisor_spectrumMap
    (m : ULift.{u + 1} (Additive (Polynomial.BoundaryOneRationalFunctions.group R))) :
    transfer (reducedTorus k 1) ((Cor.graphFunctor k).map h)
        (reducedBoundaryDivisor f m) =
      reducedBoundaryDivisor g
        (ULift.up ((Polynomial.BoundaryOneRationalFunctions.map a).toAdditive m.down)) := by
  have hg : g = Spec.map (CommRingCat.ofHom a) ≫ f := by
    rw [← ha]
    exact (MorphismProperty.Over.w h).symm
  subst g
  have hh : h = coefficientGraph f a := by
    apply MorphismProperty.Over.Hom.ext
    exact ha
  subst h
  exact reducedBoundaryDivisor_coefficientGraph f a m

/-- Naturality of the actual norm in the original ordinary spectrum-section coefficients. -/
theorem specSectionsReducedNorm_natural :
    ((toPresheaf k).obj (reducedTorus k 1)).map h.op ≫ specSectionsReducedNorm g =
      specSectionsReducedNorm f ≫ (largeUnitsPresheaf (Spec (.of k))).map h.op := by
  apply (cancel_mono (specUnitsIso g).hom).mp
  have hn : ((toPresheaf k).obj (reducedTorus k 1)).map h.op ≫ reducedNormApp g =
      reducedNormApp f ≫
        (ringUnitsFunctor ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}).map
          (CommRingCat.ofHom a) := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    exact reducedNormApp_spectrumMap f g a h ha
  simpa only [specSectionsReducedNorm, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, specUnitsIso_naturality f g a h ha, Iso.inv_hom_id_assoc] using hn

/-- Naturality of the actual reduced divisor in the original boundary section coefficients. -/
theorem specSectionsReducedBoundaryDivisor_natural :
    (largeBoundaryOnePresheaf k).map h.op ≫ specSectionsReducedBoundaryDivisor g =
      specSectionsReducedBoundaryDivisor f ≫
        ((toPresheaf k).obj (reducedTorus k 1)).map h.op := by
  have hd : (Polynomial.BoundaryOneRationalFunctions.functor ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}).map (CommRingCat.ofHom a) ≫
        reducedBoundaryDivisor g = reducedBoundaryDivisor f ≫
        ((toPresheaf k).obj (reducedTorus k 1)).map h.op := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro m
    exact (reducedBoundaryDivisor_spectrumMap f g a h ha m).symm
  dsimp only [specSectionsReducedBoundaryDivisor]
  rw [← Category.assoc, specBoundaryOneIso_naturality f g a h ha, Category.assoc, hd]
  simp only [Category.assoc]

end SpectrumMaps

end AlgebraicGeometry.NativeTorusPolynomial
