/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0BottomTargets
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassOldChartBinaryRows

/-!
# The complete shared Laurent rows of H₀ and the original Bass 44-simplex

Each original binary row is identified via the already proved match of its
full normalized target, after the actual coefficient map equality. The
common source of the two projection triangles is retained as well. Adapted
from `BinaryRowEndpoint.lean` and `BassH0LaurentSharedNodes.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd` in Quillen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectProjectionBinaryRows

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

section Endpoints

variable {X Y Z T : Scheme.{u}}
  (F : asSmallCategory (W T) ⟶ asSmallCategory (W X))
  (P : asSmallCategory (W T) ⟶ asSmallCategory (W Z)) (f : X ⟶ Y) (g : Y ⟶ Z)

private theorem preBinaryNodes_source_ref
    (ρ : F.hom.toFunctor ≅ (P ≫ BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor) :
    (preBinaryNodes F P f g ρ 0).2 = ρ := by
  change ρ ≪≫ isoWhiskerLeft P.hom.toFunctor (Iso.refl _) = ρ
  rw [isoWhiskerLeft_refl]
  exact Iso.trans_refl ρ

/-- The same full source determines the entire fixed native binary row. -/
theorem preBinaryNodes_of_source
    {ρ σ : F.hom.toFunctor ≅ (P ≫ BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor}
    (he : preBinaryNodes F P f g ρ 0 = preBinaryNodes F P f g σ 0) (i : Fin 3) :
    preBinaryNodes F P f g ρ i = preBinaryNodes F P f g σ i := by
  have hs : (preBinaryNodes F P f g ρ 0).2 = (preBinaryNodes F P f g σ 0).2 :=
    eq_of_heq (Sigma.mk.inj he).2
  rw [preBinaryNodes_source_ref, preBinaryNodes_source_ref] at hs
  exact congrArg (fun η ↦ preBinaryNodes F P f g η i) hs

/-- The two actual scheme factors and the full source determine the entire binary row. -/
theorem preBinaryNodes_source_congr {f' : X ⟶ Y} {g' : Y ⟶ Z} (hf : f = f') (hg : g = g')
    (ρ : F.hom.toFunctor ≅ (P ≫ BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor)
    (σ : F.hom.toFunctor ≅ (P ≫ BoundedFlatPerfectBinarySimplex.sourceMap f' g').hom.toFunctor)
    (he : preBinaryNodes F P f g ρ 0 = preBinaryNodes F P f' g' σ 0) (i : Fin 3) :
    preBinaryNodes F P f g ρ i = preBinaryNodes F P f' g' σ i := by
  subst f'
  subst g'
  exact preBinaryNodes_of_source F P f g he i

/-- The same normalized target determines the entire fixed native binary row. -/
theorem preBinaryNodes_of_target
    {ρ σ : F.hom.toFunctor ≅ (P ≫ BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor}
    (he : preBinaryNodes F P f g ρ 2 = preBinaryNodes F P f g σ 2) (i : Fin 3) :
    preBinaryNodes F P f g ρ i = preBinaryNodes F P f g σ i := by
  have hs : (preBinaryNodes F P f g ρ 2).2 = (preBinaryNodes F P f g σ 2).2 :=
    eq_of_heq (Sigma.mk.inj he).2
  let k := isoWhiskerLeft P.hom.toFunctor (BoundedFlatPerfectBinarySimplex.total f g)
  change ρ ≪≫ k = σ ≪≫ k at hs
  have hc := congrArg (fun η ↦ η ≪≫ k.symm) hs
  have hρ : ρ = σ := by simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hc
  exact congrArg (fun η ↦ preBinaryNodes F P f g η i) hρ

/-- Actual scheme-factor equalities and a full target equality preserve both
normalization pieces. -/
theorem preBinaryNodes_target_congr {f' : X ⟶ Y} {g' : Y ⟶ Z} (hf : f = f') (hg : g = g')
    (ρ : F.hom.toFunctor ≅ (P ≫ BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor)
    (σ : F.hom.toFunctor ≅ (P ≫ BoundedFlatPerfectBinarySimplex.sourceMap f' g').hom.toFunctor)
    (he : preBinaryNodes F P f g ρ 2 = preBinaryNodes F P f' g' σ 2) (i : Fin 3) :
    preBinaryNodes F P f g ρ i = preBinaryNodes F P f' g' σ i := by
  subst f'
  subst g'
  exact preBinaryNodes_of_target F P f g he i

end Endpoints

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectProjectionBinaryRows

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merge

open BoundedFlatPerfectProjectionBinaryRows BoundedFlatPerfectRectangleInitialBinaryRow
open BoundedFlatCoefficientBassOldChartBinaryRows

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The whole source node is the first genuine node of the shared positive projection column. -/
theorem shared_source_node : nodes P u v 2 =
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v 15 :=
  positive_source_nodes P u v 0

/-- The entire original plus Laurent row agrees through its already-proved full target. -/
theorem plus_laurent_rows (i : Fin 3) :
    nodes P u v (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v
      (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
        (BoundedFlatCoefficientBassOverlap.plusFace.toOrderHom (outerIndex i))) := by
  have ht := (plus_first_row P u v 2).symm.trans
    ((shared_positive_target_node P u v).trans (old_plus_outer_row P u v 2))
  have hr := preBinaryNodes_target_congr
    (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
    (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
    (coefficientMap P ((underToLaurent R).app a))
    (laurent_composite P u v) rfl
    (chartFirstRowReference P u v (underToLaurent R) (laurentPlus_projection P a))
    (oldOuterRowReference P u v (underToLaurent R) (laurentPlus_projection P c)) ht i
  exact (plus_first_row P u v i).trans (hr.trans (old_plus_outer_row P u v i).symm)

/-- The entire original minus Laurent row agrees through its already-proved full target. -/
theorem minus_laurent_rows (i : Fin 3) :
    nodes P u v (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom
      (BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v
      (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
        (BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom (outerIndex i))) := by
  have ht := (minus_first_row P u v 2).symm.trans
    ((shared_negative_target_node P u v).trans (old_minus_outer_row P u v 2))
  have hr := preBinaryNodes_target_congr
    (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassOverlap.projectionMap P (a := a))
    (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
    (coefficientMap P ((underToLaurentInvert R).app a))
    (laurent_composite P u v) rfl
    (chartFirstRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P a))
    (oldOuterRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P c)) ht i
  exact (minus_first_row P u v i).trans (hr.trans (old_minus_outer_row P u v i).symm)

/-- Full original shared node pair H0[9] = old[0], including its anchored reference. -/
theorem shared_positive_center_node : nodes P u v 9 =
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v 0 :=
  plus_laurent_rows P u v 0

/-- Full original shared node pair H0[10] = old[14], including its anchored reference. -/
theorem shared_positive_laurent_raw_node : nodes P u v 10 =
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v 14 :=
  plus_laurent_rows P u v 1

/-- Full original shared node pair H0[20] = old[24], including its anchored reference. -/
theorem shared_negative_center_node : nodes P u v 20 =
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v 24 :=
  minus_laurent_rows P u v 0

/-- Full original shared node pair H0[21] = old[38], including its anchored reference. -/
theorem shared_negative_laurent_raw_node : nodes P u v 21 =
    BoundedFlatCoefficientBassReferenceMerge.nodes P u v 38 :=
  minus_laurent_rows P u v 1

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merge
