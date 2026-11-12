/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedMarkedSquare
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedSourceChange

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.Norm.ProductBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.MarkedCoordinate

/-!
# The common marked factor of the two norm coefficients

Both normalized pairs use the same whole target graph coordinate on the
marked factor. The graph remains Cartier there, including on a nonreduced
mark, so this exact coordinate can be cancelled in the norm equation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {S X Y P C Z : Scheme.{u}} (q : X ⟶ S)
  (π : P ⟶ S) (f : C ⟶ P) (j : Y ⟶ C) (jA : X ⟶ P)
  (p : Y ⟶ X) (hRet : j ≫ f = p ≫ jA)
  (hB : j ≫ (f ≫ π) = p ≫ q) (hA : jA ≫ π = (𝟙 X) ≫ q)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z)

local notation "b" => (j ≫ f ≫ π)
local notation "zA" => (z ≫ jA)
local notation "M" => (pullback b (zA ≫ π))

/-- The marked product on the source side retains the same second parameter. -/
def pairedMarkToSource :
    M ⟶ pullback b (s ≫ j ≫ f ≫ π) :=
  (pullback.congrHom rfl (by
    have h : s ≫ j ≫ f = z ≫ jA := by rw [hRet, ← Category.assoc, hs]
    simpa only [Category.assoc] using (congrArg (fun g ↦ g ≫ π) h).symm)).hom

/-- On the target side only the first parameter changes, by the original map. -/
def pairedMarkToTarget :
    M ⟶ pullback (jA ≫ π) (z ≫ jA ≫ π) :=
  (pullback.congrHom rfl (Category.assoc z jA π)).hom ≫
    retainedSourceChange (jA ≫ π) b (z ≫ jA ≫ π) p (by
    rw [hA, Category.id_comp]
    exact hB.symm)

/-- The two transported frames use the same ring map from the original
target graph coordinate ring to the marked factor. -/
theorem pairedMark_coordinateMap :
    pairedMarkToSource π f j jA p hRet z s hs ≫
        markedProductToTarget q (f ≫ π) j p hB z s hs =
      pairedMarkToTarget q π f j jA p hB hA z ≫
        markedProductToTarget q π jA (𝟙 X) hA z z (Category.comp_id z) := by
  apply pullback.hom_ext <;> simp [pairedMarkToSource, pairedMarkToTarget, Category.assoc]

/-- The target marked inclusion compares with the original change of first
parameter through both literal projections. -/
theorem pairedMarkToTarget_markedProductMap :
    pairedMarkToTarget q π f j jA p hB hA z ≫ markedProductMap π jA z =
      retainedProductInclusion b π zA ≫ graphTargetParameterMap π f j jA p hRet := by
  apply pullback.hom_ext <;>
    simp [pairedMarkToTarget, markedProductMap, Category.assoc]

/-- The retained part of the finite marked product is the original source
mark, with its exact map into the full compactification. -/
theorem pairedMarkToSource_markedProductMap (H : IsPullback s (𝟙 Z) p z) [Mono jA] :
    pairedMarkToSource π f j jA p hRet z s hs ≫ markedProductMap (f ≫ π) j s =
      productMarkedSection b π f zA j s
        (pairedMark_isPullback f j jA p hRet z s H) ≫
          retainedProductInclusion b (f ≫ π) j := by
  apply pullback.hom_ext <;>
    simp [pairedMarkToSource, markedProductMap, productMarkedSection, Category.assoc]

variable [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  [IsSeparated π] [IsSeparated (f ≫ π)] [IsOpenImmersion jA] [IsOpenImmersion j]
  [SmoothOfRelativeDimension 1 (jA ≫ π)] [SmoothOfRelativeDimension 1 (j ≫ f ≫ π)]
  (H : IsPullback s (𝟙 Z) p z)

omit [SmoothOfRelativeDimension 1 q] [SmoothOfRelativeDimension 1 (jA ≫ π)] in
include hB hA hs H in
/-- The target graph equation on the whole marked factor is Cartier. -/
theorem isEffectiveCartierDivisor_pairedTargetMark :
    IsEffectiveCartierDivisor ((compactificationGraph π jA).ker.comap
      (retainedProductInclusion b π zA ≫ graphTargetParameterMap π f j jA p hRet)) := by
  let eB := pairedMarkToSource π f j jA p hRet z s hs
  let eA := pairedMarkToTarget q π f j jA p hB hA z
  let : IsIso eB := by dsimp only [eB, pairedMarkToSource]; infer_instance
  have hMark : eB ≫ markedProductToTarget q (f ≫ π) j p hB z s hs =
      eA ≫ markedProductToTarget q π jA (𝟙 X) hA z z (Category.comp_id z) :=
    pairedMark_coordinateMap q π f j jA p hRet hB hA z s hs
  have hEq : (compactificationGraph π jA).ker.comap (eA ≫ markedProductMap π jA z) =
      (markedProductGraph (f ≫ π) j s).ker.comap eB := by
    rw [IdealSheafData.comap_comp, compactificationGraphIdeal_comap_markedProductMap,
      ← markedTarget_ideal q π jA (𝟙 X) hA z z (Category.comp_id z) (IsPullback.of_id_snd),
      ← IdealSheafData.comap_comp, ← hMark, IdealSheafData.comap_comp,
      markedTarget_ideal q (f ≫ π) j p hB z s hs H]
  have hTarget : eA ≫ markedProductMap π jA z =
      retainedProductInclusion b π zA ≫ graphTargetParameterMap π f j jA p hRet :=
    pairedMarkToTarget_markedProductMap q π f j jA p hRet hB hA z
  rw [← hTarget, hEq]
  exact isPullbackDefined_of_flat eB _ inferInstance

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
