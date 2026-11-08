/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleStalkModules
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CoefficientColength
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.IntersectionMultiplicity

/-!
# The full local triple incidence is the three-ideal quotient

At every actual triple-incidence point, the sum of the two original middle
diagonal stalk ideals and the exterior coefficient stalk ideal is exactly the
kernel of the actual sixfold stalk map. Its quotient is the full local ring of
the triple incidence, with an equation identifying the map on every ambient
element. The module comparison retains that same ambient scalar action.

The geometric ideal equality is adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Correspondences/Composition/Associativity/DiagonalIdeals.lean,
Git blob 93abf1c8979c1d5daca77377ea15ece9062926a7. The stalk comparison uses native
Stacks.Chow.ker_stalkMap_eq_idealStalk_ker and AlgebraicGeometry.IdealSheafData.stalk_sup;
the quotient equivalence is Mathlib's first isomorphism theorem.

This is an exact scheme/module supplier, not a higher-Tor or Euler-associativity
claim. No perfect or algebraically closed field, integrality of the ambient,
connectedness, smoothness, or flatness of the coefficient support is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The three literal ideals in the same actual sixfold local ring. -/
def correspondenceTripleIncidenceThreeStalkIdeals
    (t : correspondenceTripleIncidence f g h i z w v) :
    Ideal (correspondenceTripleIncidenceAmbientStalk f g h i z w v t) :=
  let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v t
  IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p ⊔
    (IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p ⊔
      IdealSheafData.stalk (correspondenceTripleSupportProductInclusion f g h i z w v).ker p)

/-- The full actual stalk kernel is exactly the three-ideal sum, not its radical. -/
theorem correspondenceTripleIncidenceSixfoldInclusion_stalkMap_ker
    [IsSeparated g] [IsSeparated h]
    (t : correspondenceTripleIncidence f g h i z w v) :
    RingHom.ker ((correspondenceTripleIncidenceSixfoldInclusion f g h i z w v).stalkMap t).hom =
      correspondenceTripleIncidenceThreeStalkIdeals f g h i z w v t := by
  rw [ker_stalkMap_eq_idealStalk_ker,
    correspondenceTripleIncidenceSixfoldInclusion_ker_eq_threeIdeals,
    IdealSheafData.stalk_sup, IdealSheafData.stalk_sup]
  rfl

/-- The quotient by the literal three-ideal sum is the full common-incidence local ring. -/
def correspondenceTripleIncidenceStalkQuotientEquiv [IsSeparated g] [IsSeparated h]
    (t : correspondenceTripleIncidence f g h i z w v) :
    (correspondenceTripleIncidenceAmbientStalk f g h i z w v t ⧸
      correspondenceTripleIncidenceThreeStalkIdeals f g h i z w v t) ≃+*
        (correspondenceTripleIncidence f g h i z w v).presheaf.stalk t :=
  (Ideal.quotEquivOfEq
    (correspondenceTripleIncidenceSixfoldInclusion_stalkMap_ker f g h i z w v t).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (f := ((correspondenceTripleIncidenceSixfoldInclusion f g h i z w v).stalkMap t).hom)
      (SurjectiveOnStalks.stalkMap_surjective
        (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v) t))

/-- The quotient comparison sends each ambient germ by the original stalk map. -/
@[simp]
theorem correspondenceTripleIncidenceStalkQuotientEquiv_mk [IsSeparated g] [IsSeparated h]
    (t : correspondenceTripleIncidence f g h i z w v)
    (a : correspondenceTripleIncidenceAmbientStalk f g h i z w v t) :
    correspondenceTripleIncidenceStalkQuotientEquiv f g h i z w v t
        (Ideal.Quotient.mk (correspondenceTripleIncidenceThreeStalkIdeals f g h i z w v t) a) =
      ((correspondenceTripleIncidenceSixfoldInclusion f g h i z w v).stalkMap t).hom a := by
  rfl

/-- The same quotient comparison is linear for the actual sixfold stalk action. -/
def correspondenceTripleIncidenceStalkQuotientModuleIso [IsSeparated g] [IsSeparated h]
    (t : correspondenceTripleIncidence f g h i z w v) :
    ModuleCat.of (correspondenceTripleIncidenceAmbientStalk f g h i z w v t)
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v t ⧸
        correspondenceTripleIncidenceThreeStalkIdeals f g h i z w v t) ≅
      correspondenceTripleIncidenceStalkModule f g h i z w v t := by
  let e := correspondenceTripleIncidenceStalkQuotientEquiv f g h i z w v t
  letI : Module (correspondenceTripleIncidenceAmbientStalk f g h i z w v t)
      ((correspondenceTripleIncidence f g h i z w v).presheaf.stalk t) :=
    Module.compHom _ ((correspondenceTripleIncidenceSixfoldInclusion f g h i z w v).stalkMap t).hom
  apply LinearEquiv.toModuleIso
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro a b
  change e (a • b) =
    ((correspondenceTripleIncidenceSixfoldInclusion f g h i z w v).stalkMap t).hom a * e b
  rw [Algebra.smul_def, map_mul]
  change e (Ideal.Quotient.mk _ a) * e b = _
  rw [correspondenceTripleIncidenceStalkQuotientEquiv_mk]

end Stacks.Chow
