/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.KTheory.Waldhausen.GilletWaldhausen.GlobalEulerReduction
public import Colib.AlgebraicGeometry.Scheme.VectorBundle.KernelClosed

/-! Original-map finite and global fine-model K-class reductions. -/
@[expose] public section

open CategoryTheory.ExactCategory CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.GilletWaldhausen CochainComplex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace ColibTest.QuillenMigration.GilletWaldhausenReduction
attribute [local instance] Abelian.hasFiniteBiproducts
section
variable {A : Type (max u v)} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
local instance reductionConsumerProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

theorem actual_bounded_term_stage (k : ℕ)
    (x : (ofExactCategory (boundedTermsExactStructure P)).K k) :
    ∃ N : ℕ, ∃ y : (ofExactCategory (boundedTermsStratumExactStructure P N)).K k,
      KMap (fixedTermsInclusionExactFunctor P (-(N : ℤ)) N).waldhausenExact k y = x :=
  boundedTerms_KMap_jointlySurjective P k x

omit [(abelianExactStructure A).IsExtensionClosed P] in
theorem actual_original_single_map (n : ℤ) {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ((boundedTermsSingleFunctor P n).map f).hom =
      (HomologicalComplex.single A (ComplexShape.up ℤ) n).map f.hom := rfl

variable [(abelianExactStructure A).IsKernelClosed P]

theorem actual_acyclic_inclusion_injective (k : ℕ) :
    Function.Injective (KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k) :=
  boundedAcyclicTermsInclusion_KMap_injective P k

theorem actual_global_unique_reduction (k : ℕ)
    (x : (ofExactCategory (boundedTermsExactStructure P)).K k) :
    ∃! p : (ofExactCategory (boundedAcyclicExactStructure P)).K k ×
        (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K k,
      KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact k p.1 *
        KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact k p.2 = x :=
  boundedTerms_existsUnique_acyclic_single_zero P k x

theorem actual_global_K0_joint_kernel
    (d : (ofExactCategory (boundedAcyclicExactStructure P)).K 0)
    (c : (ofExactCategory (ExactSubcategory.exactStructure (abelianExactStructure A) P)).K 0)
    (h : KMap (boundedAcyclicTermsExactInclusion P).waldhausenExact 0 d *
      KMap (boundedTermsSingleExactFunctor P 0).waldhausenExact 0 c = 1) : d = 1 ∧ c = 1 :=
  boundedTerms_acyclic_single_zero_eq_one P 0 d c h
end

private abbrev schemeFiniteLocallyFree (X : AlgebraicGeometry.Scheme.{u}) :
    ObjectProperty X.Modules :=
  fun M ↦ SheafOfModules.IsFiniteLocallyFree.{u, u, u} M

theorem actual_scheme_global_reduction (X : AlgebraicGeometry.Scheme.{u}) (k : ℕ)
    (x : (ofExactCategory (boundedTermsExactStructure
      (schemeFiniteLocallyFree X))).K k) :
    ∃! p : (ofExactCategory (boundedAcyclicExactStructure
      (schemeFiniteLocallyFree X))).K k ×
        (ofExactCategory (ExactSubcategory.exactStructure
          (abelianExactStructure X.Modules) (schemeFiniteLocallyFree X))).K k,
      KMap (boundedAcyclicTermsExactInclusion (schemeFiniteLocallyFree X)).waldhausenExact k
        p.1 *
        KMap (boundedTermsSingleExactFunctor
          (schemeFiniteLocallyFree X)
          0).waldhausenExact k p.2 = x :=
  boundedTerms_existsUnique_acyclic_single_zero
    (schemeFiniteLocallyFree X) k x

end ColibTest.QuillenMigration.GilletWaldhausenReduction
