/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.Basic
public import Colib.AlgebraicGeometry.KTheory.BoundedFiniteLocallyFree
public import Colib.AlgebraicGeometry.Scheme.VectorBundle.KernelClosed
public import Colib.KTheory.Quillen.Map.CommonAmbient
public import Colib.KTheory.Waldhausen.GilletWaldhausen.GeneralComparison
public import Colib.KTheory.Waldhausen.QuillenComparison.Equivalence

/-!
# Gillet–Waldhausen for bounded complexes of vector bundles

The actual degree-zero insertion of a vector bundle into a bounded complex
induces an equivalence in connective K-theory. The target is the native
Waldhausen category of bounded complexes with finite locally free terms and
quasi-isomorphisms, not the category of all locally perfect complexes.

Implementation provenance:
`Quillen/AlgebraicGeometry/PerfectComplexes/GilletWaldhausen.lean` and
`Quillen/AlgebraicGeometry/PerfectComplexes/QuillenComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.ExactCategory CategoryTheory.Limits
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.GilletWaldhausen CochainComplex
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme

local instance finiteLocallyFreeExtensionClosed (X : Scheme.{u}) :
    (abelianExactStructure X.Modules).IsExtensionClosed
      (fun M : X.Modules ↦ SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :=
  Modules.finiteLocallyFree_isExtensionClosed X

local instance finiteLocallyFreeKernelClosed (X : Scheme.{u}) :
    (abelianExactStructure X.Modules).IsKernelClosed
      (fun M : X.Modules ↦ SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :=
  Modules.finiteLocallyFree_isKernelClosed X

private theorem degreeZeroMap_bijective (X : Scheme.{u})
    (Q : ObjectProperty (CochainComplex X.Modules ℤ))
    [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms] [Q.IsClosedUnderFiniteProducts]
    [(abelianExactStructure (CochainComplex X.Modules ℤ)).IsExtensionClosed Q]
    (hQ : Q = boundedTerms (fun M : X.Modules ↦ SheafOfModules.IsFiniteLocallyFree.{u, u, u} M))
    (F : X.Vect ⥤ Q.FullSubcategory)
    (hF : CategoryTheory.Waldhausen.IsExact
      (ofExactCategory (Modules.vectorBundleExactStructure X)).cof
      (ofExactCategory (Modules.vectorBundleExactStructure X)).weq
      (complexSubcategory Q).cof (complexSubcategory Q).weq F)
    (hf : F ⋙ Q.ι =
      ObjectProperty.ι
        (fun M : X.Modules ↦ SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) ⋙
      HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0) (n : ℕ) :
    Function.Bijective (CategoryTheory.Waldhausen.KMap hF n) := by
  subst Q
  let P : ObjectProperty X.Modules := fun M ↦ SheafOfModules.IsFiniteLocallyFree.{u, u, u} M
  let e : F ≅ boundedTermsSingleFunctor.{u, u + 1} P 0 :=
    ((boundedTerms P).fullyFaithfulι.whiskeringRight _).preimageIso (eqToIso hf)
  rw [KMap_eq_of_iso hF (boundedTermsSingle_coarseExact.{u, u + 1} P 0) e n]
  exact boundedTermsSingle_coarse_KMap_bijective_general.{u + 1, u} P n

/-- The canonical degree-zero vector-bundle S-map is bijective, including in degree zero. -/
theorem vectorBundleToBoundedFiniteLocallyFreeKMap_bijective (X : Scheme.{u}) (n : ℕ) :
    Function.Bijective (X.vectorBundleToBoundedFiniteLocallyFreeKMap n) := by
  have hP : boundedFiniteLocallyFreeComplex X =
      boundedTerms (fun M : X.Modules ↦ SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) := by
    funext K
    exact propext (boundedFiniteLocallyFreeComplex_iff_termBounds K)
  exact degreeZeroMap_bijective X _ hP _
    (vectorBundleComplexInclusion_isExact X) rfl n

/-- Public Quillen K-theory of vector bundles maps to the native strict-complex S-theory. -/
def vectorBundleKToBoundedFiniteLocallyFreeKMap (X : Scheme.{u}) (n : ℕ) :
    X.K n →* X.boundedFiniteLocallyFreeK n :=
  let E := Modules.vectorBundleExactStructure X
  (X.vectorBundleToBoundedFiniteLocallyFreeKMap n).comp
    ((QuillenComparison.comparisonKEquiv E n).symm.toMonoidHom.comp
      (E.smallModelToOriginal.{u + 1}.commonAmbientKMap n))

/-- The original public Quillen-to-Waldhausen comparison is bijective. -/
theorem vectorBundleKToBoundedFiniteLocallyFreeKMap_bijective (X : Scheme.{u}) (n : ℕ) :
    Function.Bijective (X.vectorBundleKToBoundedFiniteLocallyFreeKMap n) := by
  let E := Modules.vectorBundleExactStructure X
  exact (X.vectorBundleToBoundedFiniteLocallyFreeKMap_bijective n).comp
    ((QuillenComparison.comparisonKEquiv E n).symm.bijective.comp
      (E.smallModelToOriginal.{u + 1}.commonAmbientKEquiv n).bijective)

/-- Gillet–Waldhausen for schemes, with the actual degree-zero map and no extra hypothesis. -/
def vectorBundleKToBoundedFiniteLocallyFreeKEquiv (X : Scheme.{u}) (n : ℕ) :
    X.K n ≃* X.boundedFiniteLocallyFreeK n :=
  MulEquiv.ofBijective (X.vectorBundleKToBoundedFiniteLocallyFreeKMap n)
    (X.vectorBundleKToBoundedFiniteLocallyFreeKMap_bijective n)

@[simp]
theorem vectorBundleKToBoundedFiniteLocallyFreeKEquiv_toMonoidHom
    (X : Scheme.{u}) (n : ℕ) :
    (↑(X.vectorBundleKToBoundedFiniteLocallyFreeKEquiv n) : X.K n →*
      X.boundedFiniteLocallyFreeK n) =
      X.vectorBundleKToBoundedFiniteLocallyFreeKMap n := rfl

/-- The public comparison with perfect complexes is the degree-zero map followed by
the canonical inclusion of bounded finite locally free complexes. -/
def vectorBundleKToPerfectKMap (X : Scheme.{u}) (n : ℕ) :
    X.K n →* (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).K n :=
  (X.boundedFiniteLocallyFreeToPerfectKMap n).comp
    (X.vectorBundleKToBoundedFiniteLocallyFreeKMap n)

/-- The actual bounded-to-perfect chain inclusion commutes with degree-zero insertion. -/
@[simp]
theorem boundedFiniteLocallyFreeToPerfectKMap_comp_vectorBundleKToBoundedFiniteLocallyFreeKMap
    (X : Scheme.{u}) (n : ℕ) :
    (X.boundedFiniteLocallyFreeToPerfectKMap n).comp
      (X.vectorBundleKToBoundedFiniteLocallyFreeKMap n) = X.vectorBundleKToPerfectKMap n := rfl

attribute [colib_tag "COL-1312",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/GilletWaldhausen.lean:33-52"
    "adaptation" "The actual degree-zero map between the original K-groups",
  colib_ref "ThomasonTrobaugh1990" "Theorem 1.11.7, pp. 280–281"
    "adaptation" "Connective K-group comparison using the native closure hypotheses"]
  vectorBundleToBoundedFiniteLocallyFreeKMap_bijective
  vectorBundleKToBoundedFiniteLocallyFreeKMap_bijective
  vectorBundleKToBoundedFiniteLocallyFreeKEquiv
  vectorBundleKToBoundedFiniteLocallyFreeKEquiv_toMonoidHom

attribute [colib_tag "COL-1312",
  colib_ref "quillen" "Quillen/AlgebraicGeometry/PerfectComplexes/QuillenComparison.lean:48-62"
    "adaptation" "The actual public degree-zero maps and the commuting triangle"]
  vectorBundleKToBoundedFiniteLocallyFreeKMap
  vectorBundleKToPerfectKMap
  boundedFiniteLocallyFreeToPerfectKMap_comp_vectorBundleKToBoundedFiniteLocallyFreeKMap

end AlgebraicGeometry.Scheme
