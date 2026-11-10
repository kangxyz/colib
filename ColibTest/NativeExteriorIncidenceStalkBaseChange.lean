/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceStalkBaseChange

/-!
SOURCE ONLY, UNCOMPILED. These consumers use the actual original incidence
quotient module E₀/J for an arbitrary ideal J, so neither reducedness nor
flatness of the coefficient module is imposed. Scalar formulas retain the
actual projection p and the point-transported original quotient map η₀.
The quotient propositions and their specialization are elaborated over generic
bundled rings first, then instantiated with the actual native geometric family.
Each final proposition quantifies over every ideal inside that generic interface,
so the geometric specialization does not re-elaborate an ideal argument.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open AlgebraicGeometry.Scheme
open scoped TensorProduct

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- The native scalar-explicit family interface, before any quotient is substituted. -/
private def incidenceBaseChangeFamily
    (R S A B : CommRingCat.{u}) (α : R →+* S) (η₀ : R →+* A)
    (η : S →+* B) (p : A →+* B) : Type (u + 1) :=
  ∀ (M : Type u) [AddCommGroup M] [Module A M],
  let : Algebra R S := α.toAlgebra
  let : Algebra A B := p.toAlgebra
  let : Algebra S B := η.toAlgebra
  let : Module R M := Module.compHom M η₀
  B ⊗[A] M ≃ₗ[S] S ⊗[R] M

/-- The inverse generator law for the same family. -/
private def incidenceInverseFamily
    (R S A B : CommRingCat.{u}) (α : R →+* S) (η₀ : R →+* A)
    (η : S →+* B) (p : A →+* B) (F : incidenceBaseChangeFamily R S A B α η₀ η p) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module A M] (d : S) (m : M),
  let : Algebra R S := α.toAlgebra
  let : Algebra A B := p.toAlgebra
  let : Algebra S B := η.toAlgebra
  let : Module R M := Module.compHom M η₀
  (F M).symm (d ⊗ₜ[R] m) = η d ⊗ₜ[A] m

/-- The forward generator law for the same family. -/
private def incidenceForwardFamily
    (R S A B : CommRingCat.{u}) (α : R →+* S) (η₀ : R →+* A)
    (η : S →+* B) (p : A →+* B) (F : incidenceBaseChangeFamily R S A B α η₀ η p) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module A M] (d : S) (m : M),
  let : Algebra R S := α.toAlgebra
  let : Algebra A B := p.toAlgebra
  let : Algebra S B := η.toAlgebra
  let : Module R M := Module.compHom M η₀
  F M (η d ⊗ₜ[A] m) = d ⊗ₜ[R] m

/-- The scalar law for the same family. -/
private def incidenceScalarFamily
    (R S A B : CommRingCat.{u}) (α : R →+* S) (η₀ : R →+* A)
    (η : S →+* B) (p : A →+* B) (F : incidenceBaseChangeFamily R S A B α η₀ η p) : Prop :=
  ∀ (M : Type u) [AddCommGroup M] [Module A M] (d : S),
  let : Algebra R S := α.toAlgebra
  let : Algebra A B := p.toAlgebra
  let : Algebra S B := η.toAlgebra
  let : Module R M := Module.compHom M η₀
  ∀ t : B ⊗[A] M, F M (d • t) = d • F M t

/-- Existence of the equivalence on the actual ideal quotient. -/
private def quotientHasEquiv
    (R S A B : CommRingCat.{u}) (α : R →+* S) (η₀ : R →+* A)
    (η : S →+* B) (p : A →+* B) : Prop :=
  ∀ (J : Ideal A),
  let : Algebra R S := α.toAlgebra
  let : Algebra A B := p.toAlgebra
  let : Algebra S B := η.toAlgebra
  let : Module R (A ⧸ J) := Module.compHom (A ⧸ J) η₀
  Nonempty (B ⊗[A] (A ⧸ J) ≃ₗ[S] S ⊗[R] (A ⧸ J))

/-- The inverse law on the literal ideal-quotient generator. -/
private def quotientInverseFormula
    (R S A B : CommRingCat.{u}) (α : R →+* S) (η₀ : R →+* A)
    (η : S →+* B) (p : A →+* B) (F : incidenceBaseChangeFamily R S A B α η₀ η p) : Prop :=
  ∀ (J : Ideal A),
  let : Algebra R S := α.toAlgebra
  let : Algebra A B := p.toAlgebra
  let : Algebra S B := η.toAlgebra
  let : Module R (A ⧸ J) := Module.compHom (A ⧸ J) η₀
  ∀ (d : S) (a : A),
    (F (A ⧸ J)).symm (d ⊗ₜ[R] Ideal.Quotient.mk J a) =
      η d ⊗ₜ[A] Ideal.Quotient.mk J a

/-- Compatibility with the actual original-ring map on every quotient class. -/
private def quotientOriginalFormula
    (R S A B : CommRingCat.{u}) (α : R →+* S) (η₀ : R →+* A)
    (η : S →+* B) (p : A →+* B) (F : incidenceBaseChangeFamily R S A B α η₀ η p) : Prop :=
  ∀ (J : Ideal A),
  let : Algebra R S := α.toAlgebra
  let : Algebra A B := p.toAlgebra
  let : Algebra S B := η.toAlgebra
  let : Module R (A ⧸ J) := Module.compHom (A ⧸ J) η₀
  ∀ (a : R) (m : A ⧸ J),
    F (A ⧸ J) (p (η₀ a) ⊗ₜ[A] m) = α a ⊗ₜ[R] m

/-- The scalar law on arbitrary tensors with the actual ideal quotient. -/
private def quotientScalarFormula
    (R S A B : CommRingCat.{u}) (α : R →+* S) (η₀ : R →+* A)
    (η : S →+* B) (p : A →+* B) (F : incidenceBaseChangeFamily R S A B α η₀ η p) : Prop :=
  ∀ (J : Ideal A),
  let : Algebra R S := α.toAlgebra
  let : Algebra A B := p.toAlgebra
  let : Algebra S B := η.toAlgebra
  let : Module R (A ⧸ J) := Module.compHom (A ⧸ J) η₀
  ∀ (d : S) (t : B ⊗[A] (A ⧸ J)),
    F (A ⧸ J) (d • t) = d • F (A ⧸ J) t

private theorem quotientHasEquiv_of_family
    (R S A B : CommRingCat.{u}) (α : R →+* S) (η₀ : R →+* A)
    (η : S →+* B) (p : A →+* B) (F : incidenceBaseChangeFamily R S A B α η₀ η p) :
    quotientHasEquiv R S A B α η₀ η p :=
  fun J => ⟨F (A ⧸ J)⟩

private theorem quotientInverseFormula_of_family
    (R S A B : CommRingCat.{u}) (α : R →+* S) (η₀ : R →+* A)
    (η : S →+* B) (p : A →+* B) (F : incidenceBaseChangeFamily R S A B α η₀ η p)
    (hF : incidenceInverseFamily R S A B α η₀ η p F) :
    quotientInverseFormula R S A B α η₀ η p F :=
  fun J d a => hF (A ⧸ J) d (Ideal.Quotient.mk J a)

private theorem quotientOriginalFormula_of_family
    (R S A B : CommRingCat.{u}) (α : R →+* S) (η₀ : R →+* A)
    (η : S →+* B) (p : A →+* B) (F : incidenceBaseChangeFamily R S A B α η₀ η p)
    (hsq : p.comp η₀ = η.comp α) (hF : incidenceForwardFamily R S A B α η₀ η p F) :
    quotientOriginalFormula R S A B α η₀ η p F := by
  intro J
  let : Algebra R S := α.toAlgebra
  let : Algebra A B := p.toAlgebra
  let : Algebra S B := η.toAlgebra
  let : Module R (A ⧸ J) := Module.compHom (A ⧸ J) η₀
  change ∀ (a : R) (m : A ⧸ J), _
  intro a m
  have h := RingHom.congr_fun hsq a
  change p (η₀ a) = η (α a) at h
  rw [h]
  exact hF (A ⧸ J) (α a) m

private theorem quotientScalarFormula_of_family
    (R S A B : CommRingCat.{u}) (α : R →+* S) (η₀ : R →+* A)
    (η : S →+* B) (p : A →+* B) (F : incidenceBaseChangeFamily R S A B α η₀ η p)
    (hF : incidenceScalarFamily R S A B α η₀ η p F) :
    quotientScalarFormula R S A B α η₀ η p F :=
  fun J d t => hF (A ⧸ J) d t

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)
  (x : nativeExteriorIncidence X Y Z T z w hz hw)

local notation3 (prettyPrint := false) "I'" => nativeExteriorIncidence X Y Z T z w hz hw
local notation3 (prettyPrint := false) "I₀" =>
  correspondenceIncidence X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "P₀" =>
  correspondenceSupportProduct X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "Q" => nativeExteriorParameterDiagonal X Y T z hz Z w hw
local notation3 (prettyPrint := false) "c" =>
  nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw
local notation3 (prettyPrint := false) "q" =>
  nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw
local notation3 (prettyPrint := false) "π" => nativeExteriorIncidenceOriginal X Y Z T z w hz hw
local notation3 (prettyPrint := false) "C₀" => (P₀).presheaf.stalk (q (c x))
local notation3 (prettyPrint := false) "D" => (Q).presheaf.stalk (c x)
local notation3 (prettyPrint := false) "E₀" => (I₀).presheaf.stalk (π x)
local notation3 (prettyPrint := false) "E" => (I').presheaf.stalk x
local notation3 (prettyPrint := false) "α" => ((q).stalkMap (c x)).hom
local notation3 (prettyPrint := false) "η₀" =>
  (nativeExteriorRemainingOriginalIncidenceStalkMap X Y T z hz Z w hw x).hom
local notation3 (prettyPrint := false) "η" => ((c).stalkMap x).hom
local notation3 (prettyPrint := false) "p" => ((π).stalkMap x).hom

/-- The concrete family is the existing native comparison, without any quotient assumptions. -/
private def nativeQuotientConsumerFamily :
    incidenceBaseChangeFamily C₀ D E₀ E α η₀ η p :=
  fun M _ _ => nativeExteriorIncidenceStalkBaseChange X Y Z T z w hz hw x M

local notation3 (prettyPrint := false) "F" =>
  nativeQuotientConsumerFamily X Y Z T z w hz hw x

private theorem nativeQuotientConsumerInverse :
    incidenceInverseFamily C₀ D E₀ E α η₀ η p F :=
  fun M _ _ d m =>
    nativeExteriorIncidenceStalkBaseChange_symm_tmul X Y Z T z w hz hw x M d m

private theorem nativeQuotientConsumerForward :
    incidenceForwardFamily C₀ D E₀ E α η₀ η p F :=
  fun M _ _ d m =>
    nativeExteriorIncidenceStalkBaseChange_tmul X Y Z T z w hz hw x M d m

private theorem nativeQuotientConsumerScalar :
    incidenceScalarFamily C₀ D E₀ E α η₀ η p F :=
  fun M _ _ d =>
    nativeExteriorIncidenceStalkBaseChange_map_smul X Y Z T z w hz hw x M d

-- The actual quotient, for every ideal J, admits the native D-linear equivalence.
example : quotientHasEquiv C₀ D E₀ E α η₀ η p :=
  quotientHasEquiv_of_family C₀ D E₀ E α η₀ η p F

-- The inverse uses c.stalkMap on literal Ideal.Quotient.mk generators.
example : quotientInverseFormula C₀ D E₀ E α η₀ η p F :=
  quotientInverseFormula_of_family C₀ D E₀ E α η₀ η p F
    (nativeQuotientConsumerInverse X Y Z T z w hz hw x)

-- This retains the nondefinitional original-point transport on every quotient class.
example : quotientOriginalFormula C₀ D E₀ E α η₀ η p F :=
  quotientOriginalFormula_of_family C₀ D E₀ E α η₀ η p F
    (nativeExteriorRemainingIncidence_ringSquare X Y Z T z w hz hw x)
    (nativeQuotientConsumerForward X Y Z T z w hz hw x)

-- The actual D action is checked on every tensor with the original quotient module.
example : quotientScalarFormula C₀ D E₀ E α η₀ η p F :=
  quotientScalarFormula_of_family C₀ D E₀ E α η₀ η p F
    (nativeQuotientConsumerScalar X Y Z T z w hz hw x)
