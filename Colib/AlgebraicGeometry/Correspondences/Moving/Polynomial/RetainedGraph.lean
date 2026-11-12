/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.ClosedEndpointSpecialization
public import Colib.AlgebraicGeometry.Correspondences.Moving.Polynomial.PrincipalFamily
public import Colib.AlgebraicGeometry.Morphisms.ClosedImmersion.SeparatedBasePair
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.ParameterFiber

/-! # The closed graph of the original retained curve -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.Cor.PrincipalOrder

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.AffineLineFiber
open _root_.AlgebraicGeometry.Scheme.PolynomialSectionPencil
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k))) {C V : Scheme.{u}}
  [IsNoetherian V] (q : C ⟶ X.left) [IsProper q] (j : V ⟶ C) [IsOpenImmersion j]
  [SmoothOfRelativeDimension 1 (j ≫ q)]

/-- The retained curve itself is an object of the original smooth site. -/
def retainedSite : SmoothSite (Spec (.of k)) := by
  let : Smooth (j ≫ q) := SmoothOfRelativeDimension.smooth (n := 1) (f := j ≫ q)
  let : Smooth (j ≫ q ≫ X.hom) := by
    rw [← Category.assoc]
    infer_instance
  let : IsSeparated (j ≫ q ≫ X.hom) := inferInstance
  let : QuasiCompact (j ≫ q ≫ X.hom) := ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  exact SmoothSite.mk (j ≫ q ≫ X.hom)

@[simp]
theorem retainedSite_hom : (retainedSite X q j).hom = j ≫ q ≫ X.hom := rfl

theorem retainedIdentityBase : j ≫ q ≫ X.hom = 𝟙 V ≫ (retainedSite X q j).hom := by
  rw [Category.id_comp, retainedSite_hom]

/-- The structure graph into the product with the actual retained scheme. -/
def retainedGraph : V ⟶ pullback X.hom (retainedSite X q j).hom :=
  pullback.lift (j ≫ q) (𝟙 V) (by rw [Category.id_comp, retainedSite_hom, Category.assoc])

@[reassoc]
theorem retainedGraph_fst :
    retainedGraph X q j ≫ pullback.fst X.hom (retainedSite X q j).hom = j ≫ q :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem retainedGraph_snd :
    retainedGraph X q j ≫ pullback.snd X.hom (retainedSite X q j).hom = 𝟙 V :=
  pullback.lift_snd _ _ _

instance retainedGraph_isClosedImmersion : IsClosedImmersion (retainedGraph X q j) := by
  have H : IsPullback (j ≫ q) (𝟙 V) (𝟙 X.left) (j ≫ q) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  exact isClosedImmersion_pullbackLift_of_separated_base _ _ _ _ H X.hom _ _
    (Category.id_comp _) (Category.assoc _ _ _) _

local notation "L" => SmoothSite.product X (polynomialAffineLine (CommRingCat.of k))
set_option quotPrecheck false in
local notation "t" => (q ≫ X.hom)

/-- The actual parameter-preserving projection of the retained family. -/
def retainedFamilyProjection : parameterSpace (j ≫ t) ⟶ (L).left :=
  parameterMap t j ≫ parameterMap X.hom q

omit [IsNoetherian V] [IsProper q] [IsOpenImmersion j]
  [SmoothOfRelativeDimension 1 (j ≫ q)] in
theorem retainedFamilyProjection_isPullback :
    IsPullback (retainedFamilyProjection X q j) (projection (j ≫ t))
      (projection X.hom) (j ≫ q) :=
  (parameterMap_isPullback t j).flip.paste_horiz (parameterMap_isPullback X.hom q).flip

/-- The structure graph of the retained family into the original product. -/
def retainedFamilyGraph : parameterSpace (j ≫ t) ⟶ pullback (L).hom (retainedSite X q j).hom :=
  pullback.lift (retainedFamilyProjection X q j) (projection (j ≫ t)) (by
    change retainedFamilyProjection X q j ≫ projection X.hom ≫ X.hom =
      projection (j ≫ t) ≫ (j ≫ q ≫ X.hom)
    have h := congrArg (· ≫ X.hom) (retainedFamilyProjection_isPullback X q j).w
    simpa only [Category.assoc] using h)

@[reassoc]
theorem retainedFamilyGraph_fst :
    retainedFamilyGraph X q j ≫ pullback.fst (L).hom (retainedSite X q j).hom =
      retainedFamilyProjection X q j := pullback.lift_fst _ _ _

@[reassoc]
theorem retainedFamilyGraph_snd :
    retainedFamilyGraph X q j ≫ pullback.snd (L).hom (retainedSite X q j).hom =
      projection (j ≫ t) := pullback.lift_snd _ _ _

instance retainedFamilyGraph_isClosedImmersion : IsClosedImmersion (retainedFamilyGraph X q j) :=
  isClosedImmersion_pullbackLift_of_separated_base _ _ _ _
    (retainedFamilyProjection_isPullback X q j) X.hom _ _ rfl (Category.assoc _ _ _) _

@[reassoc]
theorem retainedFamilyGraph_parameter :
    retainedFamilyGraph X q j ≫
        pullback.fst (L).hom (retainedSite X q j).hom ≫ parameterProjection X.hom =
      parameterProjection (j ≫ t) := by
  rw [retainedFamilyGraph_fst_assoc]
  change (parameterMap t j ≫ parameterMap X.hom q) ≫ parameterProjection X.hom =
    parameterProjection (j ≫ t)
  rw [Category.assoc, parameterMap_snd X.hom q, parameterMap_snd t j]

/-- The native polynomial section is the literal scalar-evaluation morphism. -/
theorem polynomialAffineSection_left (a : k) :
    (polynomialAffineSection (.of k) X a).left = endpoint X.hom a := rfl

theorem polynomialAffineSection_isPullback (a : k) :
    IsPullback (polynomialAffineSection (.of k) X a).left
      X.hom (parameterProjection X.hom) (point a) := by
  rw [polynomialAffineSection_left]
  exact (endpoint_isPullback X.hom a).flip

/-- On the entire scalar fiber, the retained family graph is the original
structure graph of the retained curve. -/
theorem retainedFamilyGraph_endpoint (a : k) :
    (endpointFiberIso (j ≫ t) a).hom ≫
      closedSupportEndpointMapOfParameterEq (polynomialAffineSection (.of k) X a)
        (parameterProjection X.hom) a (polynomialAffineSection_isPullback X a)
        (retainedFamilyGraph X q j) (parameterProjection (j ≫ t))
        (retainedFamilyGraph_parameter X q j) = retainedGraph X q j := by
  let φ := polynomialAffineSection (.of k) X a
  let m := retainedFamilyGraph X q j
  let e := closedSupportEndpointMapOfParameterEq φ (parameterProjection X.hom) a
    (polynomialAffineSection_isPullback X a) m (parameterProjection (j ≫ t))
    (retainedFamilyGraph_parameter X q j)
  have he := closedSupportEndpointMapOfParameterEq_ambient φ (parameterProjection X.hom) a
    (polynomialAffineSection_isPullback X a) m (parameterProjection (j ≫ t))
    (retainedFamilyGraph_parameter X q j)
  have hp : e ≫ pullback.fst X.hom (retainedSite X q j).hom ≫ φ.left =
      inclusion (parameterProjection (j ≫ t)) a ≫ retainedFamilyProjection X q j := by
    simpa only [Category.assoc, correspondenceGraphFiberAmbientMap, pullback.map,
      pullback.lift_fst, m, retainedFamilyGraph_fst] using
      congrArg (· ≫ pullback.fst (L).hom (retainedSite X q j).hom) he
  have hs : e ≫ pullback.snd X.hom (retainedSite X q j).hom =
      inclusion (parameterProjection (j ≫ t)) a ≫ projection (j ≫ t) := by
    simpa only [Category.assoc, correspondenceGraphFiberAmbientMap, pullback.map,
      pullback.lift_snd, Category.comp_id, m, retainedFamilyGraph_snd] using
      congrArg (· ≫ pullback.snd (L).hom (retainedSite X q j).hom) he
  let : IsClosedImmersion φ.left := by
    change IsClosedImmersion (polynomialAffineSection (.of k) X a).left
    rw [polynomialAffineSection_left]
    infer_instance
  change (endpointFiberIso (j ≫ t) a).hom ≫ e = retainedGraph X q j
  apply pullback.hom_ext
  · apply (cancel_mono φ.left).mp
    calc
      _ = endpoint (j ≫ t) a ≫ retainedFamilyProjection X q j := by
        simp only [Category.assoc, hp, endpointFiberIso_hom_inclusion_assoc]
      _ = (j ≫ q) ≫ endpoint X.hom a := by
        change endpoint (j ≫ t) a ≫ (parameterMap t j ≫ parameterMap X.hom q) = _
        rw [← Category.assoc, endpoint_parameterMap, Category.assoc,
          endpoint_parameterMap, ← Category.assoc]
      _ = _ := by
        rw [retainedGraph_fst, show φ.left = endpoint X.hom a from polynomialAffineSection_left X a]
  · simp only [Category.assoc, hs, endpointFiberIso_hom_inclusion_assoc, endpoint_projection,
      retainedGraph_snd]

end AlgebraicGeometry.Cor.PrincipalOrder
