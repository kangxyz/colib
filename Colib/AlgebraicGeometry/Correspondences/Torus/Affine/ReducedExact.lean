/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.CycleNorm
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusIdentityQuotientIntegral

/-!
# The actual reduced-torus divisor sequence on integral affine sources

The norm is the direct determinant norm of the actual finite prime supports.
The canonical first-power target is compared by its actual graph isomorphism,
and the norm descends through the evaluated, already chosen presheaf cokernel.
The boundary map is the genuine rational divisor followed by that quotient.

No new quotient object, unspecified norm, transfer structure on units, or
assumed exactness is introduced. Coefficients remain in universe `u + 1`.
This is an objectwise affine result. Naturality for changes of the coefficient
ring and descent to the ordinary smooth site are separate obligations.

Implementation provenance: `motivic_source_a6805c4`,
`Motivic/Cohomology/WeightOne/Geometry/ReducedTorusNorm.lean:50-68` and
`Motivic/Cohomology/WeightOne/Geometry/ReducedTorusExact.lean:41-254`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.Chow
open Polynomial.BoundaryOneRationalFunctions

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers

variable {k R : Type u} [Field k] [CommRing R]
variable (f : Spec (.of R) ⟶ Spec (.of k)) [Smooth f] [IsSeparated f] [QuasiCompact f]

/-- The actual affine unit point, in the existing smooth site. -/
def smoothUnitPoint (v : Rˣ) : mk f ⟶ multiplicativeGroupObject (Spec (.of k)) :=
  homMk (nativeAffineTorusPoint f v).left (affineUnitPoint_over f v)

/-- Its correspondence is the original native componentwise unit graph. -/
theorem graph_smoothUnitPoint (v : Rˣ) :
    (Cor.graphFunctor k).map (smoothUnitPoint f v) =
      unitGraphCycle f v (Cor.finite_genericPoints k (Cor.mk (mk f))) := rfl

/-- The actual unit-one smooth morphism is the base structure followed by the identity section. -/
theorem smoothUnitPoint_one :
    smoothUnitPoint f 1 = structureMorphism (mk f) ≫ torusOne (Spec (.of k)) := by
  apply MorphismProperty.Over.Hom.ext
  exact affineUnitPoint_one f

/-- Actual postcomposition by the first-power comparison, on native correspondence groups. -/
def powerOneCycleEquiv :
    (Cor.mk (mk f) ⟶ Cor.mk (torusPower (Spec (.of k)) 1)) ≃+
      finiteCorrespondences f (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)) := by
  let e : Cor.mk (torusPower (Spec (.of k)) 1) ≅
      Cor.mk (multiplicativeGroupObject (Spec (.of k))) :=
    (Cor.graphFunctor k).mapIso (torusPowerOneIso (Spec (.of k)))
  let E : (Cor.mk (mk f) ⟶ Cor.mk (torusPower (Spec (.of k)) 1)) ≃+
      (Cor.mk (mk f) ⟶ Cor.mk (multiplicativeGroupObject (Spec (.of k)))) :=
    { toFun := fun z => z ≫ e.hom
      invFun := fun z => z ≫ e.inv
      left_inv := fun z =>
        (Category.assoc z e.hom e.inv).trans
          ((congrArg (fun a => z ≫ a) e.hom_inv_id).trans (Category.comp_id z))
      right_inv := fun z =>
        (Category.assoc z e.inv e.hom).trans
          ((congrArg (fun a => z ≫ a) e.inv_hom_id).trans (Category.comp_id z))
      map_add' := map_add (Preadditive.rightComp (Cor.mk (mk f)) e.hom) }
  exact E

/-- The canonical identity-axis graph becomes the literal native unit-one graph. -/
theorem powerOneCycleEquiv_identityGraph :
    powerOneCycleEquiv f (torusIdentityGraph k (mk f)) =
      unitGraphCycle f 1 (Cor.finite_genericPoints k (Cor.mk (mk f))) := by
  change torusIdentityGraph k (mk f) ≫
    (Cor.graphFunctor k).map (torusPowerOneIso (Spec (.of k))).hom = _
  rw [torusIdentityGraph_powerOneIso, ← smoothUnitPoint_one, graph_smoothUnitPoint]

variable [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]

/-- The actual support determinant norm on the original first torus power. -/
def powerOneNorm :
    (Cor.mk (mk f) ⟶ Cor.mk (torusPower (Spec (.of k)) 1)) →+ Additive Rˣ :=
  (cycleNorm f).comp (powerOneCycleEquiv f).toAddMonoidHom

/-- The actual boundary divisor with the original first torus-power target. -/
def powerOneBoundaryDivisor : Additive (group R) →+
    (Cor.mk (mk f) ⟶ Cor.mk (torusPower (Spec (.of k)) 1)) :=
  (powerOneCycleEquiv f).symm.toAddMonoidHom.comp (boundaryDivisor f)

omit [IsDomain R] [IsIntegrallyClosed R] in
theorem powerOneCycleEquiv_boundaryDivisor (m : Additive (group R)) :
    powerOneCycleEquiv f (powerOneBoundaryDivisor f m) = boundaryDivisor f m :=
  (powerOneCycleEquiv f).apply_symm_apply _

/-- The actual norm annihilates the actual canonical identity-axis graph. -/
theorem powerOneNorm_identityGraph :
    powerOneNorm f (torusIdentityGraph k (mk f)) = 0 := by
  change cycleNorm f (powerOneCycleEquiv f (torusIdentityGraph k (mk f))) = 0
  rw [powerOneCycleEquiv_identityGraph, cycleNorm_unitGraph]
  rfl

/-- The actual boundary divisor has trivial determinant norm. -/
theorem powerOneNorm_boundaryDivisor (m : Additive (group R)) :
    powerOneNorm f (powerOneBoundaryDivisor f m) = 0 := by
  change cycleNorm f (powerOneCycleEquiv f (powerOneBoundaryDivisor f m)) = 0
  rw [powerOneCycleEquiv_boundaryDivisor, cycleNorm_boundaryDivisor]

/-- Every unit is reached, using the actual unit graph and the genuine target comparison. -/
theorem powerOneNorm_surjective : Function.Surjective (powerOneNorm f) := by
  intro u
  obtain ⟨c, hc⟩ := cycleNorm_surjective f u
  exact ⟨(powerOneCycleEquiv f).symm c,
    (congrArg (cycleNorm f) ((powerOneCycleEquiv f).apply_symm_apply c)).trans hc⟩

/-- The concrete norm kernel before the quotient retains the literal signed identity graph. -/
theorem powerOneNorm_eq_zero_iff
    (z : Cor.mk (mk f) ⟶ Cor.mk (torusPower (Spec (.of k)) 1)) :
    powerOneNorm f z = 0 ↔ ∃ (m : Additive (group R)) (n : ℤ),
      z = powerOneBoundaryDivisor f m + n • torusIdentityGraph k (mk f) := by
  constructor
  · intro hz
    obtain ⟨m, n, h⟩ := (cycleNorm_eq_zero_iff f
      (Cor.finite_genericPoints k (Cor.mk (mk f))) (powerOneCycleEquiv f z)).mp hz
    refine ⟨m, n, (powerOneCycleEquiv f).injective ?_⟩
    simpa only [map_add, map_zsmul, powerOneCycleEquiv_boundaryDivisor,
      powerOneCycleEquiv_identityGraph] using h
  · rintro ⟨m, n, rfl⟩
    rw [map_add, map_zsmul, powerOneNorm_boundaryDivisor,
      powerOneNorm_identityGraph, smul_zero, add_zero]

/-- No nonzero genuine boundary divisor is removed by the identity-axis relation. -/
theorem powerOneBoundaryDivisor_identityGraph_intersection
    (m : Additive (group R)) (n : ℤ)
    (h : powerOneBoundaryDivisor f m = n • torusIdentityGraph k (mk f)) : m = 0 ∧ n = 0 := by
  have he := congrArg (powerOneCycleEquiv f) h
  rw [powerOneCycleEquiv_boundaryDivisor, map_zsmul, powerOneCycleEquiv_identityGraph] at he
  exact boundaryDivisor_identityGraph_intersection f
    (Cor.finite_genericPoints k (Cor.mk (mk f))) m n he

/-- The direct norm in exactly the coefficient universe of the canonical motivic input. -/
def largePowerOneNorm : sections (torusRepresentable k 1) (Cor.mk (mk f)) ⟶
    AddCommGrpCat.of (ULift.{u + 1} (Additive Rˣ)) :=
  AddCommGrpCat.ofHom {
    toFun z := ULift.up (powerOneNorm f z.down)
    map_zero' := by change ULift.up (powerOneNorm f 0) = ULift.up 0; rw [map_zero]
    map_add' z w := by
      change ULift.up (powerOneNorm f (z.down + w.down)) =
        ULift.up (powerOneNorm f z.down + powerOneNorm f w.down)
      rw [map_add] }

/-- The actual defining relation has zero norm, proved on its actual identity-axis image. -/
theorem relation_largePowerOneNorm :
    (torusRelation k 1).app (op (Cor.mk (mk f))) ≫ largePowerOneNorm f = 0 := by
  have : IsIntegral (SmoothSite.mk f).left := inferInstanceAs (IsIntegral (Spec (.of R)))
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  have hm : (torusRelation k 1).app (op (Cor.mk (mk f))) s ∈
      torusIdentityRelations k 1 (Cor.mk (mk f)) := by
    rw [← range_torusRelation]
    exact ⟨s, rfl⟩
  obtain ⟨n, hn⟩ := (mem_torusIdentityRelations_one_iff (mk f) _).mp hm
  change largePowerOneNorm f ((torusRelation k 1).app (op (Cor.mk (mk f))) s) = 0
  rw [hn]
  change ULift.up (powerOneNorm f (n • torusIdentityGraph k (mk f))) = ULift.up 0
  rw [map_zsmul, powerOneNorm_identityGraph, smul_zero]

/-- The ordinary norm on the actual evaluated canonical reduced-torus cokernel. -/
def reducedNormApp : sections (reducedTorus k 1) (Cor.mk (mk f)) ⟶
    AddCommGrpCat.of (ULift.{u + 1} (Additive Rˣ)) :=
  (PreservesCokernel.iso
    ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op (Cor.mk (mk f))))
    (torusRelation k 1)).hom ≫
      cokernel.desc ((torusRelation k 1).app (op (Cor.mk (mk f))))
        (largePowerOneNorm f) (relation_largePowerOneNorm f)

/-- The descended map recovers the direct support determinant norm on every signed cycle. -/
@[reassoc] theorem toReducedTorus_reducedNormApp :
    (toReducedTorus k 1).hom.app (op (Cor.mk (mk f))) ≫ reducedNormApp f =
      largePowerOneNorm f := by
  change ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op (Cor.mk (mk f)))).map
    (cokernel.π (torusRelation k 1)) ≫
      ((PreservesCokernel.iso
        ((evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op (Cor.mk (mk f))))
        (torusRelation k 1)).hom ≫ _) = _
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  exact cokernel.π_desc _ _ _

@[simp] theorem reducedNormApp_toReduced
    (z : Cor.mk (mk f) ⟶ Cor.mk (torusPower (Spec (.of k)) 1)) :
    reducedNormApp f ((toReducedTorus k 1).hom.app (op (Cor.mk (mk f))) (ULift.up z)) =
      ULift.up (powerOneNorm f z) :=
  congrArg (fun h => h (ULift.up z)) (toReducedTorus_reducedNormApp f)

/-- The actual boundary divisor followed by the original quotient, in the large universe. -/
def reducedBoundaryDivisor : AddCommGrpCat.of (ULift.{u + 1} (Additive (group R))) ⟶
    sections (reducedTorus k 1) (Cor.mk (mk f)) :=
  AddCommGrpCat.ofHom {
    toFun m := (toReducedTorus k 1).hom.app (op (Cor.mk (mk f)))
      (ULift.up (powerOneBoundaryDivisor f m.down))
    map_zero' := by
      change (toReducedTorus k 1).hom.app (op (Cor.mk (mk f)))
        (ULift.up (powerOneBoundaryDivisor f 0)) = 0
      rw [map_zero]
      exact map_zero _
    map_add' m n := by
      change (toReducedTorus k 1).hom.app (op (Cor.mk (mk f)))
        (ULift.up (powerOneBoundaryDivisor f (m.down + n.down))) = _
      rw [map_add]
      exact map_add _ _ _ }

/-- The genuine reduced divisor followed by the genuine reduced norm is zero. -/
@[reassoc (attr := simp)] theorem reducedBoundaryDivisor_norm :
    reducedBoundaryDivisor f ≫ reducedNormApp f = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro m
  exact (reducedNormApp_toReduced f (powerOneBoundaryDivisor f m.down)).trans
    (congrArg ULift.up (powerOneNorm_boundaryDivisor f m.down))

/-- The actual divisor remains injective in the canonical reduced sections. -/
theorem reducedBoundaryDivisor_injective : Function.Injective (reducedBoundaryDivisor f) := by
  have : IsIntegral (SmoothSite.mk f).left := inferInstanceAs (IsIntegral (Spec (.of R)))
  apply (injective_iff_map_eq_zero (reducedBoundaryDivisor f).hom).mpr
  intro m hm
  obtain ⟨n, hn⟩ := (toReducedTorus_eq_zero_iff_identityGraph (mk f)
    (ULift.up (powerOneBoundaryDivisor f m.down))).mp hm
  have h := (powerOneBoundaryDivisor_identityGraph_intersection f m.down n
    (congrArg ULift.down hn)).1
  exact ULift.ext h

/-- The actual reduced norm is onto, without any chosen section of the quotient. -/
theorem reducedNormApp_surjective : Function.Surjective (reducedNormApp f) := by
  intro u
  obtain ⟨z, hz⟩ := powerOneNorm_surjective f u.down
  exact ⟨(toReducedTorus k 1).hom.app (op (Cor.mk (mk f))) (ULift.up z),
    (reducedNormApp_toReduced f z).trans (congrArg ULift.up hz)⟩

/-- Exactness for the actual canonical reduced section, not for a replacement quotient. -/
theorem reducedNormApp_eq_zero_iff
    (z : sections (reducedTorus k 1) (Cor.mk (mk f))) :
    reducedNormApp f z = 0 ↔ ∃ m, reducedBoundaryDivisor f m = z := by
  constructor
  · intro hz
    obtain ⟨a, rfl⟩ := toReducedTorus_surjective k 1 (Cor.mk (mk f)) z
    have hn : powerOneNorm f a.down = 0 :=
      congrArg ULift.down ((reducedNormApp_toReduced f a.down).symm.trans hz)
    obtain ⟨m, n, hm⟩ := (powerOneNorm_eq_zero_iff f a.down).mp hn
    refine ⟨ULift.up m, ?_⟩
    change (toReducedTorus k 1).hom.app (op (Cor.mk (mk f)))
        (ULift.up (powerOneBoundaryDivisor f m)) =
      (toReducedTorus k 1).hom.app (op (Cor.mk (mk f))) (ULift.up a.down)
    rw [hm, toReducedTorus_add_identityGraph]
  · rintro ⟨m, rfl⟩
    exact congrArg (fun h => h m) (reducedBoundaryDivisor_norm f)

/-- The three actual large-coefficient groups with their actual divisor and norm. -/
def reducedDivisorShortComplex : ShortComplex AddCommGrpCat.{u + 1} :=
  ShortComplex.mk (reducedBoundaryDivisor f) (reducedNormApp f) (reducedBoundaryDivisor_norm f)

/-- A concrete short exact sequence on the chosen canonical reduced-torus section. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/WeightOne/Geometry/ReducedTorusExact.lean:214-254"
  "adaptation"
    "Actual boundary injection, kernel and norm surjectivity on integral affine sections"]
theorem reducedDivisorShortComplex_shortExact : (reducedDivisorShortComplex f).ShortExact where
  exact := (ShortComplex.ab_exact_iff _).mpr (fun z hz =>
    (reducedNormApp_eq_zero_iff f z).mp hz)
  mono_f := (AddCommGrpCat.mono_iff_injective _).mpr (reducedBoundaryDivisor_injective f)
  epi_g := (AddCommGrpCat.epi_iff_surjective _).mpr (reducedNormApp_surjective f)

end AlgebraicGeometry.NativeTorusPolynomial
