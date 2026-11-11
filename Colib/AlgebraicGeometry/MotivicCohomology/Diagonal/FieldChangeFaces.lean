/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.FieldChangeCycleGrades
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FilteredLimitCycles
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestrictionLocal
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.CurveDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Graph faces of finite flat supports under coefficient change

A rational graph coface of an embedded finite flat family is its full
scheme-theoretic endpoint cycle. This uses the cycle-level Cartier
intersection formula and therefore retains the multiplicities of a
nonreduced family as well as the lengths of its endpoint fibers.

The original coface and field-change maps are from
`Motivic/Cohomology/SuslinVoevodsky/RawFieldChange.lean:158-236` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow TopologicalSpace
open scoped Polynomial

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalFieldChange

open _root_.AlgebraicGeometry.Scheme
open DiagonalFiniteCyclePushforward PolynomialEndpointFiber
open DiagonalCorestrictionBaseChange (simplexAmbientStructure simplexZeroCycleGrade
  cyclePullback_zero_val relativeDimension_zero_of_finite_closedSupport sourceZero_isFinite)

local instance (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (Scheme.unitModule X) :=
  Stacks.Ample.isInvertibleModule_unit X

/-- The native source projection of the correspondence ambient. -/
abbrev ambientProjection (F : Type u) [Field F] (r q : ℕ) :
    ambient F r q ⟶ (source F r).left :=
  pullback.fst (source F r).hom (target F q).hom

private abbrev ambientStructure (F : Type u) [Field F] (r q : ℕ) :
    ambient F r q ⟶ Spec (.of F) :=
  simplexAmbientStructure F r q

section Endpoint

variable (F : Type u) [Field F] (q : ℕ) (i : Fin 2)

private theorem ambientFace_projection_isPullback :
    IsPullback (ambientFace F q i) (ambientProjection F 0 q)
      (ambientProjection F 1 q) (sourceFace F i).left := by
  apply IsPullback.of_right (h₁₂ := pullback.snd (source F 1).hom (target F q).hom)
    (h₂₂ := (source F 1).hom) (v₁₃ := (target F q).hom)
  · rw [ambientFace_snd, MorphismProperty.Over.w (sourceFace F i)]
    exact (IsPullback.of_hasPullback (source F 0).hom (target F q).hom).flip
  · exact ambientFace_fst F q i
  · exact (IsPullback.of_hasPullback (source F 1).hom (target F q).hom).flip

private abbrev ambientParameter : ambient F 1 q ⟶ Spec (.of F[X]) :=
  ambientProjection F 1 q ≫ (sourceChart1 F).hom

private theorem ambientFace_polynomial_isPullback :
    IsPullback (ambientFace F q i) (ambientProjection F 0 q ≫ (sourceChart0 F).hom)
      (ambientParameter F q) (endpoint (i.val : F)) := by
  have h : IsPullback (sourceChart0 F).hom (sourceFace F i).left
      (endpoint (i.val : F)) (sourceChart1 F).hom :=
    IsPullback.of_horiz_isIso ⟨(sourceFace_chart F i).symm⟩
  exact ((ambientFace_projection_isPullback F q i).flip.paste_horiz h).flip

private abbrev endpointSection (a : F) : Γ(Spec (.of F[X]), ⊤) :=
  (Scheme.ΓSpecIso (.of F[X])).inv (Polynomial.X - Polynomial.C a)

private theorem endpoint_ker_eq_zeroScheme (a : F) :
    (endpoint a).ker =
      Stacks.Divisors.zeroScheme (Spec (.of F[X])) (Scheme.unitModule _) (endpointSection F a) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  let U : (Spec (.of F[X])).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hres : (Scheme.unitModule (Spec (.of F[X]))).presheaf.map
      (homOfLE (le_top : U.1 ≤ ⊤)).op (endpointSection F a) = endpointSection F a := by
    change (Spec (.of F[X])).presheaf.map (homOfLE
      (le_top : (⊤ : (Spec (.of F[X])).Opens) ≤ ⊤)).op (endpointSection F a) = _
    simp
  have hzero := Stacks.Divisors.zeroScheme_ideal_of_trivialization
    (Spec (.of F[X])) (Scheme.unitModule _) (endpointSection F a) U
    (LinearEquiv.refl _ _) (endpointSection F a) hres
  change (endpoint a).ker.ideal U = _
  rw [hzero]
  have hker : (endpoint a).ker.ideal U =
      (Ideal.span {Polynomial.X - Polynomial.C a}).map (Scheme.ΓSpecIso (.of F[X])).inv.hom := by
    rw [Scheme.Hom.ker_apply, ← Polynomial.ker_evalRingHom]
    change RingHom.ker (endpoint a).appTop.hom = _
    rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso (.of F)).commRingCatIsoToRingEquiv]
    change RingHom.ker ((Scheme.ΓSpecIso (.of F)).hom.hom.comp (endpoint a).appTop.hom) = _
    rw [← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp,
      ← RingHom.comap_ker]
    exact (Ideal.map_symm (Scheme.ΓSpecIso (.of F[X])).commRingCatIsoToRingEquiv).symm
  simpa only [Ideal.map_span, Set.image_singleton] using hker

private theorem endpoint_ker_effective (a : F) :
    Stacks.Divisors.IsEffectiveCartierDivisor (endpoint a).ker := by
  rw [endpoint_ker_eq_zeroScheme]
  apply isEffectiveCartierDivisor_zeroScheme_of_ne_zero
  exact (map_ne_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of F[X])).inv).1).mpr (Polynomial.X_sub_C_ne_zero a)

private abbrev faceSection : Γ(ambient F 1 q, ⊤) :=
  (ambientParameter F q).appTop (endpointSection F (i.val : F))

private abbrev faceZeroScheme : (ambient F 1 q).IdealSheafData :=
  Stacks.Divisors.zeroScheme (ambient F 1 q) (Scheme.unitModule _) (faceSection F q i)

private theorem faceZeroScheme_comap :
    faceZeroScheme F q i = (endpoint (i.val : F)).ker.comap (ambientParameter F q) := by
  let f := ambientParameter F q
  let a := endpointSection F (i.val : F)
  rw [endpoint_ker_eq_zeroScheme]
  rw [← Stacks.Divisors.zeroScheme_pullback f (Scheme.unitModule _) a]
  exact (AlgebraicGeometry.zeroScheme_eq_of_iso (Scheme.Modules.pullbackUnitIso f)
    (AlgebraicGeometry.SectionsEqualizer.pullbackUnitIso_unit f a)).symm

private theorem ambientFace_ker :
    (ambientFace F q i).ker = faceZeroScheme F q i := by
  let e := (ambientFace_polynomial_isPullback F q i).isoPullback
  have h : e.hom ≫ pullback.fst (ambientParameter F q) (endpoint (i.val : F)) =
      ambientFace F q i := (ambientFace_polynomial_isPullback F q i).isoPullback_hom_fst
  rw [← h, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    faceZeroScheme_comap]

private theorem faceSupport_projection_isPullback {Z : Scheme.{u}} (j : Z ⟶ ambient F 1 q) :
    IsPullback (pullback.snd (ambientFace F q i) j)
      (pullback.fst (ambientFace F q i) j ≫ ambientProjection F 0 q)
      (j ≫ ambientProjection F 1 q) (sourceFace F i).left :=
  (IsPullback.of_hasPullback (ambientFace F q i) j).flip.paste_vert
    (ambientFace_projection_isPullback F q i)

/-- A support finite over the simplex has Noetherian coface fibers. -/
instance faceSupport_isNoetherian {Z : Scheme.{u}} (j : Z ⟶ ambient F 1 q)
    [IsFinite (j ≫ ambientProjection F 1 q)] :
    IsNoetherian (pullback (ambientFace F q i) j : Scheme.{u}) := by
  let p := pullback.fst (ambientFace F q i) j ≫ ambientProjection F 0 q
  let : IsFinite p := MorphismProperty.of_isPullback (faceSupport_projection_isPullback F q i j)
    (inferInstance : IsFinite (j ≫ ambientProjection F 1 q))
  let : IsNoetherian ((𝟭 Scheme).obj (source F 0).left) := simplexSource_isNoetherian F 0
  exact isNoetherian_of_quasiCompact_locallyOfFiniteType p

private theorem source_one_generic_grade :
    relativeDimension (fieldChowSituation F).dimensionFunction (source F 1).hom
      (genericPoint (source F 1).left) = 1 := by
  let S := (𝟭 Scheme).obj (source F 1).left
  let p : S ⟶ Spec (.of F) := (source F 1).hom
  let : LocallyOfFiniteType p := inferInstanceAs (LocallyOfFiniteType (source F 1).hom)
  let : IsIntegral S := source_isIntegral F 1
  have hPoly : topologicalKrullDim (Spec (.of F[X])) = 1 := by
    change topologicalKrullDim (PrimeSpectrum F[X]) = 1
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    rfl
  have hS : topologicalKrullDim S = (1 : WithBot ℕ∞) :=
    (IsHomeomorph.topologicalKrullDim_eq _ (sourceChart1 F).hom.homeomorph.isHomeomorph).trans hPoly
  exact relativeDimension_fieldChowSituation_genericPoint (k := F) p hS

private theorem oneSpan_grade {Z : Scheme.{u}} (j : Z ⟶ ambient F 1 q) [IsClosedImmersion j]
    [IsFinite (j ≫ ambientProjection F 1 q)] [Flat (j ≫ ambientProjection F 1 q)]
    (z : genericPoints Z) :
    relativeDimension (fieldChowSituation F).dimensionFunction (ambientStructure F 1 q)
      (j z.val) = 1 := by
  let p := j ≫ ambientProjection F 1 q
  let s : (source F 1).left ⟶ Spec (.of F) := (source F 1).hom
  let d := (fieldChowSituation F).dimensionFunction
  have hg : p z.val = genericPoint (source F 1).left := by
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using
      mem_genericPoints_of_flat p z.property
  have h := relativeDimension_eq_of_finite_residueField d s p z.val
    (residueField_finite_of_locallyQuasiFinite p z.val)
  have hcomp : j ≫ ambientStructure F 1 q = p ≫ s :=
    (Category.assoc j (ambientProjection F 1 q) s).symm
  have hd : relativeDimension d (j ≫ ambientStructure F 1 q) z.val =
      relativeDimension d (p ≫ s) z.val :=
    congrArg (fun f : Z ⟶ Spec (.of F) => relativeDimension d f z.val) hcomp
  exact (relativeDimension_comp_closedImmersion d j (ambientStructure F 1 q) z.val).symm.trans
    (hd.trans (h.trans ((congrArg (relativeDimension d s) hg).trans (source_one_generic_grade F))))

private theorem closedSpan_gradeBound {C : ChowSituation.{u}} {Z A : Scheme.{u}}
    (s : A ⟶ C.S) [LocallyOfFiniteType s] (j : Z ⟶ A) [IsClosedImmersion j] (d : ℤ)
    (hgrade : ∀ z : genericPoints Z, relativeDimension C.dimensionFunction s (j z.val) = d) :
    schemeDeltaDimension C (j ≫ s) ≤ (d : EInt) := by
  rw [schemeDeltaDimension_eq_iSup]
  refine iSup_le (fun W => ?_)
  have hW : W.2.1.genericPoint ∈ genericPoints Z := by
    change closure {W.2.1.genericPoint} ∈ irreducibleComponents Z
    rw [show closure {W.2.1.genericPoint} = (W : Set Z) from
      W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents (W : Set Z) W.2)]
    exact W.property
  change (relativeDimension C.dimensionFunction (j ≫ s) W.2.1.genericPoint : EInt) ≤ (d : EInt)
  exact le_of_eq (congrArg (fun n : ℤ => (n : EInt))
    ((relativeDimension_comp_closedImmersion C.dimensionFunction j s W.2.1.genericPoint).trans
      (hgrade ⟨_, hW⟩)))

private theorem zeroSpan_grade {Z : Scheme.{u}} (j : Z ⟶ ambient F 0 q) [IsClosedImmersion j]
    [IsFinite (j ≫ ambientProjection F 0 q)] (z : Z) :
    relativeDimension (fieldChowSituation F).dimensionFunction (ambientStructure F 0 q)
      (j z) = 0 := by
  let : IsFinite (source F 0).hom := sourceZero_isFinite F
  let : IsFinite (j ≫ ambientStructure F 0 q) := by
    change IsFinite (j ≫ (ambientProjection F 0 q ≫ (source F 0).hom))
    rw [← Category.assoc]
    infer_instance
  exact relativeDimension_zero_of_finite_closedSupport F (ambientStructure F 0 q) j z

private theorem faceCut_gradeZero {Z : Scheme.{u}} (j : Z ⟶ ambient F 1 q)
    [IsClosedImmersion j] [IsFinite (j ≫ ambientProjection F 1 q)]
    (z : (pullback (ambientFace F q i) j : Scheme.{u})) :
    relativeDimension (fieldChowSituation F).dimensionFunction (ambientStructure F 1 q)
      ((pullback.fst (ambientFace F q i) j ≫ ambientFace F q i) z) = 0 := by
  let m := pullback.fst (ambientFace F q i) j
  let : IsFinite (m ≫ ambientProjection F 0 q) :=
    MorphismProperty.of_isPullback (faceSupport_projection_isPullback F q i j)
      (inferInstance : IsFinite (j ≫ ambientProjection F 1 q))
  have h : ambientFace F q i ≫ ambientStructure F 1 q = ambientStructure F 0 q := by
    simp only [ambientStructure, simplexAmbientStructure, ambientFace_fst_assoc,
      MorphismProperty.Over.w (sourceFace F i)]
  change relativeDimension (fieldChowSituation F).dimensionFunction (ambientStructure F 1 q)
    (ambientFace F q i (m z)) = 0
  rw [← relativeDimension_comp_closedImmersion _ (ambientFace F q i), h]
  exact zeroSpan_grade F q m z

private def faceGysin :
    CycleGroup (fieldChowSituation F) (ambientStructure F 1 q) 1 →+
      CycleGroup (fieldChowSituation F) (ambientStructure F 1 q) 0 :=
  gysinCycleMapPushforward (fieldChowSituation F) (ambientStructure F 1 q) 0
    (Scheme.unitModule _) (faceSection F q i)
    ⟨Scheme.Modules.pullbackUnitIso (faceZeroScheme F q i).subschemeι⟩

private theorem gysin_closedSpan (Z : (ambient F 1 q).IdealSheafData)
    [IsFinite (Z.subschemeι ≫ ambientProjection F 1 q)]
    [Flat (Z.subschemeι ≫ ambientProjection F 1 q)] :
    (faceGysin F q i
      (cycleAssociatedToClosedSubscheme (fieldChowSituation F) (ambientStructure F 1 q)
        Z.subschemeι 1)).val =
      finiteCyclePushforward (pullback.fst (ambientFace F q i) Z.subschemeι ≫ ambientFace F q i)
        (AlgebraicCycle.fundamentalCycle (pullback (ambientFace F q i) Z.subschemeι)) := by
  let C := fieldChowSituation F
  let s := ambientStructure F 1 q
  let D := faceZeroScheme F q i
  have hZ := closedSpan_gradeBound (C := C) s Z.subschemeι 1 (oneSpan_grade F q Z.subschemeι)
  have hDZ : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap Z.subschemeι) := by
    let f := (Z.subschemeι ≫ ambientProjection F 1 q) ≫ (sourceChart1 F).hom
    let : Flat f := inferInstanceAs (Flat
      ((Z.subschemeι ≫ ambientProjection F 1 q) ≫ (sourceChart1 F).hom))
    change Stacks.Divisors.IsEffectiveCartierDivisor ((faceZeroScheme F q i).comap Z.subschemeι)
    rw [faceZeroScheme_comap, ← Scheme.IdealSheafData.comap_comp, ← Category.assoc]
    exact Stacks.Divisors.isPullbackDefined_of_flat f _ (endpoint_ker_effective F (i.val : F))
  have h := gysinCycleMapPushforward_cycleAssociatedToClosedSubscheme C s 0
    (Scheme.unitModule _) (faceSection F q i)
    ⟨Scheme.Modules.pullbackUnitIso D.subschemeι⟩ Z hZ hDZ
  let m := ambientFace F q i
  have hk : D.subschemeι.ker = m.ker := (D.ker_subschemeι).trans (ambientFace_ker F q i).symm
  let a := IsClosedImmersion.lift D.subschemeι m hk.le
  let : IsIso a := IsClosedImmersion.isIso_lift D.subschemeι m hk
  have ha : a ≫ D.subschemeι = m := IsClosedImmersion.lift_fac _ _ _
  let e := (asIso (pullback.map m Z.subschemeι D.subschemeι Z.subschemeι
    a (𝟙 _) (𝟙 _) (by simpa only [Category.comp_id] using ha.symm)
      (by simp only [Category.comp_id, Category.id_comp]))) ≪≫ (Z.comapIso D.subschemeι).symm
  have he : e.hom ≫ ((Z.comap D.subschemeι).subschemeι ≫ D.subschemeι) =
      pullback.fst m Z.subschemeι ≫ m := by
    rw [← Z.comapIso_hom_fst D.subschemeι]
    simp only [e, Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc,
      Iso.inv_hom_id_assoc, pullback.map, pullback.lift_fst_assoc, ha]
  have hc := cycleAssociatedToClosedSubscheme_eq_of_iso C s _ _ e he 0
  have hv := val_cycleAssociatedToClosedSubscheme_eq_finitePushforward_fundamental C s
    (pullback.fst m Z.subschemeι ≫ m) 0 (fun z => faceCut_gradeZero F q i Z.subschemeι z.val)
  exact (congrArg Subtype.val (h.trans hc.symm)).trans hv

private theorem finitePushforward_congr {A B : Scheme.{u}} (f g : A ⟶ B)
    [IsFinite f] [IsFinite g] (h : f = g) (c : AlgebraicCycle A ℤ) :
    finiteCyclePushforward f c = finiteCyclePushforward g c := by
  cases h
  rfl

private theorem gysin_span {Z : Scheme.{u}} (j : Z ⟶ ambient F 1 q)
    [IsClosedImmersion j] [IsFinite (j ≫ ambientProjection F 1 q)]
    [Flat (j ≫ ambientProjection F 1 q)] :
    (faceGysin F q i
      (cycleAssociatedToClosedSubscheme (fieldChowSituation F) (ambientStructure F 1 q) j 1)).val =
      finiteCyclePushforward (pullback.fst (ambientFace F q i) j ≫ ambientFace F q i)
        (AlgebraicCycle.fundamentalCycle (pullback (ambientFace F q i) j)) := by
  let I := j.ker
  let e : Z ≅ I.subscheme := asIso j.toImage
  have he : e.hom ≫ I.subschemeι = j := j.toImage_imageι
  have hp : I.subschemeι ≫ ambientProjection F 1 q = e.inv ≫ (j ≫ ambientProjection F 1 q) := by
    rw [← he, Category.assoc e.hom I.subschemeι (ambientProjection F 1 q), Iso.inv_hom_id_assoc]
  let : IsFinite (I.subschemeι ≫ ambientProjection F 1 q) := by rw [hp]; infer_instance
  let : Flat (I.subschemeι ≫ ambientProjection F 1 q) := by rw [hp]; infer_instance
  let m := ambientFace F q i
  let e' : (pullback m j : Scheme.{u}) ≅ pullback m I.subschemeι :=
    asIso (pullback.map m j m I.subschemeι (𝟙 _) e.hom (𝟙 _)
      (by simp only [Category.comp_id, Category.id_comp])
      (by simpa only [Category.comp_id] using he.symm))
  have he' : e'.hom ≫ (pullback.fst m I.subschemeι ≫ m) = pullback.fst m j ≫ m := by
    simp only [e', asIso_hom, pullback.map, Category.assoc, pullback.lift_fst_assoc,
      Category.id_comp]
  rw [cycleAssociatedToClosedSubscheme_eq_of_iso (fieldChowSituation F)
    (ambientStructure F 1 q) j I.subschemeι e he 1, gysin_closedSpan F q i I]
  rw [← finiteCyclePushforward_fundamentalCycle_iso e', finiteCyclePushforward_comp_apply]
  exact finitePushforward_congr _ _ he' _

private def gradedOne : finiteCorrespondences (source F 1).hom (target F q).hom →+
    CycleGroup (fieldChowSituation F) (ambientStructure F 1 q) 1 where
  toFun c := by
    refine ⟨c.val, (mem_cyclesOfDimension_iff_forall_point
      (fieldChowSituation F) (ambientStructure F 1 q) 1 c.val).mpr ?_⟩
    intro z hz
    let j := (integralComponentAt z).subschemeι
    have h := c.property.2 z hz
    let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
    let : IsFinite (j ≫ ambientProjection F 1 q) := h.1
    let : Flat (j ≫ ambientProjection F 1 q) := supportProjection_flat F 1 q z h
    have hgen : j (genericPoint (integralComponentAt z).subscheme) = z :=
      genericPointOf_integralComponentAt z
    rw [← hgen]
    exact oneSpan_grade F q j ⟨genericPoint _, genericPoint_mem_genericPoints _⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

private theorem gradeOne_span {Z : Scheme.{u}} [IsNoetherian Z] (j : Z ⟶ ambient F 1 q)
    [IsClosedImmersion j] [IsFinite (j ≫ ambientProjection F 1 q)]
    [Flat (j ≫ ambientProjection F 1 q)] :
    gradedOne F q (finiteFlatSpanFundamental (source F 1).hom (target F q).hom j) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation F) (ambientStructure F 1 q) j 1 :=
  Subtype.ext (val_cycleAssociatedToClosedSubscheme_eq_finitePushforward_fundamental
    (fieldChowSituation F) (ambientStructure F 1 q) j 1 (oneSpan_grade F q j)).symm

private theorem graph_face_single_val (z : ambient F 1 q)
    (hz : IsFiniteCorrespondencePoint (source F 1).hom (target F q).hom z) :
    letI : IsFinite ((integralComponentAt z).subschemeι ≫ ambientProjection F 1 q) := hz.1
    (((Cor.graphFunctor F).map (sourceFace F i)) ≫
      singleFiniteCorrespondence (source F 1).hom (target F q).hom z hz 1).val =
        finiteCyclePushforward (pullback.fst (ambientFace F q i) (integralComponentAt z).subschemeι)
          (AlgebraicCycle.fundamentalCycle
            (pullback (ambientFace F q i) (integralComponentAt z).subschemeι)) := by
  let j := (integralComponentAt z).subschemeι
  let : IsFinite (j ≫ ambientProjection F 1 q) := hz.1
  let : Flat (j ≫ ambientProjection F 1 q) := supportProjection_flat F 1 q z hz
  let : IsNoetherian ((𝟭 Scheme).obj (source F 0).left) := simplexSource_isNoetherian F 0
  let : IsNoetherian (correspondenceGraphFiber (source F 1).hom (target F q).hom z
      (sourceFace F i).left) :=
    isNoetherian_correspondenceGraphFiber (source F 1).hom (target F q).hom z
      (sourceFace F i).left hz
  let h := isPullback_correspondenceGraphFiberMap (source F 0).hom (source F 1).hom
    (target F q).hom z (sourceFace F i).left (MorphismProperty.Over.w (sourceFace F i))
  rw [Cor.graph_comp_single_val_eq_fiber F z hz (sourceFace F i)]
  rw [← finiteCyclePushforward_fundamentalCycle_iso h.isoPullback,
    finiteCyclePushforward_comp_apply]
  exact finitePushforward_congr _ _ h.isoPullback_hom_fst.symm _

/-- A rational coface restricts the full finite flat span, including every endpoint length. -/
theorem graph_comp_finiteFlatSpanFundamental_face_val {Z : Scheme.{u}} [IsNoetherian Z]
    (j : Z ⟶ ambient F 1 q) [IsClosedImmersion j]
    [IsFinite (j ≫ ambientProjection F 1 q)] [Flat (j ≫ ambientProjection F 1 q)] :
    (((Cor.graphFunctor F).map (sourceFace F i)) ≫
      finiteFlatSpanFundamental (source F 1).hom (target F q).hom j).val =
      finiteCyclePushforward (pullback.fst (ambientFace F q i) j)
        (AlgebraicCycle.fundamentalCycle (pullback (ambientFace F q i) j)) := by
  let m := ambientFace F q i
  let C := fieldChowSituation F
  let s := ambientStructure F 1 q
  let left := (finiteCyclePushforward m).comp
    ((finiteCorrespondences (source F 0).hom (target F q).hom).subtype.comp
      (Preadditive.leftComp (Cor.mk (target F q)) ((Cor.graphFunctor F).map (sourceFace F i))))
  let right := (cyclesOfDimension C s 0).subtype.comp ((faceGysin F q i).comp (gradedOne F q))
  have heq : left = right := by
    apply finiteCorrespondences.addHom_ext_one (source F 1).hom (target F q).hom
    intro z hz
    let a := (integralComponentAt z).subschemeι
    let : IsIntegral (integralComponentAt z).subscheme := isIntegral_integralComponentAt z
    let : IsFinite (a ≫ ambientProjection F 1 q) := hz.1
    let : Flat (a ≫ ambientProjection F 1 q) := supportProjection_flat F 1 q z hz
    let : IsNoetherian ((𝟭 Scheme).obj (source F 1).left) := simplexSource_isNoetherian F 1
    let : IsNoetherian (integralComponentAt z).subscheme :=
      isNoetherian_of_quasiCompact_locallyOfFiniteType (a ≫ ambientProjection F 1 q)
    have hsingle : singleFiniteCorrespondence (source F 1).hom (target F q).hom z hz 1 =
        finiteFlatSpanFundamental (source F 1).hom (target F q).hom a := by
      classical
      apply Subtype.ext
      have hgen : a (genericPoint (integralComponentAt z).subscheme) = z :=
        genericPointOf_integralComponentAt z
      exact ((finiteCyclePushforward_fundamentalCycle_integral a).trans
        (congrArg (fun x : ambient F 1 q => Function.locallyFinsuppWithin.single x (1 : ℤ))
          hgen)).symm
    change finiteCyclePushforward m
      (((Cor.graphFunctor F).map (sourceFace F i)) ≫
        singleFiniteCorrespondence (source F 1).hom (target F q).hom z hz 1).val =
      (faceGysin F q i (gradedOne F q
        (singleFiniteCorrespondence (source F 1).hom (target F q).hom z hz 1))).val
    rw [graph_face_single_val F q i z hz, finiteCyclePushforward_comp_apply, hsingle,
      gradeOne_span, gysin_span F q i a]
  have h := DFunLike.congr_fun heq (finiteFlatSpanFundamental (source F 1).hom (target F q).hom j)
  change finiteCyclePushforward m
      (((Cor.graphFunctor F).map (sourceFace F i)) ≫
        finiteFlatSpanFundamental (source F 1).hom (target F q).hom j).val =
    (faceGysin F q i (gradedOne F q
      (finiteFlatSpanFundamental (source F 1).hom (target F q).hom j))).val at h
  rw [gradeOne_span, gysin_span F q i j, ← finiteCyclePushforward_comp_apply] at h
  exact finiteCyclePushforward_injective_of_isClosedImmersion m h

end Endpoint

section Scalar

variable {k L : Type u} [Field k] [Field L] [Algebra k L] (q : ℕ) (i : Fin 2)

private abbrev scalarAmbient (r : ℕ) : ambient L r q ⟶ ambient k r q :=
  ambientMap (k := k) (E := L) r q

private abbrev scalarSupport {Z : Scheme.{u}} (j : Z ⟶ ambient k 1 q) :
    (pullback j (scalarAmbient (k := k) (L := L) q 1) : Scheme.{u}) ⟶ ambient L 1 q :=
  pullback.snd j (scalarAmbient (k := k) (L := L) q 1)

private abbrev faceSupport (F : Type u) [Field F] {Z : Scheme.{u}} (j : Z ⟶ ambient F 1 q) :
    (pullback (ambientFace F q i) j : Scheme.{u}) ⟶ ambient F 0 q :=
  pullback.fst (ambientFace F q i) j

private theorem scalarFaceSupport_projection_isPullback {Z : Scheme.{u}} (j : Z ⟶ ambient k 1 q) :
    IsPullback (pullback.fst (faceSupport q i k j) (scalarAmbient (k := k) (L := L) q 0))
      (pullback.snd (faceSupport q i k j) (scalarAmbient (k := k) (L := L) q 0) ≫
        ambientProjection L 0 q)
      (faceSupport q i k j ≫ ambientProjection k 0 q)
      (DiagonalFiniteCyclePushforward.sourceMap (k := k) (E := L) 0) :=
  (IsPullback.of_hasPullback (faceSupport q i k j) (scalarAmbient (k := k) (L := L) q 0)).paste_vert
    (ambientMap_fst_isPullback (k := k) (L := L) 0 q)

/-- The coefficient change of an endpoint of a finite support is Noetherian. -/
instance scalarFaceSupport_isNoetherian {Z : Scheme.{u}} (j : Z ⟶ ambient k 1 q)
    [IsFinite (j ≫ ambientProjection k 1 q)] :
    IsNoetherian (pullback (pullback.fst (ambientFace k q i) j)
      (ambientMap (k := k) (E := L) 0 q) : Scheme.{u}) := by
  let p := faceSupport q i k j ≫ ambientProjection k 0 q
  let : IsFinite p := MorphismProperty.of_isPullback (faceSupport_projection_isPullback k q i j)
    (inferInstance : IsFinite (j ≫ ambientProjection k 1 q))
  let π := pullback.snd (faceSupport q i k j) (scalarAmbient (k := k) (L := L) q 0) ≫
    ambientProjection L 0 q
  let : IsFinite π := MorphismProperty.of_isPullback
    (scalarFaceSupport_projection_isPullback (L := L) q i j) (inferInstance : IsFinite p)
  let : IsNoetherian ((𝟭 Scheme).obj (source L 0).left) := simplexSource_isNoetherian L 0
  exact isNoetherian_of_quasiCompact_locallyOfFiniteType π

private theorem face_after_scalar_isPullback {Z : Scheme.{u}} (j : Z ⟶ ambient k 1 q) :
    IsPullback (faceSupport q i L (scalarSupport (L := L) q j))
      (pullback.snd (ambientFace L q i) (scalarSupport (L := L) q j) ≫
        pullback.fst j (scalarAmbient (k := k) (L := L) q 1))
      (scalarAmbient (k := k) (L := L) q 0 ≫ ambientFace k q i) j := by
  rw [← ambientMap_face (k := k) (E := L) q i]
  exact (IsPullback.of_hasPullback (ambientFace L q i) (scalarSupport (L := L) q j)).paste_vert
    (IsPullback.of_hasPullback j (scalarAmbient (k := k) (L := L) q 1)).flip

private theorem scalar_after_face_isPullback {Z : Scheme.{u}} (j : Z ⟶ ambient k 1 q) :
    IsPullback (pullback.snd (faceSupport q i k j) (scalarAmbient (k := k) (L := L) q 0))
      (pullback.fst (faceSupport q i k j) (scalarAmbient (k := k) (L := L) q 0) ≫
        pullback.snd (ambientFace k q i) j)
      (scalarAmbient (k := k) (L := L) q 0 ≫ ambientFace k q i) j :=
  (IsPullback.of_hasPullback (faceSupport q i k j)
    (scalarAmbient (k := k) (L := L) q 0)).flip.paste_vert
      (IsPullback.of_hasPullback (ambientFace k q i) j)

/-- The graph face after scalar restriction of a prime is the full scalar-changed endpoint. -/
theorem graph_face_cyclePullback_single_val (z : ambient k 1 q)
    (hz : IsFiniteCorrespondencePoint (source k 1).hom (target k q).hom z) :
    let j := (integralComponentAt z).subschemeι
    letI : IsFinite (j ≫ ambientProjection k 1 q) := hz.1
    (((Cor.graphFunctor L).map (sourceFace L i)) ≫
      cyclePullback (k := k) (L := L) 1 q
        (singleFiniteCorrespondence (source k 1).hom (target k q).hom z hz 1)).val =
      finiteCyclePushforward
        (pullback.snd (pullback.fst (ambientFace k q i) j)
          (ambientMap (k := k) (E := L) 0 q))
        (AlgebraicCycle.fundamentalCycle
          (pullback (pullback.fst (ambientFace k q i) j) (ambientMap (k := k) (E := L) 0 q))) := by
  let j := (integralComponentAt z).subschemeι
  let : IsFinite (j ≫ ambientProjection k 1 q) := hz.1
  let jL := scalarSupport (L := L) q j
  let π := jL ≫ ambientProjection L 1 q
  let sq := ambientMap_fst_isPullback (k := k) (L := L) 1 q
  let : IsFinite π := MorphismProperty.of_isPullback (supportPullback_projection_isPullback sq z)
    hz.1
  let : Flat π := MorphismProperty.of_isPullback (supportPullback_projection_isPullback sq z)
    (supportProjection_flat k 1 q z hz)
  let : IsNoetherian ((𝟭 Scheme).obj (source L 1).left) := simplexSource_isNoetherian L 1
  let : IsNoetherian (pullback j (scalarAmbient (k := k) (L := L) q 1) : Scheme.{u}) :=
    isNoetherian_of_quasiCompact_locallyOfFiniteType π
  let sq₁ := face_after_scalar_isPullback (L := L) q i j
  let sq₂ := scalar_after_face_isPullback (L := L) q i j
  let e := sq₁.isoIsPullback _ _ sq₂
  have he := sq₁.isoIsPullback_hom_fst _ _ sq₂
  let β : Cor.mk (source L 1) ⟶ Cor.mk (target L q) :=
    cyclePullback (k := k) (L := L) 1 q
      (singleFiniteCorrespondence (source k 1).hom (target k q).hom z hz 1)
  have hβ : β = finiteFlatSpanFundamental (source L 1).hom (target L q).hom jL := by
    refine (cyclePullback_single (k := k) (L := L) 1 q z hz).trans (Subtype.ext ?_)
    exact supportPullbackCycle_val sq z hz (supportProjection_flat k 1 q z hz)
  have hgraph := congrArg (fun c : Cor.mk (source L 1) ⟶ Cor.mk (target L q) =>
    (((Cor.graphFunctor L).map (sourceFace L i)) ≫ c).val) hβ
  refine hgraph.trans ((graph_comp_finiteFlatSpanFundamental_face_val L q i jL).trans ?_)
  rw [← finiteCyclePushforward_fundamentalCycle_iso e, finiteCyclePushforward_comp_apply]
  exact finitePushforward_congr _ _ he.symm _

private theorem cyclePullback_face_single (z : ambient k 1 q)
    (hz : IsFiniteCorrespondencePoint (source k 1).hom (target k q).hom z) :
    cyclePullback (k := k) (L := L) 0 q
        (((Cor.graphFunctor k).map (sourceFace k i)) ≫
          singleFiniteCorrespondence (source k 1).hom (target k q).hom z hz 1) =
      ((Cor.graphFunctor L).map (sourceFace L i)) ≫
        cyclePullback (k := k) (L := L) 1 q
          (singleFiniteCorrespondence (source k 1).hom (target k q).hom z hz 1) := by
  let j := (integralComponentAt z).subschemeι
  let : IsFinite (j ≫ ambientProjection k 1 q) := hz.1
  let j₀ := faceSupport q i k j
  let p := scalarAmbient (k := k) (L := L) q 0
  let j₀L := pullback.snd j₀ p
  let : IsFinite (j₀ ≫ ambientProjection k 0 q) := MorphismProperty.of_isPullback
    (faceSupport_projection_isPullback k q i j)
    (inferInstance : IsFinite (j ≫ ambientProjection k 1 q))
  let : IsFinite (j₀L ≫ ambientProjection L 0 q) := MorphismProperty.of_isPullback
    (scalarFaceSupport_projection_isPullback (L := L) q i j)
    (inferInstance : IsFinite (j₀ ≫ ambientProjection k 0 q))
  let α : finiteCorrespondences (source k 0).hom (target k q).hom :=
    ((Cor.graphFunctor k).map (sourceFace k i)) ≫
      singleFiniteCorrespondence (source k 1).hom (target k q).hom z hz 1
  let C := fieldChowSituation k
  let s := ambientStructure k 0 q
  have hg : simplexZeroCycleGrade k q α = cycleAssociatedToClosedSubscheme C s j₀ 0 := by
    apply Subtype.ext
    exact (graph_face_single_val k q i z hz).trans
      (val_cycleAssociatedToClosedSubscheme_eq_finitePushforward_fundamental C s j₀ 0
        (fun z => zeroSpan_grade k q j₀ z.val)).symm
  let B := fieldExtensionBaseChangeSituation k L
  let sq := ambientMap_isPullback (k := k) (E := L) 0 q
  have hb := baseChangeCyclePullbackOfIsPullback_cycleAssociatedToClosedSubscheme B rfl s sq j₀ 0
    (closedSpan_gradeBound (C := C) s j₀ 0 (fun z => zeroSpan_grade k q j₀ z.val))
  have hl := cyclePullback_zero_val (k := k) (L := L) q α
  rw [hg, hb] at hl
  have hf := val_cycleAssociatedToClosedSubscheme_eq_finitePushforward_fundamental
    (fieldChowSituation L) (ambientStructure L 0 q) j₀L 0
    (fun z => zeroSpan_grade L q j₀L z.val)
  apply Subtype.ext
  exact (hl.trans hf).trans (graph_face_cyclePullback_single_val (L := L) q i z hz).symm

/-- Arbitrary field restriction commutes with each original signed graph coface. -/
theorem cyclePullback_face (α : Cor.mk (source k 1) ⟶ Cor.mk (target k q)) :
    cyclePullback (k := k) (L := L) 0 q
      ((Cor.simplexProductCosimplicial (Cor.mk (SmoothSite.base (Spec (.of k))))).δ i ≫ α) =
    (Cor.simplexProductCosimplicial (Cor.mk (SmoothSite.base (Spec (.of L))))).δ i ≫
      cyclePullback (k := k) (L := L) 1 q α := by
  let δk := (Cor.graphFunctor k).map (sourceFace k i)
  let δL := (Cor.graphFunctor L).map (sourceFace L i)
  have h : (cyclePullback (k := k) (L := L) 0 q).comp
      (Preadditive.leftComp (Cor.mk (target k q)) δk) =
    (Preadditive.leftComp (Cor.mk (target L q)) δL).comp
      (cyclePullback (k := k) (L := L) 1 q) := by
    apply finiteCorrespondences.addHom_ext_one (source k 1).hom (target k q).hom
    intro z hz
    exact cyclePullback_face_single (L := L) q i z hz
  change cyclePullback (k := k) (L := L) 0 q (δk ≫ α) =
    δL ≫ cyclePullback (k := k) (L := L) 1 q α
  exact DFunLike.congr_fun h α

end Scalar

end AlgebraicGeometry.MotivicCohomology.DiagonalFieldChange
