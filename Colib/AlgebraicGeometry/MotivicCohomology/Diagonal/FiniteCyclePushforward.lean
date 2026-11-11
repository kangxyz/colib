/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.FiniteSupportPushforward
public import Colib.AlgebraicGeometry.Simplex.BaseChange
public import Colib.AlgebraicGeometry.Sites.Smooth.Simplex.GeometricallyIntegral
public import Colib.AlgebraicGeometry.Sites.Smooth.Torus

/-!
# Finite pushforward of diagonal simplex cycles

The coefficient projection of the actual simplex-times-torus product is a
base change of the scalar morphism. Its finite pushforward preserves the
native finite-correspondence subgroup and uses each signed prime's residue
degree, including when different primes have the same image.

Adapted from `Motivic/Cohomology/WeightTwo/Corestriction.lean:38-202` at
`motivic_source_a6805c4`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Function.locallyFinsuppWithin Stacks.Chow

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalFiniteCyclePushforward

open _root_.AlgebraicGeometry.Scheme

/-- The original source in singular degree `r`. -/
abbrev source (F : Type u) [Field F] (r : ℕ) : SmoothSite (Spec (.of F)) :=
  SmoothSite.product (SmoothSite.base (Spec (.of F))) (AlgebraicSimplex.smoothSiteObj F r)

/-- The original ordered torus target in weight `q`. -/
abbrev target (F : Type u) [Field F] (q : ℕ) : SmoothSite (Spec (.of F)) :=
  SmoothSite.torusPower (Spec (.of F)) q

/-- The native ambient of the finite correspondences in degree `r` and weight `q`. -/
abbrev ambient (F : Type u) [Field F] (r q : ℕ) : Scheme.{u} :=
  pullback (source F r).hom (target F q).hom

/-- The map of relative products of two Cartesian squares is Cartesian over the same base. -/
theorem productMap_isPullback {S T X Y X' Y' : Scheme.{u}}
    {c : T ⟶ S} {f : X ⟶ S} {g : Y ⟶ S} {f' : X' ⟶ T} {g' : Y' ⟶ T}
    {a : X' ⟶ X} {b : Y' ⟶ Y}
    (ha : IsPullback a f' f c) (hb : IsPullback b g' g c) :
    IsPullback (pullback.map f' g' f g a b c ha.w.symm hb.w.symm)
      (pullback.fst f' g' ≫ f') (pullback.fst f g ≫ f) c := by
  let m := pullback.map f' g' f g a b c ha.w.symm hb.w.symm
  have hm : IsPullback m (pullback.fst f' g') (pullback.fst f g) a := by
    apply IsPullback.of_right (h₁₂ := pullback.snd f g) (h₂₂ := f) (v₁₃ := g)
    · simpa only [m, pullback.map, pullback.lift_snd, ha.w] using
        (IsPullback.of_hasPullback f' g').flip.paste_horiz hb
    · exact pullback.lift_fst _ _ _
    · exact (IsPullback.of_hasPullback f g).flip
  exact hm.paste_vert ha

variable {k E : Type u} [Field k] [Field E] [Algebra k E]

/-- The scalar morphism for the given field extension. -/
abbrev scalarMap : Spec (.of E) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k E))

/-- The original projection on the base-times-simplex source. -/
def sourceMap (r : ℕ) : (source E r).left ⟶ (source k r).left :=
  pullback.map _ _ _ _ (scalarMap (k := k) (E := E))
    (Spec.map (CommRingCat.ofHom (AlgebraicSimplex.mapCoefficients (algebraMap k E) r)))
    (scalarMap (k := k) (E := E)) (by simp [SmoothSite.base])
    (AlgebraicSimplex.mapCoefficients_isPullback (algebraMap k E) r).w.symm

/-- The source projection is the actual scalar base change. -/
theorem sourceMap_isPullback (r : ℕ) :
    IsPullback (sourceMap (k := k) (E := E) r) (source E r).hom (source k r).hom
      (scalarMap (k := k) (E := E)) := by
  unfold sourceMap
  exact productMap_isPullback (IsPullback.id_vert _)
    (AlgebraicSimplex.mapCoefficients_isPullback (algebraMap k E) r)

/-- The source projection retains the original coefficient map of the simplex. -/
@[reassoc]
theorem sourceMap_snd (r : ℕ) :
    sourceMap (k := k) (E := E) r ≫
      pullback.snd (SmoothSite.base (Spec (.of k))).hom (AlgebraicSimplex.structureMap k r) =
    pullback.snd (SmoothSite.base (Spec (.of E))).hom (AlgebraicSimplex.structureMap E r) ≫
      Spec.map (CommRingCat.ofHom (AlgebraicSimplex.mapCoefficients (algebraMap k E) r)) :=
  pullback.lift_snd _ _ _

/-- Scalar projection of the native multiplicative group, retaining its integral factor. -/
def multiplicativeGroupMap :
    (SmoothSite.multiplicativeGroupObject (Spec (.of E))).left ⟶
      (SmoothSite.multiplicativeGroupObject (Spec (.of k))).left :=
  pullback.lift (pullback.fst _ _)
    ((SmoothSite.multiplicativeGroupObject (Spec (.of E))).hom ≫ scalarMap)
    (specULiftZIsTerminal.hom_ext _ _)

/-- The scalar square of the native multiplicative group is Cartesian. -/
theorem multiplicativeGroupMap_isPullback :
    IsPullback (multiplicativeGroupMap (k := k) (E := E))
      (SmoothSite.multiplicativeGroupObject (Spec (.of E))).hom
      (SmoothSite.multiplicativeGroupObject (Spec (.of k))).hom (scalarMap (k := k) (E := E)) := by
  let p := multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ))
  let b := specULiftZIsTerminal.from (Spec (.of k))
  let b' := specULiftZIsTerminal.from (Spec (.of E))
  have hb : scalarMap (k := k) (E := E) ≫ b = b' :=
    specULiftZIsTerminal.hom_ext _ _
  apply IsPullback.of_right (h₁₂ := pullback.fst p b) (h₂₂ := b) (v₁₃ := p)
  · have hfst : multiplicativeGroupMap (k := k) (E := E) ≫ pullback.fst p b =
        pullback.fst p b' := pullback.lift_fst _ _ _
    rw [hfst, hb]
    exact IsPullback.of_hasPullback p b'
  · exact pullback.lift_snd _ _ _
  · exact IsPullback.of_hasPullback p b

/-- The projection and its Cartesian square are constructed together on the ordered power. -/
def torusBaseChange (q : ℕ) :
    {a : (target E q).left ⟶ (target k q).left //
      IsPullback a (target E q).hom (target k q).hom (scalarMap (k := k) (E := E))} :=
  match q with
  | 0 => ⟨scalarMap, IsPullback.id_vert _⟩
  | q + 1 =>
      let tail := torusBaseChange q
      let head := multiplicativeGroupMap_isPullback (k := k) (E := E)
      ⟨pullback.map _ _ _ _ (multiplicativeGroupMap (k := k) (E := E)) tail.val
        (scalarMap (k := k) (E := E)) head.w.symm tail.property.w.symm,
        productMap_isPullback head tail.property⟩

/-- The actual scalar projection of the ordered torus power. -/
def torusMap (q : ℕ) : (target E q).left ⟶ (target k q).left :=
  (torusBaseChange (k := k) (E := E) q).val

/-- The original ordered torus power is Cartesian over the scalar morphism. -/
theorem torusMap_isPullback (q : ℕ) :
    IsPullback (torusMap (k := k) (E := E) q) (target E q).hom (target k q).hom
      (scalarMap (k := k) (E := E)) :=
  (torusBaseChange (k := k) (E := E) q).property

/-- The coefficient projection on the actual simplex-times-torus ambient. -/
def ambientMap (r q : ℕ) : ambient E r q ⟶ ambient k r q :=
  pullback.map _ _ _ _ (sourceMap (k := k) (E := E) r) (torusMap (k := k) (E := E) q)
    (scalarMap (k := k) (E := E)) (sourceMap_isPullback r).w.symm (torusMap_isPullback q).w.symm

/-- The ambient projection is the actual base change of the scalar morphism. -/
theorem ambientMap_isPullback (r q : ℕ) :
    IsPullback (ambientMap (k := k) (E := E) r q)
      (pullback.fst (source E r).hom (target E q).hom ≫ (source E r).hom)
      (pullback.fst (source k r).hom (target k q).hom ≫ (source k r).hom)
      (scalarMap (k := k) (E := E)) :=
  productMap_isPullback (sourceMap_isPullback r) (torusMap_isPullback q)

/-- The ambient projection preserves the actual source projection. -/
@[reassoc]
theorem ambientMap_fst (r q : ℕ) :
    ambientMap (k := k) (E := E) r q ≫ pullback.fst (source k r).hom (target k q).hom =
      pullback.fst (source E r).hom (target E q).hom ≫ sourceMap (k := k) (E := E) r :=
  pullback.lift_fst _ _ _

/-- The ambient projection preserves the actual torus projection. -/
@[reassoc]
theorem ambientMap_snd (r q : ℕ) :
    ambientMap (k := k) (E := E) r q ≫ pullback.snd (source k r).hom (target k q).hom =
      pullback.snd (source E r).hom (target E q).hom ≫ torusMap (k := k) (E := E) q :=
  pullback.lift_snd _ _ _

instance source_isIntegral (F : Type u) [Field F] (r : ℕ) : IsIntegral (source F r).left :=
  AlgebraicSimplex.integral_product F (𝟙 (Spec (.of F))) r

instance sourceMap_surjective (r : ℕ) : Surjective (sourceMap (k := k) (E := E) r) := by
  have : Surjective (scalarMap (k := k) (E := E)) := ⟨Function.surjective_to_subsingleton _⟩
  exact MorphismProperty.of_isPullback (sourceMap_isPullback (k := k) (E := E) r).flip
    (inferInstance : Surjective (scalarMap (k := k) (E := E)))

variable [Module.Finite k E]

local instance scalarMap_isFinite : IsFinite (scalarMap (k := k) (E := E)) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

instance sourceMap_isFinite (r : ℕ) : IsFinite (sourceMap (k := k) (E := E) r) :=
  MorphismProperty.of_isPullback (sourceMap_isPullback (k := k) (E := E) r).flip
    (inferInstance : IsFinite (scalarMap (k := k) (E := E)))

instance ambientMap_isFinite (r q : ℕ) : IsFinite (ambientMap (k := k) (E := E) r q) :=
  MorphismProperty.of_isPullback (ambientMap_isPullback (k := k) (E := E) r q).flip
    (inferInstance : IsFinite (scalarMap (k := k) (E := E)))

/-- Finite scalar pushforward sends every actual admissible prime to an admissible prime. -/
theorem imagePoint_admissible (r q : ℕ) (z : ambient E r q)
    (hz : IsFiniteCorrespondencePoint (source E r).hom (target E q).hom z) :
    IsFiniteCorrespondencePoint (source k r).hom (target k q).hom
      (ambientMap (k := k) (E := E) r q z) := by
  let π := (integralComponentAt z).subschemeι ≫ pullback.fst (source E r).hom (target E q).hom
  have : IsFinite π := hz.1
  have hz' : Set.range π ∈ irreducibleComponents (source E r).left := hz.2
  have hπ : Set.range π = Set.univ := by
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hz'
    exact hz'
  have : Surjective π := ⟨Set.range_eq_univ.mp hπ⟩
  apply isFiniteCorrespondencePoint_finiteMap (source k r).hom (target k q).hom
    (ambientMap (k := k) (E := E) r q) z
  · rw [Category.assoc, ambientMap_fst, ← Category.assoc]
    exact inferInstanceAs (IsFinite (π ≫ sourceMap (k := k) (E := E) r))
  · rw [Category.assoc, ambientMap_fst, ← Category.assoc]
    change Set.range (π ≫ sourceMap (k := k) (E := E) r) ∈ irreducibleComponents (source k r).left
    simp only [range_eq_univ, irreducibleComponents_eq_singleton, Set.mem_singleton_iff]

/-- Finite pushforward on the original signed cycle groups, by restriction of the native map. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/WeightTwo/Corestriction.lean:167-202"
  "adaptation" "Actual scalar finite pushforward in all simplex degrees and torus weights"]
def cyclePushforward (r q : ℕ) :
    finiteCorrespondences (source E r).hom (target E q).hom →+
      finiteCorrespondences (source k r).hom (target k q).hom where
  toFun α := by
    let m := ambientMap (k := k) (E := E) r q
    refine ⟨finiteCyclePushforward m α.val,
      finiteCyclePushforward_finite_support m α.val α.property.1, ?_⟩
    intro y hy
    obtain ⟨z, hz, rfl⟩ := finiteCyclePushforward_support_subset m α.val hy
    exact imagePoint_admissible r q z (α.property.2 z hz)
  map_zero' := Subtype.ext (map_zero (finiteCyclePushforward (ambientMap (k := k) (E := E) r q)))
  map_add' α β :=
    Subtype.ext (map_add (finiteCyclePushforward (ambientMap (k := k) (E := E) r q)) α.val β.val)

/-- The cycle transfer has the same value as the original native finite pushforward. -/
theorem cyclePushforward_val (r q : ℕ)
    (α : finiteCorrespondences (source E r).hom (target E q).hom) :
    (cyclePushforward (k := k) (E := E) r q α).val =
      finiteCyclePushforward (ambientMap (k := k) (E := E) r q) α.val := rfl

/-- A signed prime retains its coefficient times the actual image residue degree. -/
theorem cyclePushforward_single (r q : ℕ) (z : ambient E r q)
    (hz : IsFiniteCorrespondencePoint (source E r).hom (target E q).hom z) (n : ℤ) :
    cyclePushforward (k := k) (E := E) r q
      (singleFiniteCorrespondence (source E r).hom (target E q).hom z hz n) =
    singleFiniteCorrespondence (source k r).hom (target k q).hom
      (ambientMap (k := k) (E := E) r q z) (imagePoint_admissible r q z hz)
      (n * ((ambientMap (k := k) (E := E) r q).residueDegree z : ℤ)) := by
  apply Subtype.ext
  exact finiteCyclePushforward_single (ambientMap (k := k) (E := E) r q) z n

end AlgebraicGeometry.MotivicCohomology.DiagonalFiniteCyclePushforward
