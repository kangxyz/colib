/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberFineCubeEdges
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberProjectionTrack
public import Colib.AlgebraicGeometry.KTheory.PerfectScalarCofiberCanonicalNull
public import Colib.KTheory.Waldhausen.Additivity.CompactCoproductUnits

/-! # Actual quotient-first scalar sum normalizations

One original coproduct choice is used for both weak structures. The actual normalized functors
and normalization components are identified before constructing the two fine exact targets.
The full categorical square retains the original zero-to-cone transformation and every factor
of both normalization isomorphisms. No realized-cylinder concatenation is substituted here.
-/
/-! Implementation provenance:
  `Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberSumNormalization.lean:34-341`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, universes,
normalizations, time coordinates and spatial boundaries are retained. -/
@[expose] public section
open Topology SSet

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Additivity
  CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.Product
universe u
namespace AlgebraicGeometry.Scheme.Modules
local instance scalarSumCoproducts (X : Scheme.{u}) : HasBinaryCoproducts
  (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :=
  Additivity.hasBinaryCoproducts (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
local notation "V" => RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
local notation "N" => perfectOpenNested j
local notation "W" => NestedWeakEquivalences.coarse N
local notation "Z" =>
  zeroFunctor (C := ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
    X.toRingedSpace))) W
local notation "h0f" => perfectScalarIdentityFineCofibrationSequence (X := X)
local notation "h0w" => perfectOpenScalarIdentityCofibrationSequence j
local notation "Fbar" =>
  CategoryTheory.rebaseFunctor (𝟭 (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X
    := X.toRingedSpace)))) (Structure.zero V)
  (Structure.zero W) (Limits.IsZero.iso (IsExact.zero (changeWeak_exact N)
    (Structure.isZero V)) (Structure.isZero W))

/-- Both structures have the same actual pair of chosen zeros. -/
theorem perfectOpenScalarCoproductPairZero_eq :
    (productStructure V V).zero = (productStructure W W).zero := rfl

/-- The actual fine and coarse coproduct rebases use the same functor and chosen-zero data. -/
theorem perfectOpenScalarCoproductRebase_eq :
    coproductRebasedFunctor V = coproductRebasedFunctor W := rfl

/-- Their original normalization isomorphisms agree after that exact functor transport. -/
theorem perfectOpenScalarCoproductRebaseIso_eq :
    coproductRebaseIso V ≪≫ eqToIso (perfectOpenScalarCoproductRebase_eq j) =
      coproductRebaseIso W := by
  simp only [eqToIso_refl, Iso.trans_refl]
  rfl

/-- Every actual forward normalization component retains the chosen coproduct. -/
theorem perfectOpenScalarCoproductRebaseIso_hom (K L : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (coproductRebaseIso V).hom.app (K, L) ≫
        eqToHom (congrArg (fun F => F.obj (K, L)) (perfectOpenScalarCoproductRebase_eq j)) =
      (coproductRebaseIso W).hom.app (K, L) := by
  simpa only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app] using
    NatTrans.congr_app (congrArg Iso.hom (perfectOpenScalarCoproductRebaseIso_eq j)) (K, L)

/-- Every inverse component has the matching original transport in the other direction. -/
theorem perfectOpenScalarCoproductRebaseIso_inv (K L : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    eqToHom (congrArg (fun F => F.obj (K, L))
        (perfectOpenScalarCoproductRebase_eq j).symm) ≫
        (coproductRebaseIso V).inv.app (K, L) =
      (coproductRebaseIso W).inv.app (K, L) := by
  simpa only [Iso.trans_inv, NatTrans.comp_app, eqToIso.inv, eqToHom_app] using
    NatTrans.congr_app (congrArg Iso.inv (perfectOpenScalarCoproductRebaseIso_eq j)) (K, L)

/-- The identity sequence's actual fine quotient is precisely the displayed coarse zero functor. -/
theorem perfectOpenScalarIdentityQuotient_eq :
    zeroFunctor (C := ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
      X.toRingedSpace))) V = Z := rfl

/-- The original identity quotient arrow has exactly the same chosen-zero components. -/
theorem perfectOpenScalarIdentityQuotientArrow_eq :
    QuotientRows.oneIdToZero V = QuotientRows.oneIdToZero W :=
  perfectOpenScalarFineZeroArrow_eq j

/-- The two identity split endpoints agree as actual normalized functors. -/
theorem perfectOpenScalarIdentitySplitEndpoint_eq :
    normalizedSplitEndpoint V V (h0f).exactH (h0f).exactF =
      normalizedSplitEndpoint V W (h0w).exactH (h0w).exactF := rfl

/-- Their complete original split normalization isomorphisms agree under that data equality. -/
theorem perfectOpenScalarIdentitySplitIso_eq :
    normalizedSplitIso V V (h0f).exactH (h0f).exactF ≪≫
        eqToIso (perfectOpenScalarIdentitySplitEndpoint_eq j) =
      normalizedSplitIso V W (h0w).exactH (h0w).exactF := by
  simp only [eqToIso_refl, Iso.trans_refl]
  rfl

variable (r : Γ(X, ⊤))
local notation "h1f" => perfectScalarCofibrationSequence X r
local notation "h1w" => perfectOpenScalarCofibrationSequence j r

/-- The scalar split endpoints retain the literal signed cone and the same chosen zero. -/
theorem perfectOpenScalarConeSplitEndpoint_eq :
    normalizedSplitEndpoint V V (h1f).exactH (h1f).exactF =
      normalizedSplitEndpoint V W (h1w).exactH (h1w).exactF := rfl

/-- Their normalization data agree before any realization is taken. -/
theorem perfectOpenScalarConeSplitIso_eq :
    normalizedSplitIso V V (h1f).exactH (h1f).exactF ≪≫
        eqToIso (perfectOpenScalarConeSplitEndpoint_eq j r) =
      normalizedSplitIso V W (h1w).exactH (h1w).exactF := by
  simp only [eqToIso_refl, Iso.trans_refl]
  rfl

/-- The exact zero-first target uses the same normalized identity in its second coordinate. -/
def perfectOpenScalarZeroPairTarget : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
  (X := X.toRingedSpace)) × ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
  X.toRingedSpace)) ⥤ ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
  X.toRingedSpace)) :=
  ((Z).prod Fbar) ⋙ coproductRebasedFunctor V

/-- Fine exactness retains both actual factors and the original coproduct exactness. -/
theorem perfectOpenScalarZeroPairTarget_exact :
    IsExact (productStructure V V).cof (productStructure V V).weq (V).cof (V).weq
      (perfectOpenScalarZeroPairTarget j) :=
  (pair_exact (productStructure V V) V V
    ((fst_exact V V).comp (zeroFunctor_isExact V V))
    ((snd_exact V V).comp (perfectOpenScalarIdentityRebase_fineExact j))).comp
    (coproductRebasedFunctor_exact V)

/-- The full identity normalization retains both rebases, the inverse zero rebase and coproduct. -/
def perfectOpenScalarZeroSumNormalizationIso :
    normalizedSplitEndpoint V V (h0f).exactH (h0f).exactF ≅
      perfectOpenScalarZeroPairTarget j :=
  (normalizedSplitIso V V (h0f).exactH (h0f).exactF).symm ≪≫
    isoWhiskerRight (NatIso.prod (perfectOpenScalarZeroRebaseIso j)
      (perfectOpenScalarIdentityRebaseIso j)) coproductFunctor ≪≫
    isoWhiskerRight (NatIso.prod (perfectOpenScalarZeroRebaseIso j).symm
      (Iso.refl Fbar)) coproductFunctor ≪≫
    isoWhiskerLeft ((Z).prod Fbar) (coproductRebaseIso V)

/-- All four original identity normalization factors are visible at arbitrary inputs. -/
theorem perfectOpenScalarZeroSumNormalizationIso_hom (K L : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (perfectOpenScalarZeroSumNormalizationIso j).hom.app (K, L) =
      (normalizedSplitIso V V (h0f).exactH (h0f).exactF).inv.app (K, L) ≫
        coprod.map ((perfectOpenScalarZeroRebaseIso j).hom.app K)
          ((perfectOpenScalarIdentityRebaseIso j).hom.app L) ≫
        coprod.map ((perfectOpenScalarZeroRebaseIso j).inv.app K) (𝟙 ((Fbar).obj L)) ≫
        (coproductRebaseIso V).hom.app ((Z).obj K, (Fbar).obj L) := rfl

/-- The original identity normalization is fine weak on every actual pair. -/
theorem perfectOpenScalarZeroSumNormalizationIso_weak (K L : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (V).weq ((perfectOpenScalarZeroSumNormalizationIso j).hom.app (K, L)) :=
  (V).weq_iso _ inferInstance

/-- The target's original pair of chosen zeros is literally the original fine zero. -/
theorem perfectOpenScalarZeroPairTarget_zero :
    (perfectOpenScalarZeroPairTarget j).obj ((V).zero, (V).zero) = (V).zero := by
  change (coproductRebasedFunctor V).obj ((V).zero, (Fbar).obj (V).zero) = (V).zero
  rw [CategoryTheory.rebaseFunctor_obj_base]
  exact coproductRebasedFunctor_zero V

/-- The complete identity normalization has the exact transported chosen-zero component. -/
theorem perfectOpenScalarZeroSumNormalizationIso_zero :
    eqToHom (normalizedSplitEndpoint_obj_zero V V (h0f).exactH (h0f).exactF).symm ≫
        (perfectOpenScalarZeroSumNormalizationIso j).hom.app ((V).zero, (V).zero) ≫
        eqToHom (perfectOpenScalarZeroPairTarget_zero j) = 𝟙 (V).zero :=
  (V).isZero.eq_of_src _ _

variable (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)
local notation "A" => perfectOpenScalarConeFunctor j r q hq
local notation "hA" => perfectOpenScalarConeFunctor_waldhausenExact j r q hq
local notation "Ar" => CategoryTheory.rebaseFunctor A (Structure.zero V)
  (Structure.zero (acyclicStructure N))
  (Limits.IsZero.iso (IsExact.zero hA (Structure.isZero V))
    (Structure.isZero (acyclicStructure N)))
local notation "D" => Ar ⋙ acyclicInclusion N

/-- The actual public acyclic cone rebase is the first target factor. -/
def perfectOpenScalarConePairTarget : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex
  (X := X.toRingedSpace)) × ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
  X.toRingedSpace)) ⥤ ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X :=
  X.toRingedSpace)) :=
  ((D).prod Fbar) ⋙ coproductRebasedFunctor V

/-- The cone target is fine exact using the inherited acyclic inclusion, not coarse exactness. -/
theorem perfectOpenScalarConePairTarget_exact :
    IsExact (productStructure V V).cof (productStructure V V).weq (V).cof (V).weq
      (perfectOpenScalarConePairTarget j r q hq) :=
  (pair_exact (productStructure V V) V V
    ((fst_exact V V).comp ((hA).rebase.comp (acyclicInclusion_exact N)))
    ((snd_exact V V).comp (perfectOpenScalarIdentityRebase_fineExact j))).comp
    (coproductRebasedFunctor_exact V)

/-- The cone normalization retains the original cone, identity, beta and coproduct factors. -/
def perfectOpenScalarConeSumNormalizationIso :
    normalizedSplitEndpoint V V (h1f).exactH (h1f).exactF ≅
      perfectOpenScalarConePairTarget j r q hq :=
  (normalizedSplitIso V V (h1f).exactH (h1f).exactF).symm ≪≫
    isoWhiskerRight (NatIso.prod (perfectOpenScalarConeRebaseIso j r)
      (perfectOpenScalarIdentityRebaseIso j)) coproductFunctor ≪≫
    isoWhiskerRight (NatIso.prod (perfectOpenScalarConeNormalizationIso j r q hq)
      (Iso.refl Fbar)) coproductFunctor ≪≫
    isoWhiskerLeft ((D).prod Fbar) (coproductRebaseIso V)

/-- Every original cone normalization factor is retained on arbitrary coefficient pairs. -/
theorem perfectOpenScalarConeSumNormalizationIso_hom (K L : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (perfectOpenScalarConeSumNormalizationIso j r q hq).hom.app (K, L) =
      (normalizedSplitIso V V (h1f).exactH (h1f).exactF).inv.app (K, L) ≫
        coprod.map ((perfectOpenScalarConeRebaseIso j r).hom.app K)
          ((perfectOpenScalarIdentityRebaseIso j).hom.app L) ≫
        coprod.map ((perfectOpenScalarConeNormalizationIso j r q hq).hom.app K)
          (𝟙 ((Fbar).obj L)) ≫
        (coproductRebaseIso V).hom.app ((D).obj K, (Fbar).obj L) := rfl

/-- Both fine structures see the original complete cone normalization as weak. -/
theorem perfectOpenScalarConeSumNormalizationIso_weak (K L : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (V).weq ((perfectOpenScalarConeSumNormalizationIso j r q hq).hom.app (K, L)) :=
  (V).weq_iso _ inferInstance

/-- The public acyclic rebase and same identity rebase preserve the actual pair of zeros. -/
theorem perfectOpenScalarConePairTarget_zero :
    (perfectOpenScalarConePairTarget j r q hq).obj ((V).zero, (V).zero) = (V).zero := by
  change (coproductRebasedFunctor V).obj ((D).obj (V).zero, (Fbar).obj (V).zero) = (V).zero
  rw [perfectOpenScalarAcyclicConeRebase_zero, CategoryTheory.rebaseFunctor_obj_base]
  exact coproductRebasedFunctor_zero V

/-- The full cone normalization has the exact transported original chosen-zero component. -/
theorem perfectOpenScalarConeSumNormalizationIso_zero :
    eqToHom (normalizedSplitEndpoint_obj_zero V V (h1f).exactH (h1f).exactF).symm ≫
        (perfectOpenScalarConeSumNormalizationIso j r q hq).hom.app ((V).zero, (V).zero) ≫
        eqToHom (perfectOpenScalarConePairTarget_zero j r q hq) = 𝟙 (V).zero :=
  (V).isZero.eq_of_src _ _

/-- The first component is exactly the canonical zero-to-inclusion on the public acyclic rebase. -/
def perfectOpenScalarCanonicalPairTransformation : (Z).prod Fbar ⟶ (D).prod Fbar :=
  (perfectOpenScalarRebasedZeroToCone j r q hq).prod (𝟙 Fbar)

/-- The actual quotient-first pair map retains a literal identity in the second coordinate. -/
theorem perfectOpenScalarCanonicalPairTransformation_app (K L : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (perfectOpenScalarCanonicalPairTransformation j r q hq).app (K, L) =
      ((perfectOpenScalarRebasedZeroToCone j r q hq).app K, 𝟙 ((Fbar).obj L)) := rfl

/-- Weakness uses the original canonical acyclic edge and the literal second-coordinate identity. -/
theorem perfectOpenScalarCanonicalPairTransformation_weak (K L : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (productStructure W W).weq
      ((perfectOpenScalarCanonicalPairTransformation j r q hq).app (K, L)) :=
  ⟨zeroToAcyclicInclusion_weak N ((Ar).obj K), (W).weq.id_mem _⟩

/-- The canonical pair transformation is mapped by the actual coarse normalized coproduct. -/
def perfectOpenScalarCanonicalSumTransformation :
    perfectOpenScalarZeroPairTarget j ⟶ perfectOpenScalarConePairTarget j r q hq :=
  whiskerRight (perfectOpenScalarCanonicalPairTransformation j r q hq)
    (coproductRebasedFunctor W)

/-- Its entire component is the actual coarse coproduct functor map. -/
theorem perfectOpenScalarCanonicalSumTransformation_app (K L : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (perfectOpenScalarCanonicalSumTransformation j r q hq).app (K, L) =
      (coproductRebasedFunctor W).map
        ((perfectOpenScalarRebasedZeroToCone j r q hq).app K, 𝟙 ((Fbar).obj L)) := rfl

/-- The canonical sum edge remains coarse weak on every original coefficient pair. -/
theorem perfectOpenScalarCanonicalSumTransformation_weak (K L : ObjectProperty.FullSubcategory
  (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    (W).weq ((perfectOpenScalarCanonicalSumTransformation j r q hq).app (K, L)) :=
  (coproductRebasedFunctor_exact W).weak _
    (perfectOpenScalarCanonicalPairTransformation_weak j r q hq K L)

/-- The canonical sum edge has the exact transported chosen-zero component. -/
theorem perfectOpenScalarCanonicalSumTransformation_zero :
    eqToHom (perfectOpenScalarZeroPairTarget_zero j).symm ≫
        (perfectOpenScalarCanonicalSumTransformation j r q hq).app ((V).zero, (V).zero) ≫
        eqToHom (perfectOpenScalarConePairTarget_zero j r q hq) = 𝟙 (V).zero :=
  (V).isZero.eq_of_src _ _

/-- The separated edge is exactly the original normalized identity-to-scalar transformation. -/
def perfectOpenScalarSeparatedSumTransformation :
    normalizedSplitEndpoint V V (h0f).exactH (h0f).exactF ⟶
      normalizedSplitEndpoint V V (h1f).exactH (h1f).exactF :=
  normalizedSplitEndpointTransformation W (𝟙 (𝟭 (ObjectProperty.FullSubcategory
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))))
    (perfectScalarInclusionNat X r) (𝟙 (𝟭 (ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))))) (QuotientRows.oneIdToZero W)
    (perfectScalarConeProjectionNat X r) (perfectOpenScalarZeroToCone j r q hq)
    V h0w h1w

/-- Prefixing the accepted whole zero-normalization square retains every original factor. -/
theorem perfectOpenScalarZeroNormalizationSquare_prefixed :
    perfectOpenScalarZeroToCone j r q hq ≫ (perfectOpenScalarConeRebaseIso j r).hom ≫
        (perfectOpenScalarConeNormalizationIso j r q hq).hom =
      (perfectOpenScalarZeroRebaseIso j).hom ≫ (perfectOpenScalarZeroRebaseIso j).inv ≫
        perfectOpenScalarRebasedZeroToCone j r q hq := by
  have h := perfectOpenScalarZeroNormalizationSquare j r q hq
  change ((perfectOpenScalarZeroRebaseIso j).inv ≫ perfectOpenScalarZeroToCone j r q hq ≫
    (perfectOpenScalarConeRebaseIso j r).hom) ≫
      (perfectOpenScalarConeNormalizationIso j r q hq).hom =
    (perfectOpenScalarZeroRebaseIso j).inv ≫ perfectOpenScalarRebasedZeroToCone j r q hq at h
  have hp := congrArg (fun η => (perfectOpenScalarZeroRebaseIso j).hom ≫ η) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hp

/-- The complete original quotient-first square, before any cylinder or realization is chosen. -/
theorem perfectOpenScalarSumNormalizationSquare :
    perfectOpenScalarSeparatedSumTransformation j r q hq ≫
        (perfectOpenScalarConeSumNormalizationIso j r q hq).hom =
      (perfectOpenScalarZeroSumNormalizationIso j).hom ≫
        perfectOpenScalarCanonicalSumTransformation j r q hq := by
  apply NatTrans.ext
  funext KL
  rcases KL with ⟨K, L⟩
  have h := NatTrans.congr_app (perfectOpenScalarZeroNormalizationSquare_prefixed j r q hq) K
  dsimp only [NatTrans.comp_app] at h
  have hn := (coproductRebaseIso V).hom.naturality
    (show ((Z).obj K, (Fbar).obj L) ⟶ ((D).obj K, (Fbar).obj L) from
      ((perfectOpenScalarRebasedZeroToCone j r q hq).app K, 𝟙 ((Fbar).obj L)))
  change coprod.map ((perfectOpenScalarRebasedZeroToCone j r q hq).app K)
      (𝟙 ((Fbar).obj L)) ≫ (coproductRebaseIso V).hom.app ((D).obj K, (Fbar).obj L) =
    (coproductRebaseIso V).hom.app ((Z).obj K, (Fbar).obj L) ≫
      (coproductRebasedFunctor V).map
        ((perfectOpenScalarRebasedZeroToCone j r q hq).app K, 𝟙 ((Fbar).obj L)) at hn
  dsimp only [perfectOpenScalarSeparatedSumTransformation,
    normalizedSplitEndpointTransformation, NatTrans.comp_app]
  rw [perfectOpenScalarConeSumNormalizationIso_hom,
    perfectOpenScalarZeroSumNormalizationIso_hom,
    perfectOpenScalarCanonicalSumTransformation_app]
  simp only [Category.assoc]
  change (normalizedSplitIso V V (h0f).exactH (h0f).exactF).inv.app (K, L) ≫
      coprod.map ((perfectOpenScalarZeroToCone j r q hq).app K) (𝟙 L) ≫
      (normalizedSplitIso V V (h1f).exactH (h1f).exactF).hom.app (K, L) ≫
      (normalizedSplitIso V V (h1f).exactH (h1f).exactF).inv.app (K, L) ≫
      coprod.map ((perfectOpenScalarConeRebaseIso j r).hom.app K)
        ((perfectOpenScalarIdentityRebaseIso j).hom.app L) ≫
      coprod.map ((perfectOpenScalarConeNormalizationIso j r q hq).hom.app K)
        (𝟙 ((Fbar).obj L)) ≫
      (coproductRebaseIso V).hom.app ((D).obj K, (Fbar).obj L) =
    (normalizedSplitIso V V (h0f).exactH (h0f).exactF).inv.app (K, L) ≫
      coprod.map ((perfectOpenScalarZeroRebaseIso j).hom.app K)
        ((perfectOpenScalarIdentityRebaseIso j).hom.app L) ≫
      coprod.map ((perfectOpenScalarZeroRebaseIso j).inv.app K) (𝟙 ((Fbar).obj L)) ≫
      (coproductRebaseIso V).hom.app ((Z).obj K, (Fbar).obj L) ≫
      (coproductRebasedFunctor V).map
        ((perfectOpenScalarRebasedZeroToCone j r q hq).app K, 𝟙 ((Fbar).obj L))
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← hn]
  simp only [coprod.map_map_assoc]
  rw [h]
  simp only [Category.comp_id]
  rw [show (𝟙 L) ≫ (perfectOpenScalarIdentityRebaseIso j).hom.app L =
    (perfectOpenScalarIdentityRebaseIso j).hom.app L from Category.id_comp _]

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0317",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/ScalarCofiberSumNormalization.lean:34-341"
    "adaptation"
    "Actual scalar normalization and canonical fiber maps on the unchanged subdivision cube"]
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarSeparatedSumTransformation
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarZeroNormalizationSquare_prefixed
  AlgebraicGeometry.Scheme.Modules.perfectOpenScalarSumNormalizationSquare
