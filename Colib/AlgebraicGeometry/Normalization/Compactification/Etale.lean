/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.RelativeNormal
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.Unramified.LocalStructure

/-! # The actual finite normalization of an étale map over a field

The source is the unchanged original étale source. Finiteness is proved using
native Nagata normalization, not an assumed compactification or old generic
normalization comparison. No normality or reducedness hypothesis is imposed on
a marked closed subscheme. The theorem concerns the ambient étale source only.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.EtaleCompactification

/-- Étaleness supplies actual quasi-finiteness on affine coordinate rings. -/
theorem locallyQuasiFinite_of_etale {Y X : Scheme.{u}} (f : Y ⟶ X) [Etale f] :
    LocallyQuasiFinite f := by
  constructor
  intro U hU V hV e
  have he := f.etale_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)

variable (k : Type u) [Field k] {X Y : Scheme.{u}}
  (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] [IsNormal X]
  (f : Y ⟶ X) [Etale f] [QuasiCompact f] [IsSeparated f]

include q in
/-- The finite map is the structural map of the literal relative normalization. -/
theorem finite_normalization : IsFinite f.fromNormalization := by
  have : IsNormal Y := isNormal_of_etale f
  have : IsReduced Y := inferInstance
  exact isFinite_fromNormalization_of_locallyOfFiniteType f
    (isNagataScheme_of_locallyOfFiniteType_over_field k q)

omit [IsNormal X] in
/-- The original source embeds openly; no affine replacement is inserted. -/
theorem open_normalization : IsOpenImmersion f.toNormalization := by
  have : LocallyQuasiFinite f := locallyQuasiFinite_of_etale f
  infer_instance

include q in
/-- The actual constructed normalization is normal, including disconnected sources. -/
theorem normal_normalization : IsNormal f.normalization := by
  have : IsNormal Y := isNormal_of_etale f
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ q)
  apply isNormal_normalization f
  intro V hV
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV
  have : IsNoetherian V := ⟨⟩
  exact finite_irreducibleComponents_of_isNoetherian

omit [LocallyOfFiniteType q] in
/-- All native compactification maps and their equation are constructed together. -/
theorem exists_finite_normal_compactification [IsProper q] :
    ∃ (C : Scheme.{u}) (j : Y ⟶ C) (π : C ⟶ X),
      IsOpenImmersion j ∧ IsFinite π ∧ IsNormal C ∧
      IsLocallyNoetherian C ∧ IsProper (π ≫ q) ∧
      j ≫ π = f ∧ IsDominant j := by
  have : IsFinite f.fromNormalization := finite_normalization k q f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsLocallyNoetherian f.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian f.fromNormalization
  exact ⟨f.normalization, f.toNormalization, f.fromNormalization,
    open_normalization f, inferInstance, normal_normalization k q f,
    inferInstance, inferInstance, f.toNormalization_fromNormalization, inferInstance⟩

end AlgebraicGeometry.Scheme.EtaleCompactification
