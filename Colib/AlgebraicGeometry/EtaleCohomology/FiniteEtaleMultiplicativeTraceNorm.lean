/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtaleMultiplicativeTraceNormSplit
public import Colib.AlgebraicGeometry.EtaleCohomology.NonemptyAffineSplitChart

/-! # The native finite étale multiplicative trace is the algebra norm over a field -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace Stacks.EtaleCohomology
open AlgebraicGeometry.SplitAffinePullback
variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
  [Module.Finite k A] [Etale (sourceMap (k := k) (A := A))]
  [IsFinite (sourceMap (k := k) (A := A))]

set_option backward.isDefEq.respectTransparency false in
/-- The actual native Gm trace on global units of a finite étale algebra over a field
is its determinant norm. The algebra need not be a field or a domain. -/
theorem finiteEtaleMultiplicativeTraceUnits_eq_norm (t : Aˣ) :
    (Scheme.ΓSpecIso (.of k)).hom.hom
      (finiteEtaleMultiplicativeTraceUnits (sourceMap (k := k) (A := A))
        (Scheme.Etale.mk (𝟙 (Spec (.of k))))
        (Units.map (Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom t)).val =
      Algebra.norm k t.val := by
  classical
  obtain ⟨R, hR, ψ, hψ, I, hI, e, he⟩ :=
    Stacks.Etale.exists_nonempty_affine_split_chart (sourceMap (k := k) (A := A))
  let : Nontrivial R := hR
  let : Algebra k R := ψ.hom.toAlgebra
  let : Etale (baseMap (k := k) (R := R)) := hψ
  let : Finite I := hI
  let e' : pullback (baseMap (k := k) (R := R)) (sourceMap (k := k) (A := A)) ≅
      ∐ fun _ : I => Spec R := pullbackSymmetry _ _ ≪≫ e
  have he' : e'.hom ≫ Sigma.desc (fun _ : I => 𝟙 (Spec R)) =
      pullback.fst (baseMap (k := k) (R := R)) (sourceMap (k := k) (A := A)) := by
    dsimp only [e']
    rw [Iso.trans_hom, Category.assoc, he]
    exact pullbackSymmetry_hom_comp_snd _ _
  let U := Scheme.Etale.mk (baseMap (k := k) (R := R))
  let V := Scheme.Etale.mk (𝟙 (Spec (.of k)))
  let f : U ⟶ V := MorphismProperty.Over.homMk (baseMap (k := k) (R := R))
    (by exact Category.comp_id _)
  let t' := Units.map (Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom t
  have hn := finiteEtaleMultiplicativeTraceUnits_naturality
    (sourceMap (k := k) (A := A)) f t'
  apply (algebraMap k R).injective
  calc
    algebraMap k R ((Scheme.ΓSpecIso (.of k)).hom.hom
        (finiteEtaleMultiplicativeTraceUnits (sourceMap (k := k) (A := A)) V t').val) =
      (Scheme.ΓSpecIso R).hom.hom
        (Units.map f.left.appTop.hom.toMonoidHom
          (finiteEtaleMultiplicativeTraceUnits (sourceMap (k := k) (A := A)) V t')).val := by
      exact (congrArg (fun m => m.hom
        (finiteEtaleMultiplicativeTraceUnits (sourceMap (k := k) (A := A)) V t').val)
          (Scheme.ΓSpecIso_naturality ψ)).symm
    _ = (Scheme.ΓSpecIso R).hom.hom
        (finiteEtaleMultiplicativeTraceUnits (sourceMap (k := k) (A := A)) U t').val := by rw [hn]
    _ = algebraMap k R (Algebra.norm k t.val) :=
      finiteEtaleMultiplicativeTraceUnits_affineSplit e' he' t

/-- Unit-valued form of the native trace/norm comparison, with the actual ΓSpec maps. -/
theorem finiteEtaleMultiplicativeTraceUnits_eq_unitsMap_norm (t : Aˣ) :
    Units.map (Scheme.ΓSpecIso (.of k)).hom.hom.toMonoidHom
      (finiteEtaleMultiplicativeTraceUnits (sourceMap (k := k) (A := A))
        (Scheme.Etale.mk (𝟙 (Spec (.of k))))
        (Units.map (Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom t)) =
      Units.map (Algebra.norm k) t := by
  apply Units.ext
  exact finiteEtaleMultiplicativeTraceUnits_eq_norm t

end Stacks.EtaleCohomology
