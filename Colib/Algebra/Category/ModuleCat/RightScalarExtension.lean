/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Module.RightScalarExtension
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Functoriality of literal right scalar extension

The balanced quotient defines an additive functor on all right modules over an
arbitrary ring. Its identity and composition equivalences retain the actual
quotient carriers and their pure-tensor formulas. Universe lifts are explicit
in categorical comparisons; no small replacement is substituted for a tensor.

## Implementation provenance

Adapted from the Quillen source
`Quillen/Aglib/Algebra/Category/ModuleCat/RightScalarExtension.lean` at revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

noncomputable section

universe u v w z a b

open CategoryTheory MulOpposite

namespace RightScalarExtension

variable {R : Type u} {S : Type v} [Ring R] [Ring S]
variable (f : R →+* S)
variable {M : Type w} {N : Type z} {P : Type a}
variable [AddCommGroup M] [Module Rᵐᵒᵖ M]
variable [AddCommGroup N] [Module Rᵐᵒᵖ N]
variable [AddCommGroup P] [Module Rᵐᵒᵖ P]

/-- Apply a source-module map to the first factor of the literal tensor. -/
def map (a : M →ₗ[Rᵐᵒᵖ] N) : Tensor f M →ₗ[Sᵐᵒᵖ] Tensor f N :=
  lift f ((unit f).comp a)

@[simp] lemma map_pure (a : M →ₗ[Rᵐᵒᵖ] N) (m : M) (s : S) :
    map f a (pure f m s) = pure f (a m) s := by
  rw [map, lift_pure, LinearMap.comp_apply, ← pure_eq_smul_unit]

lemma map_unit (a : M →ₗ[Rᵐᵒᵖ] N) (m : M) :
    map f a (unit f m) = unit f (a m) := by
  simp only [unit_apply, map_pure]

@[simp] lemma map_id : map f (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M) = LinearMap.id := by
  apply hom_ext_unit f
  intro m
  simp

@[simp] lemma map_comp (a : M →ₗ[Rᵐᵒᵖ] N) (b : N →ₗ[Rᵐᵒᵖ] P) :
    map f (b.comp a) = (map f b).comp (map f a) := by
  apply hom_ext_unit f
  intro m
  simp

@[simp] lemma map_add (a b : M →ₗ[Rᵐᵒᵖ] N) : map f (a + b) = map f a + map f b := by
  apply hom_ext_unit f
  intro m
  simp

@[simp] lemma map_zero : map f (0 : M →ₗ[Rᵐᵒᵖ] N) = 0 := by
  apply hom_ext_unit f
  intro m
  simp

/-- Naturality of the Hom equivalence in the source module. -/
lemma homEquiv_precomp {Q : Type b} [AddCommGroup Q] [Module Sᵐᵒᵖ Q]
    (a : M →ₗ[Rᵐᵒᵖ] N) (h : Tensor f N →ₗ[Sᵐᵒᵖ] Q) :
    homEquiv f (h.comp (map f a)) = (homEquiv f h).comp a := by
  ext m
  simp

/-- Literal scalar extension of arbitrary right modules, with the actual quotient carrier. -/
def functor : ModuleCat.{w} Rᵐᵒᵖ ⥤ ModuleCat.{max v w} Sᵐᵒᵖ where
  obj M := ModuleCat.of Sᵐᵒᵖ (Tensor f M)
  map a := ModuleCat.ofHom (map f a.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    exact map_id f
  map_comp a b := by
    apply ModuleCat.hom_ext
    exact map_comp f a.hom b.hom

instance functor_additive : (functor.{u, v, w} f).Additive where
  map_add := by
    intros M N a b
    apply ModuleCat.hom_ext
    exact map_add f a.hom b.hom

@[simp] lemma functor_map_pure {M N : ModuleCat.{w} Rᵐᵒᵖ} (a : M ⟶ N)
    (m : M) (s : S) : (functor f).map a (pure f m s) = pure f (a m) s :=
  map_pure f a.hom m s

/-- Extension along the identity is linearly equivalent to the original module. -/
def idEquiv : Tensor (RingHom.id R) M ≃ₗ[Rᵐᵒᵖ] M :=
  LinearEquiv.ofLinearMap (lift (RingHom.id R) (LinearMap.id : M →ₗ[Rᵐᵒᵖ] M))
    (unit (RingHom.id R))
    (by
      ext m
      change op (1 : R) • m = m
      simp)
    (by
      apply hom_ext_unit (RingHom.id R)
      intro m
      change unit (RingHom.id R) (op (1 : R) • m) = unit (RingHom.id R) m
      simp)

@[simp] lemma idEquiv_pure (m : M) (r : R) :
    idEquiv (pure (RingHom.id R) m r) = op r • m := rfl

@[simp] lemma idEquiv_symm_apply (m : M) :
    (idEquiv (R := R) (M := M)).symm m = unit (RingHom.id R) m := rfl

/-- The identity equivalence is natural in every module map. -/
lemma idEquiv_naturality (a : M →ₗ[Rᵐᵒᵖ] N) :
    (idEquiv (M := N)).toLinearMap.comp (map (RingHom.id R) a) =
      a.comp (idEquiv (M := M)).toLinearMap := by
  apply hom_ext (RingHom.id R)
  intro m r
  simp

/-- The categorical identity comparison explicitly raises the universe of the source. -/
def functorId : functor.{u, u, w} (RingHom.id R) ≅ ModuleCat.uliftFunctor.{u} Rᵐᵒᵖ :=
  NatIso.ofComponents (fun M =>
    ((idEquiv (M := M)).trans ULift.moduleEquiv.symm).toModuleIso) (by
      intro M N a
      apply ModuleCat.hom_ext
      apply hom_ext (RingHom.id R)
      intro m r
      apply ULift.ext
      change idEquiv (map (RingHom.id R) a.hom (pure (RingHom.id R) m r)) =
        a.hom (idEquiv (pure (RingHom.id R) m r))
      simp)


section Composition

variable {T : Type a} [Ring T] (g : S →+* T)

local instance : RingHomCompTriple f.op g.op (g.comp f).op := ⟨rfl⟩

/-- Collapse two successive literal scalar extensions using the semilinear lift. -/
def compForward : Tensor g (Tensor f M) →ₗ[Tᵐᵒᵖ] Tensor (g.comp f) M :=
  lift g (liftSemilinear f g (unit (g.comp f)))

/-- Insert the first tensor unit to invert the composition comparison. -/
def compBackward : Tensor (g.comp f) M →ₗ[Tᵐᵒᵖ] Tensor g (Tensor f M) :=
  lift (g.comp f) ((unit g).comp (unit f))

@[simp] lemma compForward_pure (m : M) (s : S) (t : T) :
    compForward f g (pure g (pure f m s) t) = pure (g.comp f) m (g s * t) := by
  rw [compForward, lift_pure, liftSemilinear_pure, unit_apply, pure_smul,
    pure_smul, one_mul]

@[simp] lemma compBackward_pure (m : M) (t : T) :
    compBackward f g (pure (g.comp f) m t) = pure g (unit f m) t := by
  rw [compBackward, lift_pure, LinearMap.comp_apply, unit_apply, pure_smul, one_mul]

/-- Two linear maps from an iterated tensor agree if they agree on successive units. -/
lemma hom_ext_unit_unit {Q : Type b} [AddCommGroup Q] [Module Tᵐᵒᵖ Q]
    {k l : Tensor g (Tensor f M) →ₗ[Tᵐᵒᵖ] Q}
    (H : ∀ m, k (unit g (unit f m)) = l (unit g (unit f m))) : k = l := by
  apply hom_ext_unit g
  intro x
  exact DFunLike.congr_fun (semilinear_ext_unit f g
    (a := k.comp (unit g)) (b := l.comp (unit g)) H) x

/-- Associativity of scalar extension as an actual linear equivalence of quotients. -/
def compEquiv : Tensor g (Tensor f M) ≃ₗ[Tᵐᵒᵖ] Tensor (g.comp f) M :=
  LinearEquiv.ofLinearMap (compForward f g) (compBackward f g)
    (by
      apply hom_ext_unit (g.comp f)
      intro m
      simp [compForward, compBackward])
    (by
      apply hom_ext_unit_unit f g
      intro m
      simp [compForward, compBackward])

@[simp] lemma compEquiv_pure (m : M) (s : S) (t : T) :
    compEquiv f g (pure g (pure f m s) t) = pure (g.comp f) m (g s * t) :=
  compForward_pure f g m s t

@[simp] lemma compEquiv_symm_pure (m : M) (t : T) :
    (compEquiv f g).symm (pure (g.comp f) m t) = pure g (unit f m) t :=
  compBackward_pure f g m t

lemma compEquiv_unit_unit (m : M) :
    compEquiv f g (unit g (unit f m)) = unit (g.comp f) m := by
  simp only [unit_apply, compEquiv_pure, map_one, one_mul]

/-- Naturality of the composition equivalence for arbitrary module maps. -/
lemma compEquiv_naturality (a : M →ₗ[Rᵐᵒᵖ] N) :
    (compEquiv f g).toLinearMap.comp (map g (map f a)) =
      (map (g.comp f) a).comp (compEquiv f g).toLinearMap := by
  apply hom_ext_unit_unit f g
  intro m
  simp

/-- The comparison with identity extension on the target commutes with composition. -/
lemma compEquiv_id_right :
    (compEquiv f (RingHom.id S) (M := M)).toLinearMap =
      (idEquiv (M := Tensor f M)).toLinearMap := by
  apply hom_ext_unit_unit f (RingHom.id S)
  intro m
  simp
  rfl

/-- The comparison with identity extension on the source commutes with composition. -/
lemma compEquiv_id_left :
    (compEquiv (RingHom.id R) f (M := M)).toLinearMap =
      map f (idEquiv (M := M)).toLinearMap := by
  apply hom_ext_unit_unit (RingHom.id R) f
  intro m
  simp
  rfl

/-- Consecutive tensor functors compare to composite extension with the necessary lift. -/
def functorComp :
    functor.{u, v, w} f ⋙ functor.{v, a, max v w} g ≅
      functor.{u, a, w} (g.comp f) ⋙ ModuleCat.uliftFunctor.{v} Tᵐᵒᵖ :=
  NatIso.ofComponents (fun M =>
    ((compEquiv f g (M := M)).trans ULift.moduleEquiv.symm).toModuleIso) (by
      intro M N a
      apply ModuleCat.hom_ext
      apply hom_ext_unit_unit f g
      intro m
      apply ULift.ext
      change compEquiv f g (map g (map f a.hom) (unit g (unit f m))) =
        map (g.comp f) a.hom (compEquiv f g (unit g (unit f m)))
      simp)

variable {U : Type b} [Ring U] (h : T →+* U)

/-- The full triple-composition diagram commutes on the literal tensor carriers. -/
@[colib_tag "COL-1317", colib_ref "quillen"
  "Quillen/Aglib/Algebra/Category/ModuleCat/RightScalarExtension.lean:240-264" "adaptation"
  "Associativity for the actual comparisons along three composable ring maps."]
lemma compEquiv_assoc :
    (compEquiv (g.comp f) h (M := M)).toLinearMap.comp
        (map h (compEquiv f g).toLinearMap) =
      (compEquiv f (h.comp g) (M := M)).toLinearMap.comp
        (compEquiv g h (M := Tensor f M)).toLinearMap := by
  apply hom_ext_unit h
  intro x
  have e :
      (((compEquiv (g.comp f) h (M := M)).toLinearMap.comp
          (map h (compEquiv f g).toLinearMap)).comp (unit h)) =
        (((compEquiv f (h.comp g) (M := M)).toLinearMap.comp
          (compEquiv g h (M := Tensor f M)).toLinearMap).comp (unit h)) := by
    apply semilinear_ext_unit g h
    intro y
    have e' :
        ((((compEquiv (g.comp f) h (M := M)).toLinearMap.comp
            (map h (compEquiv f g).toLinearMap)).comp (unit h)).comp (unit g)) =
          ((((compEquiv f (h.comp g) (M := M)).toLinearMap.comp
            (compEquiv g h (M := Tensor f M)).toLinearMap).comp (unit h)).comp (unit g)) := by
      apply semilinear_ext_unit f (h.comp g)
      intro m
      simp
      rfl
    exact DFunLike.congr_fun e' y
  exact DFunLike.congr_fun e x

end Composition

end RightScalarExtension
