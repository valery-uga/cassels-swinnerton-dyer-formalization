import PfaffianDescent.AlternatingRestriction
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Basic

namespace PfaffianDescent
section
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- A section of a linear map gives an explicit projection onto its kernel. -/
def splitKernelRetraction (f : M →ₗ[R] N) (s : N →ₗ[R] M) (hs : f.comp s = LinearMap.id) :
    M →ₗ[R] f.ker :=
  (LinearMap.id - s.comp f).codRestrict f.ker (fun x => by
    change f (x - s (f x)) = 0
    rw [map_sub, show f (s (f x)) = f x from LinearMap.congr_fun hs (f x), sub_self])

lemma splitKernelRetraction_subtype (f : M →ₗ[R] N) (s : N →ₗ[R] M)
    (hs : f.comp s = LinearMap.id) :
    (splitKernelRetraction f s hs).comp f.ker.subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change x.1 - s (f x.1) = x.1
  rw [x.2, map_zero, sub_zero]

lemma splitKernelRetraction_surjective (f : M →ₗ[R] N) (s : N →ₗ[R] M)
    (hs : f.comp s = LinearMap.id) : Function.Surjective (splitKernelRetraction f s hs) := by
  intro x
  exact ⟨x.1, LinearMap.congr_fun (splitKernelRetraction_subtype f s hs) x⟩

lemma projective_kernel_of_section [Module.Projective R M]
    (f : M →ₗ[R] N) (s : N →ₗ[R] M) (hs : f.comp s = LinearMap.id) :
    Module.Projective R f.ker :=
  Module.Projective.of_split f.ker.subtype (splitKernelRetraction f s hs)
    (splitKernelRetraction_subtype f s hs)

lemma finite_kernel_of_section [Module.Finite R M]
    (f : M →ₗ[R] N) (s : N →ₗ[R] M) (hs : f.comp s = LinearMap.id) : Module.Finite R f.ker :=
  Module.Finite.of_surjective (splitKernelRetraction f s hs) (splitKernelRetraction_surjective f s hs)

/-- A submodule with projective quotient is an actual direct summand of the ambient module. -/
lemma submodule_retraction_of_projective_quotient (W : Submodule R M) [Module.Projective R (M ⧸ W)] :
    ∃ p : M →ₗ[R] W, p.comp W.subtype = LinearMap.id := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property W.mkQ LinearMap.id W.mkQ_surjective
  let e : W.mkQ.ker ≃ₗ[R] W := LinearEquiv.ofEq _ _ W.ker_mkQ
  refine ⟨e.toLinearMap.comp (splitKernelRetraction W.mkQ s hs), ?_⟩
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change x.1 - s (W.mkQ x.1) = x.1
  rw [show W.mkQ x.1 = 0 from (Submodule.Quotient.mk_eq_zero W).mpr x.2, map_zero, sub_zero]

lemma finite_submodule_of_projective_quotient [Module.Finite R M]
    (W : Submodule R M) [Module.Projective R (M ⧸ W)] : Module.Finite R W := by
  obtain ⟨p, hp⟩ := submodule_retraction_of_projective_quotient W
  apply Module.Finite.of_surjective p
  intro x
  exact ⟨x.1, LinearMap.congr_fun hp x⟩

lemma projective_submodule_of_projective_quotient [Module.Projective R M]
    (W : Submodule R M) [Module.Projective R (M ⧸ W)] : Module.Projective R W := by
  obtain ⟨p, hp⟩ := submodule_retraction_of_projective_quotient W
  exact Module.Projective.of_split W.subtype p hp

end
section
variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]

/-- Extension along a retraction is linear in the alternating form. -/
def alternatingExtension (W : Submodule R V) (p : V →ₗ[R] W) :
    AlternatingTwoForms R W →ₗ[R] AlternatingTwoForms R V where
  toFun B := B.compLinearMap p
  map_add' B C := AlternatingMap.add_compLinearMap B C p
  map_smul' r B := by ext v; rfl

lemma alternatingRestriction_extension (W : Submodule R V) (p : V →ₗ[R] W)
    (hp : p.comp W.subtype = LinearMap.id) :
    (alternatingRestriction R V W).comp (alternatingExtension R V W p) = LinearMap.id := by
  apply LinearMap.ext
  intro B
  change (B.compLinearMap p).compLinearMap W.subtype = B
  rw [AlternatingMap.compLinearMap_assoc, hp, AlternatingMap.compLinearMap_id]

/-- Restriction of alternating forms is split surjective for every projective quotient, over arbitrary rings. -/
theorem alternatingRestriction_split_of_projective_quotient
    (W : Submodule R V) [Module.Projective R (V ⧸ W)] :
    ∃ s : AlternatingTwoForms R W →ₗ[R] AlternatingTwoForms R V,
      (alternatingRestriction R V W).comp s = LinearMap.id := by
  obtain ⟨p, hp⟩ := submodule_retraction_of_projective_quotient W
  exact ⟨alternatingExtension R V W p, alternatingRestriction_extension R V W p hp⟩

end
end PfaffianDescent
