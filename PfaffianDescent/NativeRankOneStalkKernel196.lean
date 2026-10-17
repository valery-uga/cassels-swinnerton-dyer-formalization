import PfaffianDescent.PointCartierNativeStalkPrincipalNormalization
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

noncomputable section
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u

/-- Generic kernel extraction from a genuine short exact rank-one sequence.
The geometric caller derives the zero-detection identity from the actual
closed immersion; it is not a hypothesis of the original-plane endpoint. -/
theorem nativeRankOneStalkKernel196
    {R B : Type u} [CommRing R] [CommRing B]
    (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact)
    (e₁ : S.X₁ ≅ ModuleCat.of R R) (e₂ : S.X₂ ≅ ModuleCat.of R R)
    (phi : R →+* B)
    (hzero : ∀ r : R, S.g (e₂.inv r) = 0 ↔ phi r = 0) :
    RingHom.ker phi = Ideal.span ({pointCartierNativeStalkScalar S e₁ e₂} : Set R) := by
  let t := pointCartierNativeStalkScalar S e₁ e₂
  have hex : Function.Exact S.f S.g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have hsquare := pointCartierNativeStalkPrincipal_square S e₁ e₂
  have hmul (v : S.X₁) : e₂.hom (S.f v) = t * e₁.hom v :=
    ConcreteCategory.congr_hom hsquare v
  ext r
  change phi r = 0 ↔ r ∈ Ideal.span ({t} : Set R)
  rw [← hzero r, hex (e₂.inv r)]
  constructor
  · rintro ⟨v, hv⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨e₁.hom v, ?_⟩
    have h := congrArg (fun w => e₂.hom w) hv
    rw [hmul] at h
    exact (h.trans (ConcreteCategory.congr_hom e₂.inv_hom_id r)).symm
  · intro hr
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hr
    refine ⟨e₁.inv s, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso e₂.hom).injective
    rw [hmul]
    change t * e₁.hom (e₁.inv s) = e₂.hom (e₂.inv r)
    simpa only [Iso.inv_hom_id_apply] using hs.symm

end PfaffianDescent
