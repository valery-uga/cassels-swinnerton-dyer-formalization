import PfaffianDescent.NativeLocalSurjectivePresentation316
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! SOURCE ONLY317. A closed classifying point whose residue is the original
field determines actual stalk maps into that SAME field. -/
noncomputable section
namespace PfaffianDescent

variable {R A K : Type*} [CommRing R] [CommRing A] [Field K]
  [Algebra R A] [Algebra R K]

lemma originalClassifyingFieldMap_surjective317
    (hR : Function.Surjective (algebraMap R K)) (k : A →ₐ[R] K) :
    Function.Surjective k := by
  intro x
  obtain ⟨r, hr⟩ := hR x
  exact ⟨algebraMap R A r, (k.commutes r).trans hr⟩

variable (q : Ideal A) [q.IsPrime] (k : A →ₐ[R] K)
  (hq : RingHom.ker k.toRingHom = q)

include hq in
private lemma originalFieldStalk_denominator317 (s : q.primeCompl) : IsUnit (k s.val) := by
  apply isUnit_iff_ne_zero.mpr
  intro hs
  have hm : s.val ∈ RingHom.ker k.toRingHom := hs
  exact s.property (hq ▸ hm)

/-- Localization at the ACTUAL kernel prime, retaining the original field. -/
def originalClassifyingFieldStalkMap317 : Localization.AtPrime q →ₐ[R] K :=
  IsLocalization.liftAlgHom (originalFieldStalk_denominator317 q k hq)

lemma originalClassifyingFieldStalkMap_algebraMap317 (a : A) :
    originalClassifyingFieldStalkMap317 q k hq (algebraMap A (Localization.AtPrime q) a) = k a :=
  IsLocalization.lift_eq _ _

lemma originalClassifyingFieldStalkMap_surjective317 (hk : Function.Surjective k) :
    Function.Surjective (originalClassifyingFieldStalkMap317 q k hq) := by
  intro x
  obtain ⟨a, ha⟩ := hk x
  exact ⟨algebraMap A (Localization.AtPrime q) a,
    (originalClassifyingFieldStalkMap_algebraMap317 q k hq a).trans ha⟩

lemma originalClassifyingFieldStalkMap_kernel317 (hk : Function.Surjective k) :
    RingHom.ker (originalClassifyingFieldStalkMap317 q k hq).toRingHom =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) :=
  IsLocalRing.ker_eq_maximalIdeal _
    (originalClassifyingFieldStalkMap_surjective317 q k hq hk)

end PfaffianDescent
end
