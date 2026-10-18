import PfaffianDescent.SemilocalResidueSupport318
import PfaffianDescent.ActualAffineTensorFiber174
import Mathlib.RingTheory.Localization.Algebra

/-!
Construct the actual reduction between the two
finite-support localizations, including its full coefficient kernel. A
second construction identifies the actual tensor residue of the original
semilocal ring with that residual semilocalization.
-/
noncomputable section
namespace PfaffianDescent
open scoped TensorProduct
universe u v w

/-- Two actual surjections with the same kernel give an explicit comparison
preserving every original element. -/
def surjectiveEqualKernelRingEquiv318
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : RingHom.ker f = RingHom.ker g) : B ≃+* C :=
  (f.quotientKerEquivOfSurjective hf).symm |>.trans
    ((Ideal.quotEquivOfEq hker).trans (g.quotientKerEquivOfSurjective hg))

@[simp] theorem surjectiveEqualKernelRingEquiv_apply318
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hker : RingHom.ker f = RingHom.ker g) (a : A) :
    surjectiveEqualKernelRingEquiv318 f g hf hg hker (f a) = g a := by
  simp only [surjectiveEqualKernelRingEquiv318, RingEquiv.trans_apply,
    RingHom.quotientKerEquivOfSurjective_symm_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

def semilocalResidueMap318
    {A : Type u} {A₀ : Type v} [CommRing A] [CommRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    (t : Finset (MaximalSpectrum A)) :
    Localization (finiteSupportDenominators001 t) →+*
      Localization (finiteSupportDenominators001 (residueFiniteSupport318 π hπ hker t)) :=
  IsLocalization.map _ π
    ((finiteSupportDenominators_map_residue318 π hπ hker t).symm ▸
      (finiteSupportDenominators001 t).le_comap_map)

@[simp] theorem semilocalResidueMap_algebraMap318
    {A : Type u} {A₀ : Type v} [CommRing A] [CommRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    (t : Finset (MaximalSpectrum A)) (a : A) :
    semilocalResidueMap318 π hπ hker t
        (algebraMap A (Localization (finiteSupportDenominators001 t)) a) =
      algebraMap A₀ (Localization (finiteSupportDenominators001
        (residueFiniteSupport318 π hπ hker t))) (π a) := by
  exact IsLocalization.map_eq _ a

theorem semilocalResidueMap_surjective318
    {A : Type u} {A₀ : Type v} [CommRing A] [CommRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    (t : Finset (MaximalSpectrum A)) :
    Function.Surjective (semilocalResidueMap318 π hπ hker t) := by
  let M := finiteSupportDenominators001 t
  let N := finiteSupportDenominators001 (residueFiniteSupport318 π hπ hker t)
  have hden : M.map π = N := finiteSupportDenominators_map_residue318 π hπ hker t
  letI : IsLocalization (M.map π) (Localization N) := hden.symm ▸ inferInstance
  exact IsLocalization.map_surjective_of_surjective
    (M := M) (S := Localization M) (Q := Localization N) (g := π) hπ

theorem semilocalResidueMap_ker318
    {A : Type u} {A₀ : Type v} [CommRing A] [CommRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    (t : Finset (MaximalSpectrum A)) :
    RingHom.ker (semilocalResidueMap318 π hπ hker t) =
      (RingHom.ker π).map (algebraMap A (Localization (finiteSupportDenominators001 t))) := by
  exact IsLocalization.ker_map _ π (finiteSupportDenominators_map_residue318 π hπ hker t)

theorem semilocalResidueMap_coefficient_ker318
    {S : Type u} {A : Type v} {A₀ : Type w}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A]
    (I : Ideal S) (hI : IsNilpotent I)
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = I.map (algebraMap S A))
    (t : Finset (MaximalSpectrum A)) :
    ∃ hNil : IsNilpotent (RingHom.ker π),
      RingHom.ker (semilocalResidueMap318 π hπ hNil t) =
        I.map (algebraMap S (Localization (finiteSupportDenominators001 t))) := by
  have hNil : IsNilpotent (RingHom.ker π) := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, ?_⟩
    rw [hker, ← Ideal.map_pow, hn]
    simp only [Ideal.zero_eq_bot, Ideal.map_bot]
  refine ⟨hNil, ?_⟩
  rw [semilocalResidueMap_ker318, hker, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]

/-- The actual tensor residue of the original semilocal ambient ring is
identified with the semilocalized original tensor residue, preserving the
canonical original ambient reduction. -/
theorem exists_tensor_semilocalResidueEquiv318
    {S k A A₀ : Type u}
    [CommRing S] [CommRing k] [CommRing A] [CommRing A₀]
    [Algebra S k] [Algebra S A]
    (hSk : Function.Surjective (algebraMap S k))
    (hNil : IsNilpotent (RingHom.ker (algebraMap S k)))
    (π : A →+* A₀) (hπ : Function.Surjective π)
    (hker : RingHom.ker π =
      (RingHom.ker (algebraMap S k)).map (algebraMap S A))
    (t : Finset (MaximalSpectrum A)) :
    ∃ (hπNil : IsNilpotent (RingHom.ker π))
      (e : (k ⊗[S] Localization (finiteSupportDenominators001 t)) ≃+*
        Localization (finiteSupportDenominators001 (residueFiniteSupport318 π hπ hπNil t))),
      ∀ x : Localization (finiteSupportDenominators001 t),
        e (1 ⊗ₜ[S] x) = semilocalResidueMap318 π hπ hπNil t x := by
  obtain ⟨hπNil, hlocKer⟩ := semilocalResidueMap_coefficient_ker318
    (RingHom.ker (algebraMap S k)) hNil π hπ hker t
  let L := Localization (finiteSupportDenominators001 t)
  let f := (affineTensorFiberReduction174 (R := S) (S := k) (A := L)).toRingHom
  let g := semilocalResidueMap318 π hπ hπNil t
  have hf : Function.Surjective f := affineTensorFiberReduction174_surjective hSk
  have hg : Function.Surjective g := semilocalResidueMap_surjective318 π hπ hπNil t
  have hfg : RingHom.ker f = RingHom.ker g :=
    (affineTensorFiberReduction174_kernel (A := L) hSk).trans hlocKer.symm
  refine ⟨hπNil, surjectiveEqualKernelRingEquiv318 f g hf hg hfg, ?_⟩
  intro x
  exact surjectiveEqualKernelRingEquiv_apply318 f g hf hg hfg x

end PfaffianDescent
end
