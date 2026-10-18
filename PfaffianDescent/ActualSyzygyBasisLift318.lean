import PfaffianDescent.ActualIdealReduction318
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.Flat.Stability

/-!
Lift a residue syzygy basis inside the actual relative kernel. The residue
comparison is constructed from exactness and coefficient flatness.
-/

noncomputable section
namespace AllCharacteristics
open Module LinearMap
universe u v w t t' z z₀

theorem exists_actual_relative_syzygyBasis318
    {S : Type u} {A : Type v} {A₀ : Type w}
    {ι : Type t} {κ : Type t'} {G : Type z} {G₀ : Type z₀}
    [CommRing S] [CommRing A] [CommRing A₀] [Algebra S A] [Algebra S A₀]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    [AddCommGroup G] [AddCommGroup G₀]
    [Module A G] [Module S G] [IsScalarTower S A G]
    [Module A₀ G₀] [Module S G₀] [IsScalarTower S A₀ G₀]
    [Module.Flat S A] [Module.Flat S G]
    (π : A →ₐ[S] A₀) (hπ : Function.Surjective π)
    (I : Ideal S) (hI : IsNilpotent I)
    (hker : RingHom.ker π.toRingHom = I.map (algebraMap S A))
    (f : (ι → A) →ₗ[A] G) (hf : Function.Surjective f)
    (f₀ : (ι → A₀) →ₗ[A₀] G₀)
    (ρG : G →ₗ[S] G₀)
    (hkerG : ρG.ker = I • (⊤ : Submodule S G))
    (hcomm : ∀ x, ρG (f x) = f₀ (coordinateReduction318 π x))
    (b₀ : Basis κ A₀ f₀.ker) :
    ∃ b : Basis κ A f.ker,
      ∀ j i, π ((b j : ι → A) i) = (b₀ j : ι → A₀) i := by
  let ρF := coordinateReduction318 (ι := ι) π
  have hρF := coordinateReduction318_surjective (ι := ι) π hπ
  have hkerF := coordinateReduction318_ker (ι := ι) π I hker
  obtain ⟨ρK', hρKval', hρK', hkerK'⟩ :=
    exists_kernel_reduction_of_exact_square318 I
      (f.restrictScalars S) hf (f₀.restrictScalars S)
      ρF hρF hkerF ρG hkerG hcomm
  let ρK : f.ker →ₗ[S] f₀.ker := ρK'
  have hρKval : ∀ k : f.ker, (ρK k : ι → A₀) = ρF (k : ι → A) := hρKval'
  have hρK : Function.Surjective ρK := hρK'
  have hkerK : ρK.ker = I • (⊤ : Submodule S f.ker) := hkerK'
  letI : Module.Flat S (ι → A) := Module.Flat.trans S A (ι → A)
  letI : Module.Flat S f.ker :=
    PfaffianDescent.flat_kernel_of_surjective_flat167 (f.restrictScalars S) hf
  choose k hk using fun j => hρK (b₀ j)
  let d : (κ → A) →ₗ[A] f.ker := Fintype.linearCombination A k
  have hscalar (a : A) (k' : f.ker) : ρK (a • k') = π a • ρK k' := by
    apply Subtype.ext
    rw [hρKval]
    ext i
    change π (a * (k' : ι → A) i) = π a * (ρK k' : ι → A₀) i
    rw [map_mul, hρKval]
    rfl
  have hdcomm : ∀ x, ρK (d x) =
      b₀.equivFun.symm (coordinateReduction318 π x) := by
    intro x
    change ρK (∑ j, x j • k j) = _
    rw [map_sum, Basis.equivFun_symm_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hscalar, hk]
    rfl
  have hd : Function.Bijective d :=
    bijective_of_exact_reduction_square318 I hI
      (d.restrictScalars S) (b₀.equivFun.symm.toLinearMap.restrictScalars S)
      (coordinateReduction318 π)
      (coordinateReduction318_surjective π hπ)
      (coordinateReduction318_ker π I hker)
      ρK hρK hkerK hdcomm b₀.equivFun.symm.bijective
  let e : (κ → A) ≃ₗ[A] f.ker := LinearEquiv.ofBijective d hd
  let b : Basis κ A f.ker := (Pi.basisFun A κ).map e
  refine ⟨b, ?_⟩
  have hb (j : κ) : b j = k j := by
    simp [b, e, d]
  intro j i
  have hki := congrFun (hρKval (k j)) i
  rw [hk] at hki
  exact (show π ((b j : ι → A) i) = π ((k j : ι → A) i) from
    congrArg (fun z : f.ker => π ((z : ι → A) i)) (hb j)).trans hki.symm

end AllCharacteristics
end
