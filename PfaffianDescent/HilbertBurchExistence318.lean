import PfaffianDescent.HilbertBurchCofactorScalarFactor318
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
Construct an exact presentation by signed maximal minors for an arbitrary
ideal with Artinian quotient on a regular local surface. The generator row,
syzygy basis, matrix, and cofactor ideal identification are conclusions.
-/

noncomputable section

namespace AllCharacteristics.HilbertSurfaceDraft

open Matrix

theorem exists_hilbertBurch_presentation_regularLocal_surface011
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2) (I : Ideal R)
    [IsArtinianRing (R ⧸ I)] :
    ∃ (m : ℕ) (M : Matrix (Option (Fin m)) (Fin m) R),
      Function.Injective M.mulVecLin ∧
      I = Ideal.span (Set.range (PfaffianDescent.hilbertBurchCofactors318 M)) ∧
      LinearMap.range M.mulVecLin = LinearMap.ker
        (rowFunctional008 (PfaffianDescent.hilbertBurchCofactors318 M)) := by
  letI : IsDomain R := isDomain_of_regularLocalRing R
  have hI0 : I ≠ ⊥ := by
    intro hI
    apply not_le_prime_height_le_one_of_artinian_quotient hdim I (⊥ : Ideal R)
      (by simp only [Ideal.height_bot]; norm_num)
    rw [hI]
  obtain ⟨m, f₀, g₀, hf₀, hg₀, hgf₀⟩ :=
    exists_successor_finite_free_ideal_presentation hdim I hI0
  let e : (Option (Fin m) → R) ≃ₗ[R] (Fin (m + 1) → R) :=
    LinearEquiv.funCongrLeft R R (finSuccEquiv m)
  let f : (Option (Fin m) → R) →ₗ[R] I := f₀.comp e.toLinearMap
  let g : (Fin m → R) →ₗ[R] (Option (Fin m) → R) :=
    e.symm.toLinearMap.comp g₀
  have hf : Function.Surjective f := hf₀.comp e.surjective
  have hg : Function.Injective g := e.symm.injective.comp hg₀
  have hfg₀ (u : Fin m → R) : f₀ (g₀ u) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [← hgf₀]
    exact ⟨u, rfl⟩
  have hgf : LinearMap.range g = LinearMap.ker f := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      change f₀ (e (e.symm (g₀ u))) = 0
      rw [e.apply_symm_apply]
      exact hfg₀ u
    · intro hz
      have hz₀ : e z ∈ LinearMap.ker f₀ := hz
      rw [← hgf₀] at hz₀
      obtain ⟨u, hu⟩ := hz₀
      refine ⟨u, ?_⟩
      change e.symm (g₀ u) = z
      rw [hu, e.symm_apply_apply]
  let M : Matrix (Option (Fin m)) (Fin m) R := LinearMap.toMatrix' g
  have hM : M.mulVecLin = g := by
    rw [← Matrix.toLin'_apply']
    exact Matrix.toLin'_toMatrix' g
  let a : Option (Fin m) → R := fun i ↦ (f (Pi.single i 1) : R)
  have hrow : I.subtype.comp f = rowFunctional008 a := by
    apply (Pi.basisFun R (Option (Fin m))).ext
    intro i
    simp [a, rowFunctional008_apply]
  have hlinear : rowFunctional008 a = Fintype.linearCombination R a := by
    apply LinearMap.ext
    intro z
    change (∑ i, a i * z i) = ∑ i, z i * a i
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  have hI : I = Ideal.span (Set.range a) := by
    calc
      I = LinearMap.range (I.subtype.comp f) := by
        rw [LinearMap.range_comp_of_range_eq_top I.subtype
          (LinearMap.range_eq_top.mpr hf), I.range_subtype]
      _ = LinearMap.range (rowFunctional008 a) := congrArg LinearMap.range hrow
      _ = Ideal.span (Set.range a) := by
        rw [hlinear]
        exact Fintype.range_linearCombination R a
  have hker : LinearMap.ker (rowFunctional008 a) = LinearMap.ker f := by
    rw [← hrow, LinearMap.ker_comp, Submodule.ker_subtype]
    rfl
  have hginj : Function.Injective M.mulVecLin := by simpa only [hM] using hg
  have hgfM : LinearMap.range M.mulVecLin = LinearMap.ker (rowFunctional008 a) := by
    rw [hM, hker]
    exact hgf
  obtain ⟨c, hc⟩ := exists_cofactor_scalar_of_artinian_presentation010
    hdim I M a f hf hrow hgfM
  have hunit := isUnit_cofactor_factor_of_artinian_presentation009
    hdim I M a c hI hginj hgfM hc
  have hminor : I = Ideal.span
      (Set.range (PfaffianDescent.hilbertBurchCofactors318 M)) :=
    hI.trans (cofactorIdeal_eq_of_unit_factor009 M a c hc hunit).symm
  have hcofrow : rowFunctional008 (PfaffianDescent.hilbertBurchCofactors318 M) =
      c • rowFunctional008 a := by
    apply LinearMap.ext
    intro z
    change (∑ i, PfaffianDescent.hilbertBurchCofactors318 M i * z i) =
      c * ∑ i, a i * z i
    simp_rw [hc]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_assoc _ _ _
  have hcofker : LinearMap.ker
      (rowFunctional008 (PfaffianDescent.hilbertBurchCofactors318 M)) =
      LinearMap.ker (rowFunctional008 a) := by
    ext z
    simp only [LinearMap.mem_ker, hcofrow, LinearMap.smul_apply, smul_eq_mul]
    exact hunit.mul_right_eq_zero
  exact ⟨m, M, hginj, hminor, hgfM.trans hcofker.symm⟩

end AllCharacteristics.HilbertSurfaceDraft
