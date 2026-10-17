import PfaffianDescent.GoodBlockForms

namespace PfaffianDescent
open Module
open LinearMap (BilinForm)
section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

lemma isotropic_finrank_double_le (B : BilinForm K V) (hB : B.Nondegenerate)
    (W : Submodule K V) (hiso : ∀ x ∈ W, ∀ y ∈ W, B x y = 0) :
    2 * finrank K W ≤ finrank K V := by
  have hle : W ≤ B.orthogonal W := by
    intro y hy
    exact LinearMap.BilinForm.mem_orthogonal_iff.mpr (fun x hx => hiso x hx y hy)
  have hd := Submodule.finrank_mono hle
  have hw := Submodule.finrank_le W
  rw [LinearMap.BilinForm.finrank_orthogonal hB] at hd
  omega

end
section
variable {K : Type*} [Field K] [NeZero (2 : K)]

lemma goodCommonIsotropic_invariant (W : Submodule K (Fin 3 → Fin 2 → K))
    (hdim : finrank K W = 3)
    (h0 : ∀ x ∈ W, ∀ y ∈ W, goodSymplecticForm K x y = 0)
    (h1 : ∀ x ∈ W, ∀ y ∈ W,
      goodSymplecticForm K x (goodSpectralOperator K (Fin 2 → K) y) = 0) :
    ∀ y ∈ W, goodSpectralOperator K (Fin 2 → K) y ∈ W := by
  apply invariant_of_two_isotropic (goodSymplecticForm K)
    ((goodSymplecticForm K).compl₂ (goodSpectralOperator K (Fin 2 → K)))
    (goodSymplecticForm_nondegenerate K) (goodSpectralOperator K (Fin 2 → K))
    (fun _ _ => rfl) W _ h0 h1
  simp [hdim, Module.finrank_pi_fintype]

lemma goodBlockSubmodule_isotropic (W : Submodule K (Fin 3 → Fin 2 → K))
    (h0 : ∀ x ∈ W, ∀ y ∈ W, goodSymplecticForm K x y = 0) (i : Fin 3) :
    ∀ x ∈ goodBlockSubmodule K (Fin 2 → K) W i,
      ∀ y ∈ goodBlockSubmodule K (Fin 2 → K) W i, goodPlaneForm K x y = 0 := by
  intro x hx y hy
  have h := h0 _ hx _ hy
  simpa [goodSymplecticForm_single_left] using h

lemma goodBlockSubmodule_finrank_le_one (W : Submodule K (Fin 3 → Fin 2 → K))
    (h0 : ∀ x ∈ W, ∀ y ∈ W, goodSymplecticForm K x y = 0) (i : Fin 3) :
    finrank K (goodBlockSubmodule K (Fin 2 → K) W i) ≤ 1 := by
  have hnd : (goodPlaneForm K).Nondegenerate := by
    apply LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
    norm_num [Matrix.det_fin_two]
  have hd := isotropic_finrank_double_le (goodPlaneForm K) hnd _
    (goodBlockSubmodule_isotropic W h0 i)
  rw [Module.finrank_fin_fun] at hd
  omega

/-- Each summand of a common isotropic three-space is a line in its two-dimensional block. -/
theorem goodCommonIsotropic_block_finrank (W : Submodule K (Fin 3 → Fin 2 → K))
    (hdim : finrank K W = 3)
    (h0 : ∀ x ∈ W, ∀ y ∈ W, goodSymplecticForm K x y = 0)
    (h1 : ∀ x ∈ W, ∀ y ∈ W,
      goodSymplecticForm K x (goodSpectralOperator K (Fin 2 → K) y) = 0)
    (i : Fin 3) : finrank K (goodBlockSubmodule K (Fin 2 → K) W i) = 1 := by
  have h2 : IsUnit (2 : K) := isUnit_iff_ne_zero.mpr (NeZero.ne (2 : K))
  have he := (goodSpectralSplitting K (Fin 2 → K) h2 W
    (goodCommonIsotropic_invariant W hdim h0 h1)).finrank_eq
  rw [hdim, Module.finrank_pi_fintype, Fin.sum_univ_three] at he
  have ha := goodBlockSubmodule_finrank_le_one W h0 0
  have hb := goodBlockSubmodule_finrank_le_one W h0 1
  have hc := goodBlockSubmodule_finrank_le_one W h0 2
  change 3 = finrank K (goodBlockSubmodule K (Fin 2 → K) W 0) +
    finrank K (goodBlockSubmodule K (Fin 2 → K) W 1) +
    finrank K (goodBlockSubmodule K (Fin 2 → K) W 2) at he
  fin_cases i
  · change finrank K (goodBlockSubmodule K (Fin 2 → K) W 0) = 1
    omega
  · change finrank K (goodBlockSubmodule K (Fin 2 → K) W 1) = 1
    omega
  · change finrank K (goodBlockSubmodule K (Fin 2 → K) W 2) = 1
    omega

/-- The exact product decomposition of every common isotropic three-space. -/
noncomputable def goodCommonIsotropicSplitting (W : Submodule K (Fin 3 → Fin 2 → K))
    (hdim : finrank K W = 3)
    (h0 : ∀ x ∈ W, ∀ y ∈ W, goodSymplecticForm K x y = 0)
    (h1 : ∀ x ∈ W, ∀ y ∈ W,
      goodSymplecticForm K x (goodSpectralOperator K (Fin 2 → K) y) = 0) :
    W ≃ₗ[K] ((i : Fin 3) → goodBlockSubmodule K (Fin 2 → K) W i) :=
  goodSpectralSplitting K (Fin 2 → K) (isUnit_iff_ne_zero.mpr (NeZero.ne (2 : K))) W
    (goodCommonIsotropic_invariant W hdim h0 h1)

end
end PfaffianDescent
