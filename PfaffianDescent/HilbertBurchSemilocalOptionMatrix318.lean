import PfaffianDescent.HilbertBurchRowKernelFintypeRank318
import PfaffianDescent.ResidueTensorLocalizedRank
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Localization.Ideal

/-!
The semilocal basis/matrix construction in the actual Option(Fin m)
indexing of signed maximal minors. No syzygy flatness, fixed local rank,
nonzero localized ideal, or exact matrix is supplied as a premise.
-/

noncomputable section

namespace PfaffianDescent

open Module Matrix AllCharacteristics.HilbertSurfaceDraft

theorem semilocalSurface_rowKernel_nonempty_basis_fintype017
    {R κ : Type*} [CommRing R] [IsNoetherianRing R] [Fintype κ]
    [Finite (MaximalSpectrum R)] (m : ℕ) (a : κ → R)
    (hcard : Fintype.card κ = m + 1)
    [IsArtinianRing (R ⧸ Ideal.span (Set.range a))]
    (hreg : ∀ (p : Ideal R) (_ : p.IsMaximal),
      IsRegularLocalRing (Localization.AtPrime p))
    (hdim : ∀ (p : Ideal R) (_ : p.IsMaximal),
      ringKrullDim (Localization.AtPrime p) = 2) :
    Nonempty (Basis (Fin m) R (LinearMap.ker (rowFunctional008 a))) := by
  let K := LinearMap.ker (rowFunctional008 a)
  let J := Ideal.span (Set.range a)
  letI : Module.Projective R K :=
    projective_row_kernel_of_regular_surface_maximal_localizations013 a hreg hdim
  letI : Module.Flat R K := inferInstance
  apply semilocal_nonempty_basis_of_localized_finrank001 R K m
  intro p
  let L := Localization.AtPrime p.asIdeal
  let Jp := J.map (algebraMap R L)
  letI : IsRegularLocalRing L := hreg p.asIdeal p.isMaximal
  letI : IsDomain L := AllCharacteristics.isDomain_of_regularLocalRing L
  letI : IsArtinianRing (L ⧸ Jp) :=
    IsArtinianRing.localization_artinian (Algebra.algebraMapSubmonoid (R ⧸ J) p.asIdeal.primeCompl) _
  have hJp : Jp ≠ ⊥ := by
    intro hzero
    apply not_le_prime_height_le_one_of_artinian_quotient
      (hdim p.asIdeal p.isMaximal) Jp (⊥ : Ideal L)
      (by simp only [Ideal.height_bot]; norm_num)
    rw [hzero]
  have hmap : Jp = Ideal.span
      (Set.range (fun i ↦ algebraMap R L (a i))) := by
    change (Ideal.span (Set.range a)).map (algebraMap R L) = _
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hrank := finrank_localized_row_kernel_add_one_fintype015
    p.asIdeal.primeCompl (hdim p.asIdeal p.isMaximal) a
    (by rw [← hmap]; exact hJp)
  rw [hcard] at hrank
  change Module.finrank (Localization.AtPrime p.asIdeal)
    (LocalizedModule.AtPrime p.asIdeal K) + 1 = m + 1 at hrank
  exact Nat.add_right_cancel hrank

theorem semilocalSurface_exists_exact_option_matrix017
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    [Finite (MaximalSpectrum R)] (m : ℕ) (a : Option (Fin m) → R)
    [IsArtinianRing (R ⧸ Ideal.span (Set.range a))]
    (hreg : ∀ (p : Ideal R) (_ : p.IsMaximal),
      IsRegularLocalRing (Localization.AtPrime p))
    (hdim : ∀ (p : Ideal R) (_ : p.IsMaximal),
      ringKrullDim (Localization.AtPrime p) = 2) :
    ∃ M : Matrix (Option (Fin m)) (Fin m) R,
      Function.Injective M.mulVecLin ∧
      LinearMap.range M.mulVecLin = LinearMap.ker (rowFunctional008 a) := by
  let K := LinearMap.ker (rowFunctional008 a)
  obtain ⟨b⟩ := semilocalSurface_rowKernel_nonempty_basis_fintype017 m a (by simp) hreg hdim
  let g : (Fin m → R) →ₗ[R] (Option (Fin m) → R) :=
    K.subtype.comp b.equivFun.symm.toLinearMap
  let M := LinearMap.toMatrix' g
  have hM : M.mulVecLin = g := by
    rw [← Matrix.toLin'_apply']
    exact Matrix.toLin'_toMatrix' g
  refine ⟨M, ?_, ?_⟩
  · rw [hM]
    exact Subtype.val_injective.comp b.equivFun.symm.injective
  · rw [hM]
    change LinearMap.range (K.subtype.comp b.equivFun.symm.toLinearMap) = K
    rw [LinearMap.range_comp_of_range_eq_top K.subtype
      (LinearMap.range_eq_top.mpr b.equivFun.symm.surjective), K.range_subtype]

end PfaffianDescent
