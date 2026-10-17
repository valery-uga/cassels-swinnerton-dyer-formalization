import PfaffianDescent.FiveQuadricChainComplex

namespace PfaffianDescent.FiveQuadricResolution
open CategoryTheory Limits HomologicalComplex MvPolynomial
section
variable {K : Type*} [Field K] {I : Ideal (MvPolynomial (Fin 4) K)}
    (S : FiveQuadricResolution K I)

lemma augmentation_comp_last : I.mkQ.comp S.lastMap = 0 := by
  apply LinearMap.range_le_ker_iff.mp
  rw [Submodule.ker_mkQ]
  exact S.image_eq.le

/-- The augmentation from the finite free chain complex to its actual quotient. -/
noncomputable def chainAugmentation : S.chainComplex ⟶
    (ChainComplex.single₀ (ModuleCat (MvPolynomial (Fin 4) K))).obj
      (ModuleCat.of _ (MvPolynomial (Fin 4) K ⧸ I)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨ModuleCat.ofHom I.mkQ, by
    rw [S.chainComplex_d]
    exact ModuleCat.hom_ext S.augmentation_comp_last⟩

@[simp] lemma chainAugmentation_f_zero :
    S.chainAugmentation.f 0 = ModuleCat.ofHom I.mkQ :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

lemma chainAugmentation_exact :
    (ShortComplex.mk (S.chainComplex.d 1 0) (S.chainAugmentation.f 0)
      (by rw [S.chainAugmentation_f_zero, S.chainComplex_d]
          exact ModuleCat.hom_ext S.augmentation_comp_last)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (S.chainComplex.d 1 0).hom =
    LinearMap.ker (S.chainAugmentation.f 0).hom
  rw [S.chainAugmentation_f_zero, S.chainComplex_d]
  change LinearMap.range S.lastMap = LinearMap.ker I.mkQ
  rw [Submodule.ker_mkQ]
  exact S.image_eq

lemma chainAugmentation_epi : Epi (S.chainAugmentation.f 0) := by
  rw [S.chainAugmentation_f_zero]
  exact (ModuleCat.epi_iff_range_eq_top (ModuleCat.ofHom I.mkQ)).mpr (Submodule.range_mkQ I)

/-- The augmentation induces an isomorphism on homology in every degree. -/
theorem chainAugmentation_quasiIso : QuasiIso S.chainAugmentation := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · exact ⟨S.chainAugmentation_exact, S.chainAugmentation_epi⟩
      · rfl
      · rfl
      · rfl
  | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact S.chainComplex_exact_succ n
      · exact ChainComplex.exactAt_succ_single_obj _ _

/-- The five-point complex is a projective resolution in mathlib's standard sense. -/
noncomputable def projectiveResolution :
    ProjectiveResolution (ModuleCat.of (MvPolynomial (Fin 4) K) (MvPolynomial (Fin 4) K ⧸ I)) where
  complex := S.chainComplex
  projective := chainModule_projective
  π := S.chainAugmentation
  quasiIso := S.chainAugmentation_quasiIso

end
end PfaffianDescent.FiveQuadricResolution
