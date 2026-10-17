import AllCharacteristics.IdealTensorQuotientInjection
import Mathlib.Tactic.Abel

/-! Square-zero lifting of an actual linear map.  No upstairs flatness or
freeness is assumed.  A finite presentation or a local-ring assumption is
unnecessary for these elementary square-zero arguments. -/

open LinearMap TensorProduct
namespace AllCharacteristics
universe u v w t

/-- Reduced surjectivity lifts across a square-zero coefficient ideal. -/
theorem surjective_of_square_zero_lTensor_surjective166
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    {F : Type v} {M : Type w} [AddCommGroup F] [AddCommGroup M]
    [Module R F] [Module R M] (f : F →ₗ[R] M)
    (hred : Function.Surjective (f.lTensor (R ⧸ I))) :
    Function.Surjective f := by
  have hII : I * I = ⊥ := by simpa only [pow_two] using hI
  have htop : (⊤ : Submodule R M) ≤ f.range ⊔ I • (⊤ : Submodule R M) := by
    intro m hm
    obtain ⟨t, ht⟩ := hred (1 ⊗ₜ[R] m)
    obtain ⟨n, hn⟩ := TensorProduct.mk_surjective
      (R := R) (M := F) (S := R ⧸ I) Ideal.Quotient.mk_surjective t
    have htn : (1 : R ⧸ I) ⊗ₜ[R] f n = 1 ⊗ₜ[R] m := by
      rw [← hn] at ht
      change f.lTensor (R ⧸ I) (1 ⊗ₜ[R] n) = 1 ⊗ₜ[R] m at ht
      simpa only [LinearMap.lTensor_tmul] using ht
    have hq : (Submodule.Quotient.mk (f n) : M ⧸ I • (⊤ : Submodule R M)) =
        Submodule.Quotient.mk m := by
      simpa only [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul] using
        congrArg (TensorProduct.quotTensorEquivQuotSMul M I) htn
    have hdiff : m - f n ∈ I • (⊤ : Submodule R M) :=
      (Submodule.Quotient.eq _).mp hq.symm
    have hsum : f n + (m - f n) = m := by abel
    rw [← hsum]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self f n) hdiff
  have hIM : I • (⊤ : Submodule R M) ≤ f.range := by
    calc
      I • (⊤ : Submodule R M) ≤
          I • (f.range ⊔ I • (⊤ : Submodule R M)) :=
        smul_mono_right I htop
      _ = I • f.range ⊔ I • (I • (⊤ : Submodule R M)) :=
        Submodule.smul_sup I _ _
      _ = I • f.range := by
        rw [← Submodule.mul_smul, hII, Submodule.bot_smul, sup_bot_eq]
      _ ≤ f.range := Submodule.smul_le_right
  apply LinearMap.range_eq_top.mp
  exact le_antisymm le_top (htop.trans (sup_le le_rfl hIM))

/-- With the canonical coefficient-ideal tensor injection proved, a
surjection with injective whole reduction is itself injective. -/
theorem injective_of_square_zero_lTensor_injective166
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    {F : Type v} {M : Type w} [AddCommGroup F] [AddCommGroup M]
    [Module R F] [Module R M] (f : F →ₗ[R] M)
    (hf : Function.Surjective f)
    (hred : Function.Injective (f.lTensor (R ⧸ I)))
    (hmu : Function.Injective (idealTensorMultiplication166 I M)) :
    Function.Injective f := by
  have hII : I * I = ⊥ := by simpa only [pow_two] using hI
  have hker : f.ker ≤ I • (⊤ : Submodule R F) := by
    intro x hx
    have hxred : f.lTensor (R ⧸ I) (1 ⊗ₜ[R] x) = 0 := by
      simp only [LinearMap.lTensor_tmul, LinearMap.mem_ker.mp hx, tmul_zero]
    have hxt : (1 : R ⧸ I) ⊗ₜ[R] x = 0 :=
      (injective_iff_map_eq_zero _).mp hred _ hxred
    apply (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule R F))).mp
    simpa only [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero] using
      congrArg (TensorProduct.quotTensorEquivQuotSMul F I) hxt
  have hzero : (idealTensorMultiplication166 I F).comp
      (f.ker.subtype.lTensor I) = 0 := by
    ext r k
    simp only [idealTensorMultiplication166, LinearMap.comp_apply,
      LinearMap.lTensor_tmul, LinearMap.rTensor_tmul,
      TensorProduct.lid_tmul, LinearMap.zero_apply]
    change (r : R) • (k : F) = 0
    have hmem : (r : R) • (k : F) ∈ I • (I • (⊤ : Submodule R F)) :=
      Submodule.smul_mem_smul r.property (hker k.property)
    rw [← Submodule.mul_smul, hII, Submodule.bot_smul] at hmem
    exact (Submodule.mem_bot R).mp hmem
  apply (injective_iff_map_eq_zero f).mpr
  intro x hx
  have hxI : x ∈ I • (⊤ : Submodule R F) := hker (LinearMap.mem_ker.mpr hx)
  rw [← idealTensorMultiplication166_range I F] at hxI
  obtain ⟨y, hy⟩ := hxI
  have hyf : f.lTensor I y = 0 := by
    apply (injective_iff_map_eq_zero _).mp hmu
    calc
      idealTensorMultiplication166 I M (f.lTensor I y) =
          f (idealTensorMultiplication166 I F y) :=
        congrArg (fun h : I ⊗[R] F →ₗ[R] M => h y)
          (idealTensorMultiplication166_naturality I f)
      _ = 0 := by rw [hy]; exact hx
  obtain ⟨z, hz⟩ := (lTensor_exact I (LinearMap.exact_subtype_ker_map f) hf y).mp hyf
  calc
    x = idealTensorMultiplication166 I F y := hy.symm
    _ = idealTensorMultiplication166 I F (f.ker.subtype.lTensor I z) := by rw [hz]
    _ = 0 := congrArg (fun h : I ⊗[R] f.ker →ₗ[R] F => h z) hzero

/-- The square-zero comparison theorem for the original linear map. -/
theorem bijective_of_square_zero_lTensor_bijective166
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    {F : Type v} {M : Type w} [AddCommGroup F] [AddCommGroup M]
    [Module R F] [Module R M] (f : F →ₗ[R] M)
    (hred : Function.Bijective (f.lTensor (R ⧸ I)))
    (hmu : Function.Injective (idealTensorMultiplication166 I M)) :
    Function.Bijective f := by
  have hf := surjective_of_square_zero_lTensor_surjective166 I hI f hred.surjective
  exact ⟨injective_of_square_zero_lTensor_injective166 I hI f hf hred.injective hmu, hf⟩

/-- The comparison retains the actual downstairs coefficient algebra `S`.
The canonical quotient by its kernel is used only inside the proof. -/
theorem bijective_of_square_zero_actualBaseChange_bijective166
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (hRS : Function.Surjective (algebraMap R S))
    (hI : (RingHom.ker (algebraMap R S)) ^ 2 = ⊥)
    {F : Type w} {M : Type t} [AddCommGroup F] [AddCommGroup M]
    [Module R F] [Module R M] (f : F →ₗ[R] M)
    (hred : Function.Bijective (f.lTensor S))
    (hmu : Function.Injective
      (idealTensorMultiplication166 (RingHom.ker (algebraMap R S)) M)) :
    Function.Bijective f := by
  let I := RingHom.ker (algebraMap R S)
  let e : (R ⧸ I) ≃ₗ[R] S :=
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hRS).toLinearEquiv
  let eF := e.rTensor F
  let eM := e.rTensor M
  have hcomm : eM.toLinearMap.comp (f.lTensor (R ⧸ I)) =
      (f.lTensor S).comp eF.toLinearMap := by
    ext r x
    simp [eM, eF]
  have hfun : (f.lTensor (R ⧸ I) : (R ⧸ I) ⊗[R] F → (R ⧸ I) ⊗[R] M) =
      eM.symm ∘ f.lTensor S ∘ eF := by
    funext x
    apply eM.injective
    rw [Function.comp_apply, Function.comp_apply, eM.apply_symm_apply]
    exact congrArg (fun h : (R ⧸ I) ⊗[R] F →ₗ[R] S ⊗[R] M => h x) hcomm
  apply bijective_of_square_zero_lTensor_bijective166 I hI f
  · rw [hfun]
    exact eM.symm.bijective.comp (hred.comp eF.bijective)
  · exact hmu

end AllCharacteristics
