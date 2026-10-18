import PfaffianDescent.ResidueTensorDevissage318
import AllCharacteristics.FlatCokernelCriterion

/-!
Nilpotent maximal-ideal devissage proves universal tensor injectivity from
residue injectivity for a map between two base-flat modules. This supplies
the tensor injection used to lift relative regular elements and construct
flat principal quotients.
-/

noncomputable section
namespace AllCharacteristics
open Module LinearMap TensorProduct
universe u v w t

/-- Devissage along powers of a nilpotent maximal ideal. Modules and test
modules may be infinite over the coefficient ring. -/
theorem lTensor_injective_of_nilpotent_residue318
    {R : Type u} [CommRing R] (I : Ideal R) [I.IsMaximal]
    (hI : IsNilpotent I)
    {F : Type v} {N : Type w} [AddCommGroup F] [AddCommGroup N]
    [Module R F] [Module R N] [Module.Flat R F] [Module.Flat R N]
    (f : F →ₗ[R] N)
    (hred : Function.Injective (f.lTensor (R ⧸ I)))
    (T : Type t) [AddCommGroup T] [Module R T] :
    Function.Injective (f.lTensor T) := by
  have H : ∀ (n : ℕ) (T : Type t) [AddCommGroup T] [Module R T],
      I ^ n • (⊤ : Submodule R T) = ⊥ → Function.Injective (f.lTensor T) := by
    intro n
    induction n with
    | zero =>
      intro T _ _ hkill
      have hz : (⊤ : Submodule R T) = ⊥ := by
        simpa only [pow_zero, one_smul] using hkill
      have hzero : ∀ x : T, x = 0 := by
        intro x
        have hx : x ∈ (⊤ : Submodule R T) := Submodule.mem_top
        rw [hz] at hx
        exact (Submodule.mem_bot R).mp hx
      letI : Subsingleton T := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
      exact fun x y _ => Subsingleton.elim x y
    | succ n ih =>
      intro T _ _ hkill
      let U : Submodule R T := I • (⊤ : Submodule R T)
      have hkillU : I ^ n • (⊤ : Submodule R U) = ⊥ := by
        apply le_antisymm ?_ bot_le
        intro x hx
        have hximage : (x : T) ∈
            (I ^ n • (⊤ : Submodule R U)).map U.subtype :=
          Submodule.mem_map.mpr ⟨x, hx, rfl⟩
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at hximage
        change (x : T) ∈ I ^ n • (I • (⊤ : Submodule R T)) at hximage
        rw [← Submodule.mul_smul, ← pow_succ, hkill] at hximage
        change x = 0
        apply Subtype.ext
        exact (Submodule.mem_bot R).mp hximage
      have hU : Function.Injective (f.lTensor U) := ih U hkillU
      letI : Module (R ⧸ I) (T ⧸ U) :=
        inferInstanceAs (Module (R ⧸ I) (T ⧸ I • (⊤ : Submodule R T)))
      letI : IsScalarTower R (R ⧸ I) (T ⧸ U) :=
        inferInstanceAs (IsScalarTower R (R ⧸ I) (T ⧸ I • (⊤ : Submodule R T)))
      have hQ : Function.Injective (f.lTensor (T ⧸ U)) :=
        lTensor_injective_of_residueModule318 I f hred (T ⧸ U)
      exact lTensor_injective_of_extension318 f U.subtype U.mkQ
        U.subtype_injective U.mkQ_surjective (LinearMap.exact_subtype_mkQ U) hU hQ
  obtain ⟨n, hn⟩ := hI
  apply H n T
  rw [hn, Ideal.zero_eq_bot, Submodule.bot_smul]

/-- The map itself is injective, as a consequence of universal tensor
injectivity, rather than a supplied regularity premise. -/
theorem injective_of_nilpotent_residue_of_flat318
    {R : Type u} [CommRing R] (I : Ideal R) [I.IsMaximal]
    (hI : IsNilpotent I)
    {F : Type v} {N : Type w} [AddCommGroup F] [AddCommGroup N]
    [Module R F] [Module R N] [Module.Flat R F] [Module.Flat R N]
    (f : F →ₗ[R] N)
    (hred : Function.Injective (f.lTensor (R ⧸ I))) : Function.Injective f := by
  have h := lTensor_injective_of_nilpotent_residue318 I hI f hred R
  intro x y hxy
  have hxy' : (1 : R) ⊗ₜ[R] x = (1 : R) ⊗ₜ[R] y := by
    apply h
    simp only [LinearMap.lTensor_tmul, hxy]
  simpa only [TensorProduct.lid_tmul, one_smul] using
    congrArg (TensorProduct.lid R F) hxy'

end AllCharacteristics
end
