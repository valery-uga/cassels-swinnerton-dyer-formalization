import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations

/-! SOURCE ONLY167. Equality of ENTIRE prescribed ideals from nilpotent
reduction and the explicit intersection identity. No finite generation,
Noetherian, regularity, deformation lifting or Hilbert certificate premise. -/
namespace AllCharacteristics
universe u v

/-- The ideal form of nilpotent Nakayama. Finite generation is unnecessary
because the error ideal is nilpotent, rather than merely Jacobson radical. -/
theorem ideal_eq_of_nilpotent_error167
    {A : Type u} [CommRing A] (L J K : Ideal A)
    (hL : L ≤ J) (herror : J ≤ L ⊔ K * J) (hK : IsNilpotent K) :
    J = L := by
  have hiter : ∀ n : ℕ, J ≤ L ⊔ K ^ n * J := by
    intro n
    induction n with
    | zero => simpa only [pow_zero, Ideal.one_eq_top, Ideal.top_mul] using
        (le_sup_right : J ≤ L ⊔ J)
    | succ n ih =>
        calc
          J ≤ L ⊔ K ^ n * J := ih
          _ ≤ L ⊔ K ^ n * (L ⊔ K * J) :=
            sup_le_sup_left (Ideal.mul_mono_right herror) L
          _ = L ⊔ K ^ (n + 1) * J := by
            rw [Ideal.mul_sup, ← Ideal.mul_assoc, ← pow_succ,
              ← sup_assoc, Ideal.sup_mul_left_self]
  obtain ⟨n, hn⟩ := hK
  apply le_antisymm _ hL
  simpa only [hn, Ideal.zero_eq_bot, Ideal.bot_mul, sup_bot_eq] using hiter n

/-- Equal reductions of a subideal and the actual prescribed ideal imply
whole-ideal equality when the actual kernel meets J in its product with J. -/
theorem ideal_eq_of_same_nilpotent_reduction167
    {A : Type u} {A₀ : Type v} [CommRing A] [CommRing A₀]
    (π : A →+* A₀) (hπ : Function.Surjective π) (L J : Ideal A)
    (hL : L ≤ J) (hmap : J.map π = L.map π)
    (hK : IsNilpotent (RingHom.ker π))
    (hinter : RingHom.ker π ⊓ J = RingHom.ker π * J) :
    J = L := by
  have hsup : J ≤ L ⊔ RingHom.ker π := by
    rw [← Ideal.comap_map_of_surjective' π hπ L, ← hmap]
    exact Ideal.map_le_iff_le_comap.mp le_rfl
  apply ideal_eq_of_nilpotent_error167 L J (RingHom.ker π) hL _ hK
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (hsup hx)
  have hbJ : b ∈ J := by
    have habJ : a + b ∈ J := hab.symm ▸ hx
    simpa only [add_sub_cancel_left] using J.sub_mem habJ (hL ha)
  have hbprod : b ∈ RingHom.ker π * J := by
    rw [← hinter]
    exact ⟨hb, hbJ⟩
  exact Submodule.mem_sup.mpr ⟨a, ha, b, hbprod, hab⟩

end AllCharacteristics
